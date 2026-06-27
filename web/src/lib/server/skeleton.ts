// Skeleton view for the LeanNets NETWORK mode — the Node port of the Python
// analysis/skeleton_graph.build_skeleton_view. Atoms become nodes, |ref|>=2
// entries become directed edges (ref[0] -> ref[i]); size/color are computed.
//
// The common modes (size: uniform | degree | in-degree | out-degree;
// color: sort; cluster: none) are ported exactly. The networkx-only analytics
// (pagerank, betweenness, community, louvain, depth…) fall back gracefully
// (uniform size / sort colour / no cluster) rather than failing.
import type { Store } from './store'

interface GNode { id: string; sort: string; title: string; source: string; state: string }
interface GEdge { source: string; target: string; hash: string; sort: string; hyper: boolean }

function parseRecord(raw: string): Record<string, any> | null {
  try { const p = JSON.parse(raw); return p && typeof p === 'object' && !Array.isArray(p) ? p : null }
  catch { return null }
}

function buildGraph(entries: Store): { nodes: Map<string, GNode>; edges: GEdge[] } {
  const nodes = new Map<string, GNode>()
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h) {
      const r = parseRecord(e.record) || {}
      nodes.set(h, { id: h, sort: r.sort ?? '', title: r.title ?? '', source: r.source ?? '', state: r.state ?? '' })
    }
  }
  const edges: GEdge[] = []
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length >= 2) {
      const src = e.ref[0]
      const r = parseRecord(e.record)
      const sort = r?.sort ?? ''
      const hyper = e.ref.length > 2
      for (const tgt of e.ref.slice(1)) {
        if (nodes.has(src) && nodes.has(tgt)) edges.push({ source: src, target: tgt, hash: h, sort, hyper })
      }
    }
  }
  return { nodes, edges }
}

function hslToHex(h: number, s: number, l: number): string {
  const sf = s / 100, lf = l / 100
  const f = (n: number) => {
    const k = (n + h / 30) % 12
    const a = sf * Math.min(lf, 1 - lf)
    const v = Math.round((lf - a * Math.max(-1, Math.min(k - 3, 9 - k, 1))) * 255)
    return v.toString(16).padStart(2, '0')
  }
  return `#${f(0)}${f(8)}${f(4)}`
}

/** Deterministic sort → hex (matches the Python backend). */
function sortToColor(sort: string): string {
  let h = 0
  for (const c of sort) h = (Math.imul(h, 31) + c.charCodeAt(0)) >>> 0
  return hslToHex(h % 360, 50 + ((h >>> 8) % 30), 45 + ((h >>> 16) % 20))
}

function blendHex(a: string, b: string): string {
  const p = (x: string, i: number) => parseInt(x.slice(i, i + 2), 16)
  const m = (x: number, y: number) => Math.floor((x + y) / 2).toString(16).padStart(2, '0')
  return `#${m(p(a, 1), p(b, 1))}${m(p(a, 3), p(b, 3))}${m(p(a, 5), p(b, 5))}`
}

function normalize(values: Record<string, number>, lo: number, hi: number): Record<string, number> {
  const vs = Object.values(values)
  if (!vs.length) return {}
  const min = Math.min(...vs), max = Math.max(...vs), mid = (lo + hi) / 2
  const out: Record<string, number> = {}
  for (const [k, v] of Object.entries(values)) out[k] = max === min ? mid : lo + ((v - min) / (max - min)) * (hi - lo)
  return out
}

function degree(nodes: Map<string, GNode>, edges: GEdge[], mode: 'total' | 'in' | 'out'): Record<string, number> {
  const d: Record<string, number> = {}
  for (const id of nodes.keys()) d[id] = 0
  for (const e of edges) {
    if (mode !== 'in' && e.source in d) d[e.source] += 1
    if (mode !== 'out' && e.target in d) d[e.target] += 1
  }
  return d
}

function filterBySource(entries: Store, source: string): Store {
  const keep = new Set<string>()
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && e.ref[0] === h) {
      const r = parseRecord(e.record)
      if (r?.source === source) keep.add(h)
    }
  }
  const out: Store = {}
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length === 1 && keep.has(h)) out[h] = e
    else if (e.ref.length === 2 && keep.has(e.ref[0]) && keep.has(e.ref[1])) out[h] = e
  }
  return out
}

export function buildSkeletonView(
  entries: Store,
  opts: { source?: string; size?: string; color?: string; cluster?: string },
) {
  let ents = entries
  if (opts.source && opts.source !== 'all') ents = filterBySource(entries, opts.source)

  const { nodes, edges } = buildGraph(ents)
  if (nodes.size === 0) return { nodes: [], edges: [] }

  // size
  let radii: Record<string, number> = {}
  const size = opts.size ?? 'uniform'
  if (size === 'degree' || size === 'in-degree' || size === 'out-degree') {
    const mode = size === 'degree' ? 'total' : size === 'in-degree' ? 'in' : 'out'
    radii = normalize(degree(nodes, edges, mode as 'total' | 'in' | 'out'), 3, 14)
  } else {
    for (const id of nodes.keys()) radii[id] = 6.0 // uniform / unsupported metric
  }

  // color (sort is the default and only fully-ported mode; others fall back to it)
  const colors: Record<string, string> = {}
  for (const [id, n] of nodes) colors[id] = sortToColor(n.sort)

  const outNodes = [...nodes.values()].map((n) => ({
    id: n.id,
    sort: n.sort,
    title: n.title,
    radius: radii[n.id] ?? 6.0,
    color: colors[n.id] ?? '#888888',
    ...(n.state ? { state: n.state } : {}),
  }))

  const outEdges = edges.map((e) => {
    const su = nodes.get(e.source)?.source ?? ''
    const sv = nodes.get(e.target)?.source ?? ''
    const cross = !!(su && sv && su !== sv)
    const color = cross ? '#333333' : blendHex(colors[e.source] ?? '#888888', colors[e.target] ?? '#888888')
    const dashed = e.sort.endsWith(', proof)') || e.hyper
    return {
      source: e.source,
      target: e.target,
      sort: e.sort,
      hash: e.hash,
      color,
      hyper: e.hyper,
      cross,
      ...(dashed ? { dashed: true } : {}),
    }
  })

  return { nodes: outNodes, edges: outEdges }
}
