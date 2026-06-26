'use client'

import { useEffect, useState, useCallback } from 'react'
import { API_BASE } from '@/lib/apiBase'

const PROJECT_PATH =
  process.env.NEXT_PUBLIC_PROJECT_PATH || '/Users/moqian/OpenGALib/projects/riemannian-geometry'

interface LeanNode { name?: string; title?: string; sort?: string; state?: string; file?: string; line?: number }
interface Snapshot { total: number; proven: number; open: LeanNode[]; at: string }

// Pull the live store and reduce it to the formalization status. The single
// source of truth is each lean atom's `state` field (sorry | proven) — nothing
// here is hand-written, so the board never goes stale.
function reduce(entries: Record<string, { ref: string[]; record: string }>): Snapshot {
  const lean: LeanNode[] = []
  for (const [h, e] of Object.entries(entries)) {
    if (e.ref.length !== 1 || e.ref[0] !== h) continue // atoms only
    let r: any
    try { r = JSON.parse(e.record) } catch { continue }
    if (r.source !== 'lean') continue
    lean.push(r)
  }
  const open = lean
    .filter((r) => r.state === 'sorry')
    .sort((a, b) => (a.name || '').localeCompare(b.name || ''))
  return { total: lean.length, proven: lean.length - open.length, open, at: new Date().toLocaleTimeString() }
}

export function StatusBoard() {
  const [snap, setSnap] = useState<Snapshot | null>(null)
  const [error, setError] = useState(false)
  const [loading, setLoading] = useState(true)

  const refresh = useCallback(async () => {
    try {
      const res = await fetch(`${API_BASE}/api/astrolabe/entries?path=${encodeURIComponent(PROJECT_PATH)}`)
      if (!res.ok) throw new Error(String(res.status))
      setSnap(reduce(await res.json()))
      setError(false)
    } catch {
      setError(true)
    } finally {
      setLoading(false)
    }
  }, [])

  useEffect(() => {
    refresh()
    const id = setInterval(refresh, 30_000) // live: re-poll every 30s
    return () => clearInterval(id)
  }, [refresh])

  if (loading) return <p className="text-[15px] text-white/40">Loading live status…</p>

  if (error || !snap) {
    return (
      <div className="rounded-lg border border-white/10 bg-white/[0.02] px-5 py-4">
        <p className="text-[15px] text-white/55">
          Live status is served by the project backend. Start it
          (<code className="text-cyan-300/80 bg-white/[0.06] px-1.5 py-0.5 rounded text-[13px] font-mono">uvicorn astrolabe_app.server:app</code>)
          and this board updates itself.
        </p>
      </div>
    )
  }

  const pct = snap.total ? Math.round((snap.proven / snap.total) * 1000) / 10 : 0

  return (
    <>
      <h2 id="summary" className="text-xl font-semibold text-white/85 mt-2 mb-3 scroll-mt-20 flex items-center gap-3">
        Summary
        <span className="inline-flex items-center gap-1.5 text-[11px] font-normal text-emerald-300/80">
          <span className="w-1.5 h-1.5 rounded-full bg-emerald-400 animate-pulse" /> live · {snap.at}
        </span>
      </h2>

      <div className="grid grid-cols-3 gap-3 mb-5">
        {[
          { label: 'Declarations', value: snap.total },
          { label: 'Proven', value: snap.proven },
          { label: 'Open', value: snap.open.length },
        ].map((s) => (
          <div key={s.label} className="rounded-lg border border-white/10 bg-white/[0.02] px-4 py-4">
            <div className="text-3xl font-semibold text-white/90 tabular-nums">{s.value}</div>
            <div className="text-[11px] uppercase tracking-[0.15em] text-white/35 mt-1">{s.label}</div>
          </div>
        ))}
      </div>

      <div className="mb-2 flex items-center justify-between text-[13px] text-white/45">
        <span>{snap.proven} of {snap.total} machine-checked</span>
        <span className="tabular-nums">{pct}%</span>
      </div>
      <div className="h-1.5 rounded-full bg-white/10 overflow-hidden mb-12">
        <div className="h-full bg-emerald-400/70" style={{ width: `${pct}%` }} />
      </div>

      <h2 id="open-problems" className="text-xl font-semibold text-white/85 mt-14 mb-3 scroll-mt-20">
        Open problems
      </h2>
      {snap.open.length === 0 ? (
        <p className="text-[15px] text-white/55">No open <code className="text-cyan-300/80 bg-white/[0.06] px-1.5 py-0.5 rounded text-[13px] font-mono">sorry</code> — the formalized library is complete.</p>
      ) : (
        <ul className="space-y-2">
          {snap.open.map((r) => (
            <li key={r.name} className="rounded-lg border border-white/10 bg-white/[0.02] px-4 py-3">
              <div className="flex items-baseline justify-between gap-3">
                <span className="text-[15px] text-white/80">{r.title || r.name}</span>
                <span className="text-[11px] uppercase tracking-wider text-amber-300/70">{r.sort || 'sorry'}</span>
              </div>
              <div className="text-[12px] font-mono text-white/35 mt-1 truncate">
                {r.name}{r.file ? ` · ${r.file}${r.line ? `:${r.line}` : ''}` : ''}
              </div>
            </li>
          ))}
        </ul>
      )}
    </>
  )
}
