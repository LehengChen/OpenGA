// Hand-authored schematic diagrams for the docs — pure presentational, no deps.
// Styled to the site: monochrome + hairlines, mono cyan for hashes, the Astrolabe
// orange for assigned numbers. Used from MDX via the route's components map.

const Hash = ({ children }: { children: React.ReactNode }) => (
  <span className="text-cyan-300/80">{children}</span>
)
const Num = ({ children }: { children: React.ReactNode }) => (
  <span className="text-[#e67e22]">{children}</span>
)
const Dim = ({ children }: { children: React.ReactNode }) => (
  <span className="text-white/30">{children}</span>
)

/** The one-file-per-node storage layout. */
export function StorageTree() {
  return (
    <figure className="my-8">
      <pre className="rounded-lg border border-white/10 bg-white/[0.02] p-5 text-[13px] leading-relaxed font-mono text-white/55 overflow-x-auto">
        <div><Dim>.astrolabe/</Dim></div>
        <div>├─ atoms/</div>
        <div>│  ├─ <Hash>38c99016b279</Hash>.md{'   '}<Dim>← one file per node</Dim></div>
        <div>│  └─ <Hash>097d60abf481</Hash>.md</div>
        <div>├─ edges/</div>
        <div>│  └─ <Hash>014c1e2a49fe</Hash>.md{'   '}<Dim>← a (lean, tex) bridge</Dim></div>
        <div>└─ docs/</div>
        <div>{'   '}├─ 00-index.mdx</div>
        <div>{'   '}└─ 03-geodesics.mdx{'  '}<Dim>composes nodes by hash</Dim></div>
      </pre>
      <figcaption className="mt-2 text-[13px] text-white/35">
        Every node is a single file named by its hash; documents only reference them.
      </figcaption>
    </figure>
  )
}

/** One row of an entry: a fixed-width key and its value. */
function Field({ k, v, indent }: { k: string; v: React.ReactNode; indent?: boolean }) {
  return (
    <div className={`flex gap-2 ${indent ? 'pl-5' : ''}`}>
      <span className="w-14 shrink-0 text-white/35">{k}</span>
      <span className="text-white/65 min-w-0 break-words">{v}</span>
    </div>
  )
}

/** An entry in the canonical (hash, ref, record) shape — everything but ref and
 *  hash lives, layered, inside record. */
function NodeEntry({ hash, refs, record }: { hash: string; refs: string[]; record: [string, React.ReactNode][] }) {
  const badge = refs.length === 1 ? 'self-reference → atom' : refs.length === 2 ? 'two atoms → edge' : ''
  return (
    <figure className="my-5">
      <div className="rounded-lg border border-white/10 bg-white/[0.02] p-4 text-[12px] font-mono leading-relaxed">
        <Field k="hash" v={<Hash>{hash}</Hash>} />
        <Field k="ref" v={<>[ <Hash>{refs.join(', ')}</Hash> ]{badge && <Dim>{'  ← '}{badge}</Dim>}</>} />
        <div className="text-white/35 mt-0.5">record</div>
        {record.map(([k, v]) => <Field key={k} k={k} v={v} indent />)}
      </div>
    </figure>
  )
}

/** A real atom from the Riemannian Geometry project. */
export function AtomExample() {
  return (
    <NodeEntry
      hash="38c99016b279"
      refs={['38c99016b279']}
      record={[
        ['sort', 'definition'],
        ['source', 'tex'],
        ['title', 'Geodesic sphere'],
        ['notes', String.raw`$S_\delta = \exp_p(\{v : \lVert v\rVert = \delta\})$`],
      ]}
    />
  )
}

/** A real (lean, tex) cross-source edge. */
export function EdgeExample() {
  return (
    <NodeEntry
      hash="014c1e2a49fe"
      refs={['264fbf8cb406', '6e6c552589c3']}
      record={[
        ['sort', <>(ref[0].source, ref[1].source)<Dim>{'  = (lean, tex)'}</Dim></>],
        ['rel', 'formalizes'],
        ['kind', 'bipartite'],
        ['notes', 'formalizes «geodesic»'],
      ]}
    />
  )
}

/** Two tiers: atoms + binary edges form a traditional graph; a hyperedge is a
 *  structure built on top of it, bundling several nodes into one n-ary relation. */
export function GraphLayers() {
  const nodes: [number, number][] = [
    [155, 100], // center theorem
    [55, 50], [60, 160], // cited-by (left)
    [255, 52], [320, 110], [250, 165], // joined cluster (right)
  ]
  const edges: [number, number][] = [[0, 1], [0, 2], [0, 3], [0, 4], [0, 5], [3, 4]]
  return (
    <figure className="my-8">
      <div className="rounded-lg border border-white/10 bg-white/[0.02] p-5">
        <svg viewBox="0 0 380 200" className="w-full max-w-lg mx-auto" role="img"
          aria-label="Atoms and binary edges form a graph; a hyperedge bundles several nodes.">
          {/* hyperedge: a structure layered over a cluster of the graph */}
          <ellipse cx="250" cy="108" rx="100" ry="78" fill="rgba(230,126,34,0.06)"
            stroke="#e67e22" strokeOpacity="0.55" strokeWidth="1" strokeDasharray="4 3" />
          <text x="333" y="28" textAnchor="end" fontSize="11" fill="#e67e22" fillOpacity="0.85"
            fontFamily="ui-monospace, monospace">hyperedge · |ref| ≥ 3</text>

          {/* binary edges → lines */}
          {edges.map(([a, b], i) => (
            <line key={i} x1={nodes[a][0]} y1={nodes[a][1]} x2={nodes[b][0]} y2={nodes[b][1]}
              stroke="rgba(255,255,255,0.20)" strokeWidth="1" />
          ))}
          <text x="44" y="112" fontSize="11" fill="rgba(255,255,255,0.35)"
            fontFamily="ui-monospace, monospace">edge · |ref| = 2</text>

          {/* atoms → nodes */}
          {nodes.map(([x, y], i) => (
            <circle key={i} cx={x} cy={y} r={i === 0 ? 6 : 5}
              fill="rgba(255,255,255,0.75)" />
          ))}
        </svg>
      </div>
      <figcaption className="mt-2 text-[13px] text-white/35">
        Atoms and binary edges are a traditional graph; a hyperedge is layered on top,
        capturing a whole bundle as one n-ary relation.
      </figcaption>
    </figure>
  )
}

/** How a hash gets its derived number from its first appearance in a document. */
export function NumberingFlow() {
  const rows: [string, string, string][] = [
    ['a1f3c9e2', 'Definition', '3.2.1'],
    ['9c2e0f81', 'Theorem', '3.2.2'],
    ['4e7d22b0', 'Corollary', '3.2.3'],
  ]
  return (
    <figure className="my-8">
      <div className="rounded-lg border border-white/10 bg-white/[0.02] p-5 text-[13px] font-mono">
        <div className="flex items-center gap-2 mb-4 text-white/45">
          03-geodesics.mdx <Dim>→ chapter 3</Dim>
        </div>
        <div className="space-y-2.5">
          {rows.map(([h, kind, n]) => (
            <div key={h} className="flex items-center gap-3 whitespace-nowrap">
              <Hash>{h}…</Hash>
              <Dim>{kind} · first appears</Dim>
              <span className="text-white/25">→</span>
              <Num>{n}</Num>
            </div>
          ))}
          <div className="flex items-center gap-3 whitespace-nowrap pt-1.5 border-t border-white/[0.07]">
            <Hash>a1f3c9e2…</Hash>
            <Dim>appears again</Dim>
            <span className="text-white/25">→</span>
            <Num>3.2.1</Num>
            <Dim>(same hash, same number)</Dim>
          </div>
        </div>
      </div>
      <figcaption className="mt-2 text-[13px] text-white/35">
        The number is assigned on first occurrence and follows the hash — never stored,
        always consistent within the project.
      </figcaption>
    </figure>
  )
}
