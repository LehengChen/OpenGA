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
        <div>│  ├─ <Hash>a1f3c9e20b4d</Hash>.md{'   '}<Dim>← one file per node</Dim></div>
        <div>│  └─ <Hash>9c2e0f81a3c7</Hash>.md</div>
        <div>├─ edges/</div>
        <div>│  └─ <Hash>4d8b1a05f9e2</Hash>.md{'   '}<Dim>← a (lean, tex) bridge</Dim></div>
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
