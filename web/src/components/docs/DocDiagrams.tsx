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

/** How a hash gets its derived number from its first appearance in a document. */
export function NumberingFlow() {
  const rows: [string, string, string][] = [
    ['a1f3c9e2', 'Definition', '3.1'],
    ['9c2e0f81', 'Theorem', '3.2'],
    ['4e7d22b0', 'Corollary', '3.3'],
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
            <Num>3.1</Num>
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
