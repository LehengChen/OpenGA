import ParticleBackground from '@/components/ParticleBackground'
import { Navbar } from '@/components/Navbar'

// Placeholder. Replace the hard-coded challenges with data once we wire this to
// the knowledge graph (open `sorry`s + tex statements that lack a Lean proof).
const CHALLENGES = [
  {
    tag: 'open · hard',
    title: 'The exponential differential',
    blurb:
      'Formalize d(exp_p)_v for general v (only the v = 0 case exists). This is the single hard core blocking the Gauss lemma → Hopf–Rinow chain.',
    ref: 'do Carmo, Ch. 5 — exp ↔ Jacobi',
  },
  {
    tag: 'open · 4 sorries',
    title: 'Hopf–Rinow, unconditional',
    blurb:
      'Discharge the remaining sorries: minimizing-geodesic existence (geodesic-sphere + connectedness argument) and completeness via Heine–Borel.',
    ref: 'do Carmo, Ch. 7 §2',
  },
  {
    tag: 'open · elementary',
    title: 'Gauss lemma, no Jacobi fields',
    blurb:
      'Prove dist(exp_p v, p) = ‖v‖ via the symmetry lemma (3.4, done) and a geodesic variation — the elementary route that avoids the second-variation machinery.',
    ref: 'do Carmo, Ch. 3 §3, Lemma 3.5',
  },
]

export default function Activities() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 relative overflow-y-auto">
        <ParticleBackground particleCount={200} mouseRadius={220} />
        <div className="relative z-10 max-w-3xl mx-auto px-8 py-24">
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">Current activities</p>
          <h1 className="text-4xl font-bold tracking-[0.04em] text-white/90 mb-3">
            Riemannian Geometry Challenge
          </h1>
          <p className="text-sm text-white/45 mb-16 max-w-xl leading-relaxed">
            Open problems on the road to a fully formalized <span className="text-white/70">Hopf–Rinow</span>,
            sourced from the live tex ↔ Lean knowledge graph. Pick one, formalize it, close the loop.
            <span className="block mt-1 text-white/25">(placeholder — challenges will be generated from the graph&apos;s open <code className="text-cyan-400/70">sorry</code>s.)</span>
          </p>

          <div className="space-y-4">
            {CHALLENGES.map((c) => (
              <div
                key={c.title}
                className="group border border-white/10 hover:border-white/25 rounded-lg p-5 transition-colors bg-white/[0.015]"
              >
                <div className="flex items-center justify-between mb-2">
                  <span className="text-[10px] uppercase tracking-wider text-cyan-400/60 font-medium">{c.tag}</span>
                  <span className="text-[11px] text-white/25">{c.ref}</span>
                </div>
                <h2 className="text-lg font-medium text-white/85 group-hover:text-white transition-colors mb-1.5">
                  {c.title}
                </h2>
                <p className="text-sm text-white/45 leading-relaxed">{c.blurb}</p>
              </div>
            ))}
          </div>

          <p className="text-xs text-white/25 mt-16">
            Want to contribute? See the loop in <code className="text-white/40">docs/LEAN_TEX_WORKFLOW.md</code>.
          </p>
        </div>
      </main>
    </div>
  )
}
