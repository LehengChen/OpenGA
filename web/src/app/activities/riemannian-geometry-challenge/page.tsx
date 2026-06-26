import { Navbar } from '@/components/Navbar'

function Section({ title, children }: { title: string; children: React.ReactNode }) {
  return (
    <section className="mt-12">
      <h2 className="text-xs uppercase tracking-[0.2em] text-white/30 mb-4">{title}</h2>
      <div className="space-y-3 text-[15px] leading-relaxed text-white/55">{children}</div>
    </section>
  )
}

function Track({ name, blurb }: { name: string; blurb: string }) {
  return (
    <div className="border-l border-white/10 pl-4 py-1">
      <div className="text-white/80 font-medium text-[15px]">{name}</div>
      <div className="text-sm text-white/45 mt-0.5">{blurb}</div>
    </div>
  )
}

export default function RiemannianGeometryChallenge() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-3xl mx-auto px-8 py-24">
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">Decentralized online formalization</p>
          <h1 className="text-4xl font-bold tracking-[0.03em] text-white/90 mb-6">
            Riemannian Geometry Challenge
          </h1>
          <p className="text-[15px] leading-relaxed text-white/55 max-w-2xl">
            An open, decentralized project to formalize Riemannian geometry — grounded in
            do&nbsp;Carmo&apos;s <span className="italic">Riemannian Geometry</span>. We build a single
            content-addressed knowledge graph in which the natural-language (tex) layer and the formal
            (Lean) layer are linked by cross-source hyperedges, and we advance it with a self-reinforcing
            tex&nbsp;↔&nbsp;Lean loop. Chapter by chapter, the book becomes a machine-checked, navigable graph.
          </p>

          <Section title="Challenge tracks">
            <Track name="Graph visualization" blurb="Optimize the layout / rendering algorithm for the hypergraph — make a 1000-node graph legible and fast." />
            <Track name="Frontend design" blurb="The Astrolabe reading / network / detail UI: navigation, card rendering, the cross-source experience." />
            <Track name="Mathematical completeness" blurb="Discharge the open Lean sorrys — the formalization frontier, advancing chapter by chapter across the book." />
            <Track name="Math content review" blurb="Review the formal proofs and audit the do Carmo transcriptions for fidelity and logical gaps." />
          </Section>

          <Section title="How it works">
            <p>
              <span className="text-white/80">Content-addressing cards.</span> Every statement — a definition,
              a lemma, a Lean declaration — is a content-addressed node, one file per node. Identity is the hash
              of what the node <span className="italic">is</span>, so a card can be re-derived, re-referenced, and
              merged without ambiguity, and the same hash means the same content everywhere it appears.
            </p>
            <p>
              <span className="text-white/80">Hypergraph metrics.</span> The graph is measured, not just drawn:
              degree and connectivity, concept coverage, under-linkage (long content with few edges flags a
              missed concept), and the distance between the formal and informal frontiers. The metrics decide
              where attention goes next.
            </p>
            <p>
              <span className="text-white/80">A self-iterating loop.</span> Audit the graph → pick the most
              upstream gap → formalize or repair it → re-extract, register, bridge → re-audit. Each step usually
              surfaces new gaps and unlocks new ready-to-prove statements, so the loop compounds.
            </p>
          </Section>

          <Section title="Roles">
            <p>
              <span className="text-white/80">Offense</span> attacks the natural language: find the logical holes
              the prose hides behind symbols — a dependency the proof needs but the text never states, a step that
              does not follow.
            </p>
            <p>
              <span className="text-white/80">Defense</span> reviews the formal side: read the Lean code, check that
              a proof says what it claims, and that an interface field is not quietly an axiom.
            </p>
            <p>
              <span className="text-white/80">Submitters</span> close the gaps: transcribe a chapter, formalize a
              lemma, add a cross-source bridge — every contribution is a content-addressed node in the shared graph.
            </p>
          </Section>

          <p className="text-xs text-white/25 mt-16">
            The challenge list — generated from the graph&apos;s open <code className="text-cyan-400/70">sorry</code>s
            and unformalized tex statements — goes here.
          </p>
        </div>
      </main>
    </div>
  )
}
