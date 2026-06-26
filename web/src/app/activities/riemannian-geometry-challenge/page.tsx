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
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">An open public initiative</p>
          <h1 className="text-4xl font-bold tracking-[0.03em] text-white/90 mb-6">
            Riemannian Geometry Challenge
          </h1>
          <p className="text-[15px] leading-relaxed text-white/55 max-w-2xl">
            We are building Riemannian geometry as a public good: a living, machine-verified textbook
            that belongs to the whole community — open to learn from, to contribute to, to reuse, and to
            build on. do&nbsp;Carmo&apos;s <span className="italic">Riemannian Geometry</span> is our starting
            blueprint; the aim is bigger — a lasting, international foundation for the field that keeps
            growing, made by everyone, for everyone.
          </p>
          <p className="text-[15px] leading-relaxed text-white/55 max-w-2xl mt-4">
            It is open to anyone — mathematicians, students, programmers, designers. There is no gate. Every
            piece that lands becomes part of a foundation that others can rely on and reuse, forever.
          </p>

          <Section title="Ways to contribute">
            <Track name="Mathematics" blurb="Prove the theorems so a machine can check them; complete the foundations, one result at a time." />
            <Track name="Review" blurb="Keep the mathematics honest — on the written side and the formal side; find the gap, flag the step that does not follow." />
            <Track name="Design & visualization" blurb="Make a body of knowledge with thousands of results legible, beautiful, and a pleasure to explore." />
            <Track name="Tools & infrastructure" blurb="Build the systems that let everyone read, contribute, and reuse — the public plumbing of the textbook." />
          </Section>

          <Section title="How we work together">
            <p>
              <span className="text-white/80">Challengers</span> attack the written mathematics — find the
              holes the prose hides, the assumption never stated, the step that does not follow.
            </p>
            <p>
              <span className="text-white/80">Reviewers</span> defend the record — read a proof and confirm it
              really proves what it claims.
            </p>
            <p>
              <span className="text-white/80">Contributors</span> close the gaps — write, formalize, design,
              connect. Everything that lands is shared, reusable, and built on by the next person.
            </p>
          </Section>

          <p className="text-xs text-white/25 mt-16">
            The open problems — current challenges to pick up — go here.
          </p>

          <Section title="References">
            <ol className="space-y-2 text-sm text-white/45">
              <li className="list-none">
                <span className="text-white/35 mr-2">[1]</span>
                M. P. do Carmo,{' '}
                <a
                  href="https://link.springer.com/book/9780817634902"
                  target="_blank"
                  rel="noopener noreferrer"
                  className="italic text-white/70 hover:text-white underline decoration-white/20 hover:decoration-white/50 underline-offset-2 transition-colors"
                >
                  Riemannian Geometry
                </a>
                . Trans. F. Flaherty. Mathematics: Theory &amp; Applications. Birkhäuser, Boston, 1992.
              </li>
            </ol>
          </Section>
        </div>
      </main>
    </div>
  )
}
