import { Navbar } from '@/components/Navbar'

// Blank canvas for the Riemannian Geometry Challenge. Add the challenge content
// here (or wire it to the knowledge graph) later.
export default function RiemannianGeometryChallenge() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 overflow-y-auto">
        <div className="max-w-3xl mx-auto px-8 py-24">
          <h1 className="text-3xl font-bold tracking-[0.04em] text-white/90">
            Riemannian Geometry Challenge
          </h1>
          {/* content goes here */}
        </div>
      </main>
    </div>
  )
}
