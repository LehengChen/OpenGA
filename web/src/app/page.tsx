import Link from 'next/link'
import ParticleBackground from '@/components/ParticleBackground'
import { Navbar } from '@/components/Navbar'

// The active project lives outside the web app, as its own folder.
// Override with NEXT_PUBLIC_PROJECT_PATH when deploying elsewhere.
const PROJECT_PATH =
  process.env.NEXT_PUBLIC_PROJECT_PATH || '/Users/moqian/OpenGALib/projects/riemannian-geometry'

export default function Home() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 relative overflow-y-auto">
        <ParticleBackground particleCount={260} mouseRadius={250} />
        <div className="relative z-10 max-w-3xl mx-auto px-8 py-24">
          <h1 className="text-4xl font-bold tracking-[0.15em] text-white/90 mb-2">ASTROLABE</h1>
          <p className="text-sm text-white/40 mb-20">Manage your knowledge network</p>

          <h2 className="text-xs uppercase tracking-wider text-white/30 mb-4">Projects</h2>
          <Link
            href={`/local/edit?path=${encodeURIComponent(PROJECT_PATH)}`}
            className="text-2xl font-medium text-white/85 hover:text-white border-b border-white/15 hover:border-white/50 transition-colors pb-0.5"
          >
            Riemannian Geometry
          </Link>
          <p className="text-sm text-white/40 mt-3">
            A shared tex + Lean knowledge graph of Riemannian geometry — chapters following do Carmo
          </p>

          <h2 className="text-xs uppercase tracking-wider text-white/30 mb-4 mt-20">Current activity</h2>
          <div>
            <h3 className="text-2xl font-medium text-white/85">Riemannian Geometry Challenge</h3>
            <p className="text-sm text-white/40 mt-3">
              Recent — open problems toward a fully formalized Hopf–Rinow, sourced from the live tex ↔ Lean graph.
            </p>
          </div>
        </div>
      </main>
    </div>
  )
}
