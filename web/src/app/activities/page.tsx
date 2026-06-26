import Link from 'next/link'
import ParticleBackground from '@/components/ParticleBackground'
import { Navbar } from '@/components/Navbar'

export default function Activities() {
  return (
    <div className="h-full flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 relative overflow-y-auto">
        <ParticleBackground particleCount={200} mouseRadius={220} />
        <div className="relative z-10 max-w-3xl mx-auto px-8 py-24">
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-10">Current activities</p>

          <Link
            href="/activities/riemannian-geometry-challenge"
            className="group block"
          >
            <h2 className="text-2xl font-medium text-white/85 group-hover:text-white border-b border-white/15 group-hover:border-white/50 transition-colors pb-1 inline-block">
              Riemannian Geometry Challenge
            </h2>
            <p className="text-sm text-white/40 mt-3">Recent — open problems toward Hopf–Rinow</p>
          </Link>
        </div>
      </main>
    </div>
  )
}
