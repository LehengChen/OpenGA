import Link from 'next/link'

/** Top navigation bar — gives the site a normal-website feel. */
export function Navbar() {
  return (
    <nav className="h-14 shrink-0 flex items-center px-8 border-b border-white/10 bg-[#0a0a0f]/80 backdrop-blur relative z-20">
      <Link
        href="/"
        className="text-sm font-semibold tracking-[0.22em] text-white/85 hover:text-white transition-colors"
      >
        ASTROLABE
      </Link>
      <div className="ml-auto flex items-center gap-6 text-xs text-white/40">
        <Link href="/" className="hover:text-white/75 transition-colors">
          Home
        </Link>
        <Link href="/docs/introduction" className="hover:text-white/75 transition-colors">
          About us
        </Link>
        <a
          href="https://github.com/MathNetwork/Astrolabe"
          target="_blank"
          rel="noopener noreferrer"
          className="hover:text-white/75 transition-colors"
        >
          GitHub
        </a>
      </div>
    </nav>
  )
}
