'use client'

import { useState, useEffect } from 'react'

export interface TocItem { level: number; text: string; id: string }

/** Three-column documentation shell: left master TOC, MDX content, right
 *  on-this-page TOC. Styled to the project's dark aesthetic. */
export function DocsShell({ title, toc, children }: { title: string; toc: TocItem[]; children: React.ReactNode }) {
  const sections = toc.filter((t) => t.level === 2)
  const [active, setActive] = useState('')

  useEffect(() => {
    const obs = new IntersectionObserver(
      (entries) => entries.forEach((e) => { if (e.isIntersecting) setActive((e.target as HTMLElement).id) }),
      { rootMargin: '0px 0px -78% 0px', threshold: 0 },
    )
    toc.forEach((t) => { const el = document.getElementById(t.id); if (el) obs.observe(el) })
    return () => obs.disconnect()
  }, [toc])

  return (
    <div className="flex max-w-7xl mx-auto w-full">
      {/* left — master TOC */}
      <nav className="hidden lg:block w-56 shrink-0 sticky top-0 self-start max-h-[calc(100vh-3.5rem)] overflow-y-auto px-6 py-12 border-r border-white/5">
        <div className="text-[10px] uppercase tracking-[0.2em] text-white/25 mb-4">Documentation</div>
        <div className="text-white/75 text-sm font-medium mb-3">{title}</div>
        <ul className="space-y-1.5 text-[13px]">
          {sections.map((s) => (
            <li key={s.id}>
              <a href={`#${s.id}`} className={`block transition-colors ${active === s.id ? 'text-white/85' : 'text-white/35 hover:text-white/60'}`}>{s.text}</a>
            </li>
          ))}
        </ul>
      </nav>

      {/* center — MDX content */}
      <article className="flex-1 min-w-0 px-8 lg:px-14 py-14 max-w-2xl">{children}</article>

      {/* right — on this page */}
      <nav className="hidden xl:block w-56 shrink-0 sticky top-0 self-start max-h-[calc(100vh-3.5rem)] overflow-y-auto px-6 py-12">
        <div className="text-[10px] uppercase tracking-[0.2em] text-white/25 mb-4">On this page</div>
        <ul className="space-y-1.5 text-[13px]">
          {toc.map((t) => (
            <li key={t.id} className={t.level === 3 ? 'pl-3' : ''}>
              <a href={`#${t.id}`} className={`block transition-colors ${active === t.id ? 'text-white/80' : 'text-white/30 hover:text-white/55'}`}>{t.text}</a>
            </li>
          ))}
        </ul>
      </nav>
    </div>
  )
}
