import fs from 'fs'
import path from 'path'
import { notFound } from 'next/navigation'
import { compileMDX } from 'next-mdx-remote/rsc'
import remarkGfm from 'remark-gfm'
import remarkMath from 'remark-math'
import rehypeKatex from 'rehype-katex'
import 'katex/dist/katex.min.css'
import { Navbar } from '@/components/Navbar'
import { DocsShell, type TocItem } from '@/components/DocsShell'
import { StatusBoard } from '@/components/StatusBoard'
import { DOCS } from '@/lib/docs'

export function generateStaticParams() {
  return DOCS.map((d) => ({ slug: d.slug }))
}

const slug = (s: string) => s.toLowerCase().replace(/[^a-z0-9]+/g, '-').replace(/^-+|-+$/g, '')
const textOf = (c: any): string =>
  Array.isArray(c) ? c.map(textOf).join('') : typeof c === 'string' ? c : c?.props?.children ? textOf(c.props.children) : ''

// MDX element overrides — the project's dark documentation style.
const components = {
  h2: ({ children }: any) => <h2 id={slug(textOf(children))} className="text-xl font-semibold text-white/85 mt-14 mb-3 scroll-mt-20">{children}</h2>,
  h3: ({ children }: any) => <h3 id={slug(textOf(children))} className="text-base font-medium text-white/80 mt-8 mb-2 scroll-mt-20">{children}</h3>,
  p: ({ children }: any) => <p className="text-[15px] leading-relaxed text-white/55 mb-4">{children}</p>,
  ul: ({ children }: any) => <ul className="list-disc list-inside text-[15px] text-white/55 mb-4 space-y-1">{children}</ul>,
  ol: ({ children }: any) => <ol className="text-[15px] text-white/55 mb-4 space-y-2 list-none">{children}</ol>,
  li: ({ children }: any) => <li>{children}</li>,
  strong: ({ children }: any) => <strong className="text-white/80 font-medium">{children}</strong>,
  em: ({ children }: any) => <em className="italic text-white/45">{children}</em>,
  a: ({ href, children }: any) => (
    <a href={href} target="_blank" rel="noopener noreferrer"
      className="text-white/70 hover:text-white underline decoration-white/20 hover:decoration-white/50 underline-offset-2 transition-colors">{children}</a>
  ),
  hr: () => <hr className="border-white/10 my-10" />,
  code: ({ children }: any) => <code className="text-cyan-300/80 bg-white/[0.06] px-1.5 py-0.5 rounded text-[13px] font-mono">{children}</code>,
}

function parseToc(src: string): TocItem[] {
  return src.split('\n').filter((l) => /^#{2,3}\s/.test(l)).map((l) => {
    const level = (l.match(/^#+/) as RegExpMatchArray)[0].length
    const text = l.replace(/^#+\s+/, '').replace(/[*`_]/g, '')
    return { level, text, id: slug(text) }
  })
}

export default async function Page({ params }: { params: Promise<{ slug: string }> }) {
  const { slug: s } = await params
  const doc = DOCS.find((d) => d.slug === s)
  if (!doc) notFound()

  // Live docs (e.g. Status) render from a component, not an MDX file, so their
  // content reflects the store in real time rather than a stored snapshot.
  if (doc.live) {
    const toc: TocItem[] = [
      { level: 2, text: 'Summary', id: 'summary' },
      { level: 2, text: 'Open problems', id: 'open-problems' },
    ]
    return (
      <div className="h-screen flex flex-col bg-[#0a0a0f] text-white">
        <Navbar />
        <main className="flex-1 overflow-y-auto">
          <DocsShell docs={DOCS} current={doc.slug} toc={toc}>
            <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">{doc.eyebrow}</p>
            <h1 className="text-4xl font-bold tracking-[0.03em] text-white/90 mb-8">{doc.title}</h1>
            <StatusBoard />
          </DocsShell>
        </main>
      </div>
    )
  }

  const source = fs.readFileSync(path.join(process.cwd(), `content/${doc.slug}.mdx`), 'utf8')
  const { content } = await compileMDX({
    source,
    components,
    options: { mdxOptions: { remarkPlugins: [remarkGfm, remarkMath], rehypePlugins: [rehypeKatex as any] } },
  })

  return (
    <div className="h-screen flex flex-col bg-[#0a0a0f] text-white">
      <Navbar />
      <main className="flex-1 overflow-y-auto">
        <DocsShell docs={DOCS} current={doc.slug} toc={parseToc(source)}>
          <p className="text-xs uppercase tracking-[0.2em] text-white/30 mb-3">{doc.eyebrow}</p>
          <h1 className="text-4xl font-bold tracking-[0.03em] text-white/90 mb-8">{doc.title}</h1>
          {content}
        </DocsShell>
      </main>
    </div>
  )
}
