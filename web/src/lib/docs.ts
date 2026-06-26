// The documentation registry — one entry per MDX file in `web/content/`.
// Drives both the dynamic /docs/[slug] route and the left "Documentation" nav.
export interface DocMeta {
  slug: string // file is content/<slug>.mdx
  title: string
  eyebrow: string
}

export const DOCS: DocMeta[] = [
  {
    slug: 'introduction',
    title: 'Introduction',
    eyebrow: 'Riemannian Geometry Challenge',
  },
  {
    slug: 'challenge',
    title: 'Riemannian Geometry Challenge',
    eyebrow: 'An open public initiative',
  },
  {
    slug: 'data-model',
    title: 'Data Model & Astrolabe',
    eyebrow: 'How the knowledge is stored',
  },
]
