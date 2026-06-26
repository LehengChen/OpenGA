// The documentation registry — one entry per MDX file in `web/content/`.
// Drives both the dynamic /docs/[slug] route and the left "Documentation" nav.
export interface DocMeta {
  slug: string // file is content/<slug>.mdx (unless `live`)
  title: string
  eyebrow: string
  live?: boolean // rendered from a live component, not an MDX file
}

export const DOCS: DocMeta[] = [
  {
    slug: 'introduction',
    title: 'Introduction',
    eyebrow: 'Riemannian Geometry Challenge',
  },
  {
    slug: 'status',
    title: 'Status',
    eyebrow: 'Live formalization progress',
    live: true,
  },
  {
    slug: 'challenge',
    title: 'Open Questions',
    eyebrow: 'The questions we are curious about',
  },
  {
    slug: 'data-model',
    title: 'Data Model & Astrolabe',
    eyebrow: 'How the knowledge is stored',
  },
]
