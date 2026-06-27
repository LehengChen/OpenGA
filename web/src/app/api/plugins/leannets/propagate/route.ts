import { loadStore } from '@/lib/server/store'
import { toGraph } from '@/lib/server/analysis'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

/** Semantic propagation: every atom that depends on `changed`, via reverse BFS
 *  over the skeleton (edge ref[0] -> ref[1] means ref[0] depends on ref[1]). */
export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  const changed = searchParams.get('changed') ?? ''
  if (!projectPath) return Response.json({ detail: 'path required' }, { status: 400 })

  const g = toGraph(loadStore(projectPath))
  if (!g.hasNode(changed)) return Response.json({ changed, affected: [] })

  const affected = new Set<string>()
  const stack = [changed]
  while (stack.length) {
    const u = stack.pop()!
    g.forEachInNeighbor(u, (p) => { if (!affected.has(p)) { affected.add(p); stack.push(p) } })
  }
  return Response.json({ changed, affected: [...affected].sort() })
}
