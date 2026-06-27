import { loadStore } from '@/lib/server/store'
import {
  toGraph, degreeMetric, centralityMetric, dagMetric,
  communityMetric, clusterByAttr, stageMetric,
} from '@/lib/server/analysis'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

/** Compute a metric over the whole 1-skeleton: { node: value }. */
export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  const metric = searchParams.get('metric') ?? ''
  if (!projectPath) return Response.json({ detail: 'path required' }, { status: 400 })

  const g = toGraph(loadStore(projectPath))
  if (metric === 'degree' || metric === 'in-degree' || metric === 'out-degree') {
    return Response.json(degreeMetric(g, metric === 'degree' ? 'total' : metric === 'in-degree' ? 'in' : 'out'))
  }
  if (metric === 'pagerank' || metric === 'betweenness') return Response.json(centralityMetric(g, metric))
  if (metric === 'depth' || metric === 'reachability') return Response.json(dagMetric(g, metric))
  if (metric === 'community') return Response.json(communityMetric(g))
  if (metric === 'cluster-louvain') return Response.json(communityMetric(g))
  if (metric === 'cluster-sort') return Response.json(clusterByAttr(g, 'sort'))
  if (metric === 'cluster-stage') return Response.json(stageMetric(g))
  return Response.json({ error: `Unknown metric: ${metric}` })
}
