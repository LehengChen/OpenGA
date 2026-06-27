import fs from 'node:fs'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const filePath = searchParams.get('path')
  if (!filePath) return Response.json({ detail: 'path required' }, { status: 400 })
  if (!fs.existsSync(filePath)) return Response.json({ detail: `File not found: ${filePath}` }, { status: 404 })

  const line = Number(searchParams.get('line') ?? '1')
  const context = Number(searchParams.get('context') ?? '20')
  const lines = fs.readFileSync(filePath, 'utf8').split('\n')
  const total = lines.length
  const start = Math.max(1, line - context)
  const end = Math.min(total, line + context)
  return Response.json({
    content: lines.slice(start - 1, end).join('\n'),
    startLine: start,
    endLine: end,
    totalLines: total,
  })
}
