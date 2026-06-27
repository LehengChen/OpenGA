import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const raw = searchParams.get('path')
  if (!raw) return Response.json({ detail: 'path required' }, { status: 400 })
  const filePath = resolveFs(raw)
  if (!fs.existsSync(filePath)) return Response.json({ detail: `File not found: ${filePath}` }, { status: 404 })
  return Response.json({ content: fs.readFileSync(filePath, 'utf8'), name: path.basename(filePath) })
}
