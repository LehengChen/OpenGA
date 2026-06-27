import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const raw = searchParams.get('path')
  if (!raw) return Response.json({ detail: 'path required' }, { status: 400 })
  const projectPath = resolveFs(raw)

  if (!fs.existsSync(projectPath)) {
    return Response.json({ exists: false, hasNetmath: false, isSignatureProject: false, message: 'Directory does not exist' })
  }
  const ready = fs.existsSync(path.join(projectPath, '.astrolabe'))
  return Response.json({ exists: true, isSignatureProject: ready, message: ready ? 'Ready.' : 'No .astrolabe/ found' })
}
