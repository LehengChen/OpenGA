import fs from 'node:fs'
import path from 'node:path'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const projectPath = searchParams.get('path')
  if (!projectPath) return Response.json({ detail: 'path required' }, { status: 400 })

  if (!fs.existsSync(projectPath)) {
    return Response.json({ exists: false, hasNetmath: false, isSignatureProject: false, message: 'Directory does not exist' })
  }
  const ready = fs.existsSync(path.join(projectPath, '.astrolabe'))
  return Response.json({ exists: true, isSignatureProject: ready, message: ready ? 'Ready.' : 'No .astrolabe/ found' })
}
