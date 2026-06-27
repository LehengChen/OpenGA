import fs from 'node:fs'
import path from 'node:path'
import { resolveFs } from '@/lib/server/paths'

export const dynamic = 'force-dynamic'
export const runtime = 'nodejs'

/** Latest mtime of .lean files under a lake project at `path` or one level down;
 *  null if there is no lakefile (the common case for a pure md project). */
export async function GET(req: Request) {
  const { searchParams } = new URL(req.url)
  const raw = searchParams.get('path')
  if (!raw) return Response.json({ detail: 'path required' }, { status: 400 })
  const root = resolveFs(raw)

  const hasLake = (d: string) =>
    fs.existsSync(path.join(d, 'lakefile.lean')) || fs.existsSync(path.join(d, 'lakefile.toml'))

  let leanRoot: string | null = null
  if (fs.existsSync(root)) {
    const candidates = [root]
    for (const e of fs.readdirSync(root, { withFileTypes: true })) {
      if (e.isDirectory() && !e.name.startsWith('.')) candidates.push(path.join(root, e.name))
    }
    leanRoot = candidates.find(hasLake) ?? null
  }
  if (!leanRoot) return Response.json({ mtime: null })

  let latest = 0
  const walk = (dir: string) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      if (e.name === '.lake') continue
      const fp = path.join(dir, e.name)
      if (e.isDirectory()) walk(fp)
      else if (e.name.endsWith('.lean')) {
        try { latest = Math.max(latest, fs.statSync(fp).mtimeMs / 1000) } catch { /* ignore */ }
      }
    }
  }
  walk(leanRoot)
  return Response.json({ mtime: latest > 0 ? latest : null })
}
