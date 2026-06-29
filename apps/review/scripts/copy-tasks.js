import fs from 'fs'
import path from 'path'
import { fileURLToPath } from 'url'

const __dirname = path.dirname(fileURLToPath(import.meta.url))
const root = path.resolve(__dirname, '../../..')
const sourceDir = path.join(root, 'projects/riemannian-geometry/tasks')
const targetDir = path.join(__dirname, '../public/tasks')

if (!fs.existsSync(sourceDir)) {
  console.error(`Source tasks directory not found: ${sourceDir}`)
  process.exit(1)
}

fs.mkdirSync(targetDir, { recursive: true })

for (const file of fs.readdirSync(sourceDir)) {
  const src = path.join(sourceDir, file)
  const dst = path.join(targetDir, file)
  const stat = fs.statSync(src)
  if (stat.isFile()) {
    fs.copyFileSync(src, dst)
    console.log(`Copied ${file} -> public/tasks/${file}`)
  }
}
