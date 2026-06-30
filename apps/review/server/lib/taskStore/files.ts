import fs from 'node:fs';

export function atomicWriteFileSync(filePath: string, content: string): void {
  const tmpPath = `${filePath}.tmp-${process.pid}-${Date.now()}`;
  fs.writeFileSync(tmpPath, content, 'utf-8');
  fs.renameSync(tmpPath, filePath);
}
