import fs from 'node:fs';
import path from 'node:path';
import { atomicWriteFileSync } from './files.js';
import { projectRoot } from './paths.js';

function resolveAtomPath(atomPath: string): string {
  const resolved = path.resolve(projectRoot, atomPath);
  const relative = path.relative(projectRoot, resolved);
  if (path.isAbsolute(relative) || relative.startsWith('..')) {
    throw new Error('Invalid atom path');
  }
  return resolved;
}

export function readAtom(atomPath: string): string {
  const fullPath = resolveAtomPath(atomPath);
  return fs.readFileSync(fullPath, 'utf-8');
}

export function writeAtom(atomPath: string, content: string): void {
  const fullPath = resolveAtomPath(atomPath);
  fs.mkdirSync(path.dirname(fullPath), { recursive: true });
  atomicWriteFileSync(fullPath, content);
}
