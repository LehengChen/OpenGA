import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { dump, load } from 'js-yaml';
import type { ReviewTask, TaskDataset } from '../../src/lib/taskSchema';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const projectRoot = path.resolve(__dirname, '../../../..');
export const yamlPath = path.join(
  projectRoot,
  'projects/riemannian-geometry/tasks/pilot.tasks.yaml'
);
export const jsonPath = path.join(
  projectRoot,
  'apps/review/src/data/pilot.tasks.json'
);

class Mutex {
  private locked = false;
  private queue: Array<() => void> = [];

  async acquire(): Promise<() => void> {
    return new Promise((resolve) => {
      const release = () => {
        const next = this.queue.shift();
        if (next) {
          next();
        } else {
          this.locked = false;
        }
      };

      if (!this.locked) {
        this.locked = true;
        resolve(release);
      } else {
        this.queue.push(() => resolve(release));
      }
    });
  }
}

const writeLock = new Mutex();

export async function withTaskLock<T>(fn: () => T | Promise<T>): Promise<T> {
  const release = await writeLock.acquire();
  try {
    return await fn();
  } finally {
    release();
  }
}

export function readTasks(): TaskDataset {
  const text = fs.readFileSync(yamlPath, 'utf-8');
  return load(text) as TaskDataset;
}

function atomicWriteFileSync(filePath: string, content: string): void {
  const tmpPath = `${filePath}.tmp-${process.pid}-${Date.now()}`;
  fs.writeFileSync(tmpPath, content, 'utf-8');
  fs.renameSync(tmpPath, filePath);
}

export function writeTasks(dataset: TaskDataset): void {
  const yamlText = dump(dataset, {
    indent: 2,
    lineWidth: -1,
    seqNoIndent: true,
    sortKeys: false
  });
  atomicWriteFileSync(yamlPath, yamlText);

  const jsonText = JSON.stringify(dataset, null, 2) + '\n';
  atomicWriteFileSync(jsonPath, jsonText);
}

export function findTask(tasks: ReviewTask[], taskId: string): ReviewTask | undefined {
  return tasks.find((task) => task.id === taskId);
}

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

export function leafTasksInOrder(tasks: ReviewTask[]): ReviewTask[] {
  const leaves = tasks.filter((task) => task.kind === 'leaf');
  return leaves.sort((a, b) => {
    const chapterDiff = (a.chapter ?? Infinity) - (b.chapter ?? Infinity);
    if (chapterDiff !== 0) return chapterDiff;
    return (a.dcref ?? '').localeCompare(b.dcref ?? '');
  });
}

export function nextLeafId(tasks: ReviewTask[], currentId: string): string | null {
  const leaves = leafTasksInOrder(tasks);
  const index = leaves.findIndex((task) => task.id === currentId);
  if (index === -1 || index === leaves.length - 1) return null;
  return leaves[index + 1].id;
}

export function prevLeafId(tasks: ReviewTask[], currentId: string): string | null {
  const leaves = leafTasksInOrder(tasks);
  const index = leaves.findIndex((task) => task.id === currentId);
  if (index <= 0) return null;
  return leaves[index - 1].id;
}
