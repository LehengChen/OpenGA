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

export function readTasks(): TaskDataset {
  const text = fs.readFileSync(yamlPath, 'utf-8');
  return load(text) as TaskDataset;
}

export function writeTasks(dataset: TaskDataset): void {
  const yamlText = dump(dataset, {
    indent: 2,
    lineWidth: -1,
    noArrayIndent: true,
    sortKeys: false
  });
  fs.writeFileSync(yamlPath, yamlText, 'utf-8');

  const jsonText = JSON.stringify(dataset, null, 2) + '\n';
  fs.writeFileSync(jsonPath, jsonText, 'utf-8');
}

export function findTask(tasks: ReviewTask[], taskId: string): ReviewTask | undefined {
  return tasks.find((task) => task.id === taskId);
}

export function readAtom(atomPath: string): string {
  const fullPath = path.join(projectRoot, atomPath);
  return fs.readFileSync(fullPath, 'utf-8');
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
