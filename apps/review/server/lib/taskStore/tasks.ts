import fs from 'node:fs';
import path from 'node:path';
import { dump, load } from 'js-yaml';
import type { ReviewTask, TaskDataset } from '../../../src/lib/taskSchema';
import { atomicWriteFileSync } from './files.js';
import { defaultProjectId } from './paths.js';
import { getProjectConfig } from './projects.js';

export function readTasks(projectId = defaultProjectId): TaskDataset {
  const config = getProjectConfig(projectId);
  const text = fs.readFileSync(config.yamlPath, 'utf-8');
  const dataset = load(text) as TaskDataset;
  return {
    ...dataset,
    title: dataset.title ?? config.title,
    description: dataset.description ?? config.description,
    review_kind: dataset.review_kind ?? config.reviewKind
  };
}

export function writeTasks(projectId: string, dataset: TaskDataset): void {
  const config = getProjectConfig(projectId);
  const datasetForWrite: TaskDataset = { ...dataset };
  if (projectId === defaultProjectId) {
    delete datasetForWrite.title;
    delete datasetForWrite.description;
    delete datasetForWrite.review_kind;
  }
  const yamlText = dump(datasetForWrite, {
    indent: 2,
    lineWidth: -1,
    seqNoIndent: true,
    sortKeys: false
  });
  fs.mkdirSync(path.dirname(config.yamlPath), { recursive: true });
  atomicWriteFileSync(config.yamlPath, yamlText);

  if (config.jsonPath) {
    const jsonText = JSON.stringify(datasetForWrite, null, 2) + '\n';
    fs.mkdirSync(path.dirname(config.jsonPath), { recursive: true });
    atomicWriteFileSync(config.jsonPath, jsonText);
  }
}

export function findTask(tasks: ReviewTask[], taskId: string): ReviewTask | undefined {
  return tasks.find((task) => task.id === taskId);
}

export function leafTasksInOrder(tasks: ReviewTask[]): ReviewTask[] {
  return tasks.filter((task) => task.kind === 'leaf');
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
