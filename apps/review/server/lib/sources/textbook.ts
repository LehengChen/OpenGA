import fs from 'node:fs';
import { execFileSync } from 'node:child_process';
import type { ReviewTask } from '../../../src/lib/taskSchema';
import type { ProjectConfig } from '../taskStore/projects.js';
import type { TextbookEntry } from './types.js';

const textbookFileCache = new Map<string, TextbookEntry[]>();

export function normalizeTextbookMarkdown(source: string): string {
  return source
    .replace(/\\\[/g, '$$')
    .replace(/\\\]/g, '$$')
    .replace(/\\\(/g, '$')
    .replace(/\\\)/g, '$')
    .replace(/[ \t]+$/gm, '');
}

export function renderTextbookEntry(entry: TextbookEntry, fallbackLabel: string): string {
  const pieces = [
    `# ${entry.label ?? fallbackLabel}`,
    normalizeTextbookMarkdown(entry.content ?? '')
  ];
  if (entry.dependencies?.length) {
    pieces.push(`Dependencies: ${entry.dependencies.join(', ')}`);
  }
  if (entry.proof) {
    pieces.push('## Proof', normalizeTextbookMarkdown(entry.proof));
  }
  return pieces.join('\n\n').trim();
}

export function loadTextbookEntry(config: ProjectConfig, task: ReviewTask): TextbookEntry | null {
  if (!task.source?.textbook_json || !task.source.textbook_label) return null;
  if (!config.textbookZipPath) return null;
  if (!fs.existsSync(config.textbookZipPath)) {
    return {
      label: task.source.textbook_label,
      content: [
        `Textbook source zip not found: ${config.textbookZipPath}`,
        '',
        'The default copy is tracked at projects/smooth-manifolds-lee/sources/smooth-manifolds.zip. Set SMOOTH_MANIFOLDS_LEE_ZIP only if you want to use another local copy.'
      ].join('\n')
    };
  }
  const zipEntry = task.source.textbook_json;
  if (!zipEntry.endsWith('.json') || zipEntry.includes('..')) {
    throw new Error('Invalid textbook JSON path');
  }
  const cacheKey = `${config.textbookZipPath}:${zipEntry}`;
  let entries = textbookFileCache.get(cacheKey);
  if (!entries) {
    const raw = execFileSync('unzip', ['-p', config.textbookZipPath, zipEntry], {
      encoding: 'utf-8',
      maxBuffer: 10 * 1024 * 1024
    });
    entries = JSON.parse(raw) as TextbookEntry[];
    textbookFileCache.set(cacheKey, entries);
  }
  const entry = entries.find((item) => item.label === task.source?.textbook_label);
  if (!entry) {
    return {
      label: task.source.textbook_label,
      content: `Textbook entry not found: ${task.source.textbook_label}`
    };
  }
  return entry;
}
