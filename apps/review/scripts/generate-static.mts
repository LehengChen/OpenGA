// Pre-render every API response the read-only frontend needs into static JSON
// files under dist/data/, so the review app can be published to GitHub Pages
// with no backend. Run after `vite build`. Mirrors the live API exactly (same
// enrichment, same source panels — including the do Carmo Lean formalization).
import fs from 'node:fs';
import path from 'node:path';
import {
  listProjects,
  nextLeafId,
  prevLeafId,
  readTasks,
  readTaskSource
} from '../server/lib/taskStore.js';
import { enrichLeafTask } from '../server/lib/sources/docarmoLean.js';

const OUT = path.resolve(process.cwd(), 'dist', 'data');

// Which projects to pre-render. Defaults to riemannian-geometry (the do Carmo
// formalization status); other projects (e.g. the Lee import, whose Lean source
// rendering shells out to git per declaration) are slow, so opt in explicitly
// via STATIC_PROJECTS=a,b or STATIC_PROJECTS=all.
const projectFilter = (process.env.STATIC_PROJECTS ?? 'riemannian-geometry').trim();
const selected = projectFilter === 'all' ? null : new Set(projectFilter.split(',').map((s) => s.trim()));

function writeJson(rel: string, data: unknown): void {
  const file = path.join(OUT, rel);
  fs.mkdirSync(path.dirname(file), { recursive: true });
  fs.writeFileSync(file, JSON.stringify(data));
}

const projects = listProjects().filter((project) => !selected || selected.has(project.id));
writeJson('projects.json', projects);

for (const project of projects) {
  const pid = project.id;
  let dataset;
  try {
    dataset = readTasks(pid);
  } catch (error) {
    console.warn(`skip project ${pid}: ${String(error)}`);
    continue;
  }
  for (const task of dataset.tasks) enrichLeafTask(task);
  writeJson(`projects/${pid}/tasks.json`, dataset);

  const leaves = dataset.tasks.filter((task) => task.kind === 'leaf');
  let sourced = 0;
  for (const task of leaves) {
    try {
      writeJson(`projects/${pid}/tasks/${task.id}/source.json`, readTaskSource(pid, task));
      sourced++;
    } catch (error) {
      // e.g. a Lean-source ref not available in the checkout; keep the page usable.
      writeJson(`projects/${pid}/tasks/${task.id}/source.json`, {
        taskId: task.id,
        panels: [],
        error: String(error)
      });
    }
    writeJson(`projects/${pid}/tasks/${task.id}/neighbors.json`, {
      prevId: prevLeafId(dataset.tasks, task.id),
      nextId: nextLeafId(dataset.tasks, task.id)
    });
  }
  console.log(`generated ${pid}: ${leaves.length} leaves (${sourced} with source)`);
}

console.log(`static data written to ${OUT}`);
