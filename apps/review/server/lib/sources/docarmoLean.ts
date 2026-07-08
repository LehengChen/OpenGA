import fs from 'node:fs';
import path from 'node:path';
import { load } from 'js-yaml';
import { projectRoot } from '../taskStore/paths.js';
import { readAtom } from '../taskStore/atoms.js';
import type { ReviewTask, TaskSourceItem } from '../../../src/lib/taskSchema';

// Surfaces the Lean formalization of an atom-based (do Carmo) task by walking the
// Astrolabe store: a `formalizes` bridge links a statement atom directly to a
// `source: lean` atom, and a `restates` bridge reaches the blueprint node whose
// `formalizes` bridge names the Lean declaration. The declaration's full source
// (docstring + signature + body/proof) is read from `OpenGALib/`.

const leanRoot = path.join(projectRoot, 'OpenGALib');

type Node = { ref: string[]; fields: Record<string, unknown> };
type Index = { mtime: number; atoms: Map<string, Node>; edges: Map<string, Node> };
const indexCache = new Map<string, Index>();

function parseNode(text: string): Node {
  if (text.startsWith('---\n')) {
    const end = text.indexOf('\n---\n', 3);
    if (end !== -1) {
      const front = (load(text.slice(4, end + 1)) as Record<string, unknown>) ?? {};
      const { ref, ...fields } = front;
      return { ref: Array.isArray(ref) ? (ref as string[]) : [], fields };
    }
  }
  return { ref: [], fields: {} };
}

function dirMtime(dir: string): number {
  try {
    return fs.statSync(dir).mtimeMs;
  } catch {
    return 0;
  }
}

// Resolve the store's atoms/ and edges/ dirs from a task's atom path.
function storeDirs(atomPath: string): { atomsDir: string; edgesDir: string } {
  const atomsDir = path.dirname(path.resolve(projectRoot, atomPath));
  return { atomsDir, edgesDir: path.join(path.dirname(atomsDir), 'edges') };
}

function loadIndex(atomsDir: string, edgesDir: string): Index {
  const mtime = Math.max(dirMtime(atomsDir), dirMtime(edgesDir));
  const cached = indexCache.get(atomsDir);
  if (cached && cached.mtime === mtime) return cached;
  const atoms = new Map<string, Node>();
  const edges = new Map<string, Node>();
  const read = (dir: string, into: Map<string, Node>) => {
    if (!fs.existsSync(dir)) return;
    for (const f of fs.readdirSync(dir)) {
      if (f.endsWith('.md')) {
        into.set(f.slice(0, -3), parseNode(fs.readFileSync(path.join(dir, f), 'utf-8')));
      }
    }
  };
  read(atomsDir, atoms);
  read(edgesDir, edges);
  const index = { mtime, atoms, edges };
  indexCache.set(atomsDir, index);
  return index;
}

type LeanRef = {
  name: string;
  file?: string;
  line?: number;
  state?: string;
  signature?: string;
  via: 'direct' | 'blueprint';
};

function asLeanRef(hash: string, via: LeanRef['via'], atoms: Map<string, Node>): LeanRef | null {
  const node = atoms.get(hash);
  if (!node || node.fields.source !== 'lean' || typeof node.fields.name !== 'string') return null;
  const f = node.fields;
  return {
    name: f.name as string,
    file: typeof f.file === 'string' ? f.file : undefined,
    line: typeof f.line === 'number' ? f.line : undefined,
    state: typeof f.state === 'string' ? f.state : undefined,
    signature: typeof f.content === 'string' ? f.content : undefined,
    via
  };
}

function neighborsByRel(hash: string, rel: string, edges: Map<string, Node>): string[] {
  const out: string[] = [];
  for (const edge of edges.values()) {
    if (edge.fields.rel === rel && edge.ref.includes(hash)) {
      for (const other of edge.ref) if (other !== hash) out.push(other);
    }
  }
  return out;
}

function leanForAtom(atomHash: string, atoms: Map<string, Node>, edges: Map<string, Node>): LeanRef[] {
  const out = new Map<string, LeanRef>();
  for (const other of neighborsByRel(atomHash, 'formalizes', edges)) {
    const ref = asLeanRef(other, 'direct', atoms);
    if (ref) out.set(ref.name, ref);
  }
  for (const bp of neighborsByRel(atomHash, 'restates', edges)) {
    for (const other of neighborsByRel(bp, 'formalizes', edges)) {
      const ref = asLeanRef(other, 'blueprint', atoms);
      if (ref && !out.has(ref.name)) out.set(ref.name, ref);
    }
  }
  return [...out.values()];
}

function refsForTask(task: ReviewTask): LeanRef[] {
  if (!task.files.atom) return [];
  const { atomsDir, edgesDir } = storeDirs(task.files.atom);
  const { atoms, edges } = loadIndex(atomsDir, edgesDir);
  const hash = path.basename(task.files.atom).replace(/\.md$/, '');
  return leanForAtom(hash, atoms, edges);
}

/** True if the task's statement has at least one linked Lean declaration. */
export function hasLeanFormalization(task: ReviewTask): boolean {
  return refsForTask(task).length > 0;
}

/** The declaration kind (definition/theorem/…) from a task atom's `sort` field. */
export function atomSort(atomPath: string | undefined): string | undefined {
  if (!atomPath) return undefined;
  try {
    const front = /^---\s*\n([\s\S]*?)\n---/.exec(readAtom(atomPath));
    if (!front) return undefined;
    const match = /^sort:\s*(.+)$/m.exec(front[1]);
    return match ? match[1].trim() : undefined;
  } catch {
    return undefined;
  }
}

/**
 * Annotate a leaf task with derived roadmap/review metadata: its declaration
 * kind, whether it is formalized, and a `lean_review` check when it is. Used by
 * both the live API and the static export so they stay identical.
 */
export function enrichLeafTask(task: ReviewTask): void {
  if (task.kind !== 'leaf' || !task.files.atom) return;
  task.sort = atomSort(task.files.atom);
  task.formalized = hasLeanFormalization(task);
  if (task.formalized) {
    task.checks = { ...(task.checks ?? {}), lean_review: task.checks?.lean_review ?? 'pending' };
  }
}

const DECL_BOUNDARY =
  /^(@\[|\/--|\/-!|theorem\b|lemma\b|def\b|abbrev\b|noncomputable\b|instance\b|structure\b|inductive\b|class\b|example\b|namespace\b|end\b|section\b|variable\b|open\b)/;

// Full declaration source (docstring + signature + body/proof) from OpenGALib.
function leanDeclSource(file: string, line: number): string | null {
  if (!file.endsWith('.lean') || file.includes('..')) return null;
  const abs = path.resolve(leanRoot, file);
  if (abs !== leanRoot && !abs.startsWith(leanRoot + path.sep)) return null;
  if (!fs.existsSync(abs)) return null;
  const lines = fs.readFileSync(abs, 'utf-8').split('\n');
  if (line < 1 || line > lines.length) return null;
  const sig = line - 1;

  let start = sig;
  while (start - 1 >= 0) {
    const prev = lines[start - 1].trim();
    if (prev === '') break;
    if (prev.endsWith('-/')) {
      let k = start - 1;
      while (k >= 0 && !lines[k].trim().startsWith('/-')) k--;
      if (k < 0) break;
      start = k;
      continue;
    }
    if (prev.startsWith('@[')) {
      start -= 1;
      continue;
    }
    break;
  }

  let cursor = start;
  if ((lines[cursor]?.trim() ?? '').startsWith('/-')) {
    while (cursor < lines.length && !lines[cursor].includes('-/')) cursor++;
    cursor++;
  }
  while (cursor < lines.length && lines[cursor].trim().startsWith('@[')) cursor++;

  let end = cursor + 1;
  while (end < lines.length && !DECL_BOUNDARY.test(lines[end])) end++;
  while (end > cursor + 1 && lines[end - 1].trim() === '') end--;
  return lines.slice(start, end).join('\n');
}

/** Lean declarations formalizing an atom task, as source-item cards. */
export function astrolabeLeanItems(task: ReviewTask): TaskSourceItem[] {
  return refsForTask(task).map((ref) => {
    const source = ref.file && ref.line ? leanDeclSource(ref.file, ref.line) : null;
    const location = ref.file ? `${ref.file}${ref.line ? `:${ref.line}` : ''}` : undefined;
    return {
      id: ref.name,
      title: ref.name,
      kind: 'lean' as const,
      language: 'lean',
      content: source ?? ref.signature ?? '',
      meta: [ref.state ?? 'lean', location, ref.via === 'blueprint' ? 'via blueprint' : undefined].filter(
        (item): item is string => Boolean(item)
      )
    };
  });
}
