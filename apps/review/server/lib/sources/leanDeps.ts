import fs from 'node:fs';
import path from 'node:path';
import { projectRoot } from '../taskStore/paths.js';
import type { LeanDependencyNode } from '../../../src/lib/taskSchema';
import type { LeanDeclaration } from './types.js';

type RawNode = Omit<LeanDependencyNode, 'children' | 'truncated' | 'repeated'>;

type RawEdge = {
  from: string;
  to: string;
  fromName?: string;
  toName?: string;
  kind?: string;
};

type Graph = {
  nodes: Map<string, RawNode>;
  outgoing: Map<string, string[]>;
  idsByFileAndName: Map<string, string[]>;
  idsByName: Map<string, string[]>;
};

type TreeOptions = {
  depth: number;
  maxChildren: number;
  maxNodes: number;
};

const depsDir = path.join(projectRoot, 'projects/smooth-manifolds-lee/lean-deps');
const graphCache = new Map<string, Graph | null>();
const mathlibRoot = path.join(projectRoot, '.lake/packages/mathlib');
let mathlibRevision: string | null | undefined;
const textFileCache = new Map<string, string | null>();
const docCache = new Map<string, string | undefined>();
const declarationLineCache = new Map<string, number | undefined>();

function readJsonl<T>(filePath: string): T[] {
  if (!fs.existsSync(filePath)) return [];
  const content = fs.readFileSync(filePath, 'utf-8').trim();
  if (!content) return [];
  return content.split(/\n+/).map((line) => JSON.parse(line) as T);
}

function pushMap(map: Map<string, string[]>, key: string, value: string): void {
  const values = map.get(key);
  if (values) {
    if (!values.includes(value)) values.push(value);
  } else {
    map.set(key, [value]);
  }
}

function fileNameKey(file: string, name: string): string {
  return `${file}:${name}`;
}

function shortName(name: string): string {
  return name.split('.').at(-1) ?? name;
}

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function containsLeanIdentifier(text: string, name: string): boolean {
  if (!name) return false;
  const pattern = new RegExp(`(^|[^A-Za-z0-9_'.])${escapeRegExp(name)}([^A-Za-z0-9_'.]|$)`);
  return pattern.test(text);
}

function aliasesFor(name: string): string[] {
  switch (name) {
    case 'Nat':
      return ['ℕ'];
    case 'Int':
      return ['ℤ'];
    case 'Rat':
      return ['ℚ'];
    case 'Real':
      return ['ℝ'];
    case 'NNReal':
      return ['ℝ≥0'];
    case 'ENNReal':
      return ['ℝ≥0∞'];
    default:
      return [];
  }
}

function shouldShowDependency(parent: RawNode, child: RawNode): boolean {
  if (child.source !== 'mathlib') return true;
  const candidateNames = [child.name, shortName(child.name), ...aliasesFor(child.name)];
  return candidateNames.some((name) => parent.type.includes(name) || containsLeanIdentifier(parent.type, name));
}

function mathlibModulePath(moduleName: string): string | null {
  if (!moduleName.startsWith('Mathlib.')) return null;
  return `${moduleName.split('.').join('/')}.lean`;
}

function readTextFile(filePath: string): string | null {
  if (textFileCache.has(filePath)) return textFileCache.get(filePath) ?? null;
  const content = fs.existsSync(filePath) ? fs.readFileSync(filePath, 'utf-8') : null;
  textFileCache.set(filePath, content);
  return content;
}

function getMathlibRevision(): string {
  if (mathlibRevision !== undefined) return mathlibRevision ?? 'master';
  try {
    const manifest = JSON.parse(fs.readFileSync(path.join(projectRoot, 'lake-manifest.json'), 'utf-8'));
    mathlibRevision =
      manifest.packages?.find((item: { name?: string }) => item.name === 'mathlib')?.rev ?? 'master';
  } catch {
    mathlibRevision = 'master';
  }
  return mathlibRevision ?? 'master';
}

function normalizeDocstring(text: string): string {
  return text
    .replace(/^\/--\s?/, '')
    .replace(/\s*-\/\s*$/, '')
    .replace(/^\s*\*\s?/gm, '')
    .trim();
}

function docstringBeforeLine(source: string, line: number | undefined): string | undefined {
  if (!line || line <= 0) return undefined;
  const lines = source.split(/\r?\n/);
  const end = Math.min(lines.length - 1, line - 1);
  const start = Math.max(0, end - 80);

  for (let i = end; i >= start; i -= 1) {
    if (!lines[i].includes('/--')) continue;
    const block: string[] = [];
    for (let j = i; j < Math.min(lines.length, end + 30); j += 1) {
      block.push(lines[j]);
      if (lines[j].includes('-/')) {
        return normalizeDocstring(block.join('\n')) || undefined;
      }
    }
  }
  return undefined;
}

function declarationLineForName(source: string, node: RawNode): number | undefined {
  const lines = source.split(/\r?\n/);
  const short = shortName(node.name);
  const keyword = '\\b(?:abbrev|axiom|class|def|inductive|instance|lemma|opaque|structure|theorem)\\s+';
  const boundary = '(?=[\\s:{(]|$)';
  const patterns = [
    new RegExp(`${keyword}(?:_root_\\.)?${escapeRegExp(node.name)}${boundary}`),
    new RegExp(`${keyword}(?:_root_\\.)?${escapeRegExp(short)}${boundary}`)
  ];
  const matches = lines
    .map((line, index) => ({ line, index }))
    .filter(({ line }) => patterns.some((pattern) => pattern.test(line)));
  if (!matches.length) return undefined;
  const hintedLine = node.line ?? 1;
  return (
    matches.sort(
      (left, right) => Math.abs(left.index + 1 - hintedLine) - Math.abs(right.index + 1 - hintedLine)
    )[0].index + 1
  );
}

function mathlibDeclarationLine(node: RawNode): number | undefined {
  if (node.source !== 'mathlib') return undefined;
  if (declarationLineCache.has(node.id)) return declarationLineCache.get(node.id);
  const modulePath = mathlibModulePath(node.module);
  const source = modulePath ? readTextFile(path.join(mathlibRoot, modulePath)) : null;
  const line = source ? declarationLineForName(source, node) ?? node.line : node.line;
  declarationLineCache.set(node.id, line);
  return line;
}

function mathlibDoc(node: RawNode): string | undefined {
  if (node.source !== 'mathlib') return undefined;
  if (docCache.has(node.id)) return docCache.get(node.id);
  const modulePath = mathlibModulePath(node.module);
  const source = modulePath ? readTextFile(path.join(mathlibRoot, modulePath)) : null;
  const doc = source ? docstringBeforeLine(source, mathlibDeclarationLine(node)) : undefined;
  docCache.set(node.id, doc);
  return doc;
}

function mathlibUrls(node: RawNode): Pick<LeanDependencyNode, 'docsUrl' | 'sourceUrl'> {
  if (node.source !== 'mathlib') return {};
  const modulePath = mathlibModulePath(node.module);
  if (!modulePath) return {};
  const docsPath = modulePath.replace(/\.lean$/, '.html');
  const line = mathlibDeclarationLine(node);
  const sourceLine = line && line > 0 ? `#L${line}` : '';
  return {
    docsUrl: `https://leanprover-community.github.io/mathlib4_docs/${docsPath}#${encodeURIComponent(node.name)}`,
    sourceUrl: `https://github.com/leanprover-community/mathlib4/blob/${getMathlibRevision()}/${modulePath}${sourceLine}`
  };
}

function enrichNode(node: RawNode): LeanDependencyNode {
  return {
    ...node,
    doc: mathlibDoc(node),
    ...mathlibUrls(node)
  };
}

function sortNodeIds(nodes: Map<string, RawNode>, ids: string[]): string[] {
  return [...new Set(ids)].sort((left, right) => {
    const a = nodes.get(left);
    const b = nodes.get(right);
    if (!a || !b) return left.localeCompare(right);
    if (a.source !== b.source) {
      if (a.source === 'lee') return -1;
      if (b.source === 'lee') return 1;
    }
    return a.name.localeCompare(b.name);
  });
}

function loadGraph(projectId: string): Graph | null {
  if (projectId !== 'smooth-manifolds-lee') return null;
  if (graphCache.has(projectId)) return graphCache.get(projectId) ?? null;

  const nodePath = path.join(depsDir, 'nodes.jsonl');
  const edgePath = path.join(depsDir, 'edges.jsonl');
  if (!fs.existsSync(nodePath) || !fs.existsSync(edgePath)) {
    graphCache.set(projectId, null);
    return null;
  }

  const nodes = new Map<string, RawNode>();
  for (const node of readJsonl<RawNode>(nodePath)) {
    nodes.set(node.id, node);
  }

  const outgoing = new Map<string, string[]>();
  for (const edge of readJsonl<RawEdge>(edgePath)) {
    if (!nodes.has(edge.from) || !nodes.has(edge.to)) continue;
    pushMap(outgoing, edge.from, edge.to);
  }
  for (const [id, values] of outgoing) {
    outgoing.set(id, sortNodeIds(nodes, values));
  }

  const idsByFileAndName = new Map<string, string[]>();
  const idsByName = new Map<string, string[]>();
  for (const node of nodes.values()) {
    pushMap(idsByName, node.name, node.id);
    pushMap(idsByName, shortName(node.name), node.id);
    if (node.file) {
      pushMap(idsByFileAndName, fileNameKey(node.file, node.name), node.id);
      pushMap(idsByFileAndName, fileNameKey(node.file, shortName(node.name)), node.id);
    }
  }

  const graph = { nodes, outgoing, idsByFileAndName, idsByName };
  graphCache.set(projectId, graph);
  return graph;
}

function resolveRootIds(graph: Graph, decl: LeanDeclaration): string[] {
  const ids = new Set<string>();
  if (decl.sourceFile) {
    for (const name of [decl.fullName, decl.name]) {
      for (const id of graph.idsByFileAndName.get(fileNameKey(decl.sourceFile, name)) ?? []) {
        ids.add(id);
      }
    }
  }
  if (ids.size === 0 && (decl.kind === 'check' || decl.kind === 'recall')) {
    for (const name of [decl.fullName, decl.name]) {
      for (const id of graph.idsByName.get(name) ?? []) ids.add(id);
    }
  }
  return sortNodeIds(graph.nodes, [...ids]).slice(0, 3);
}

function buildTree(
  graph: Graph,
  id: string,
  options: TreeOptions,
  seen: Set<string>,
  counter: { value: number }
): LeanDependencyNode | null {
  const node = graph.nodes.get(id);
  if (!node) return null;
  if (counter.value >= options.maxNodes) {
    return { ...enrichNode(node), truncated: true, children: [] };
  }
  counter.value += 1;

  if (seen.has(id)) {
    return { ...enrichNode(node), repeated: true, children: [] };
  }
  if (options.depth <= 0) {
    return { ...enrichNode(node), children: [] };
  }

  const nextSeen = new Set(seen);
  nextSeen.add(id);
  const childIds = (graph.outgoing.get(id) ?? []).filter((childId) => {
    const child = graph.nodes.get(childId);
    return child ? shouldShowDependency(node, child) : false;
  });
  const children: LeanDependencyNode[] = [];
  let truncated = false;

  for (const childId of childIds) {
    if (children.length >= options.maxChildren || counter.value >= options.maxNodes) {
      truncated = true;
      break;
    }
    const child = buildTree(
      graph,
      childId,
      { ...options, depth: options.depth - 1 },
      nextSeen,
      counter
    );
    if (child) children.push(child);
  }

  return { ...enrichNode(node), truncated, children };
}

export function dependencyTreesForDeclaration(
  projectId: string,
  decl: LeanDeclaration
): LeanDependencyNode[] {
  const graph = loadGraph(projectId);
  if (!graph) return [];

  const roots = resolveRootIds(graph, decl);
  const counter = { value: 0 };
  return roots
    .map((id) =>
      buildTree(
        graph,
        id,
        { depth: 2, maxChildren: 24, maxNodes: 120 },
        new Set(),
        counter
      )
    )
    .filter((node): node is LeanDependencyNode => node !== null);
}
