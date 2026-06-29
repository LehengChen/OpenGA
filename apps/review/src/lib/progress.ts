import { ReviewTask, workflowOrder } from './taskSchema';

const doneValues = new Set(['done', 'accepted', 'verified']);

export function rootTasks(tasks: ReviewTask[]) {
  return tasks.filter((task) => task.parent === null);
}

export function leafTasks(tasks: ReviewTask[]) {
  return tasks.filter((task) => task.kind === 'leaf');
}

export function childrenFor(tasks: ReviewTask[], parentId: string) {
  return tasks.filter((task) => task.parent === parentId);
}

export function findTask(tasks: ReviewTask[], taskId: string) {
  return tasks.find((task) => task.id === taskId);
}

export function dependentsFor(tasks: ReviewTask[], taskId: string) {
  return tasks.filter((task) => task.depends_on.includes(taskId));
}

export function leafDescendants(tasks: ReviewTask[], taskId: string): ReviewTask[] {
  const task = findTask(tasks, taskId);
  if (!task) return [];
  if (task.kind === 'leaf') return [task];

  const children = childrenFor(tasks, taskId);
  return children.flatMap((child) => leafDescendants(tasks, child.id));
}

export function taskProgress(tasks: ReviewTask[], taskId: string): number {
  const task = findTask(tasks, taskId);
  if (!task) return 0;

  if (task.kind === 'leaf') {
    const checks = Object.values(task.checks ?? {});
    if (checks.length === 0) return 0;
    const done = checks.filter((value) => doneValues.has(value)).length;
    return Math.round((done / checks.length) * 100);
  }

  const leaves = leafDescendants(tasks, taskId);
  if (leaves.length === 0) return 0;
  const sum = leaves.reduce((acc, leaf) => acc + taskProgress(tasks, leaf.id), 0);
  return Math.round(sum / leaves.length);
}

export function tasksDone(tasks: ReviewTask[], taskId: string): number {
  const leaves = leafDescendants(tasks, taskId);
  return leaves.filter((leaf) => taskProgress(tasks, leaf.id) === 100).length;
}

export function tasksTotal(tasks: ReviewTask[], taskId: string): number {
  return leafDescendants(tasks, taskId).length;
}

export function upstreamTasks(tasks: ReviewTask[], taskId: string): ReviewTask[] {
  const task = findTask(tasks, taskId);
  if (!task) return [];

  const upstreamIds = new Set<string>();
  if (task.parent) upstreamIds.add(task.parent);
  task.depends_on.forEach((id) => upstreamIds.add(id));
  tasks.forEach((t) => {
    if (t.unlocks.includes(taskId)) upstreamIds.add(t.id);
  });

  return Array.from(upstreamIds)
    .map((id) => findTask(tasks, id))
    .filter((t): t is ReviewTask => t !== undefined);
}

export type DagEdge = { from: string; to: string };

export function dagEdges(tasks: ReviewTask[]): DagEdge[] {
  const leafIds = new Set(leafTasks(tasks).map((t) => t.id));
  const edges: DagEdge[] = [];
  const seen = new Set<string>();

  for (const task of leafTasks(tasks)) {
    for (const depId of task.depends_on) {
      if (!leafIds.has(depId)) continue;
      const key = `${depId}->${task.id}`;
      if (!seen.has(key)) {
        seen.add(key);
        edges.push({ from: depId, to: task.id });
      }
    }
    for (const unlockedId of task.unlocks) {
      if (!leafIds.has(unlockedId)) continue;
      const key = `${task.id}->${unlockedId}`;
      if (!seen.has(key)) {
        seen.add(key);
        edges.push({ from: task.id, to: unlockedId });
      }
    }
  }

  return edges;
}

export function taskDepth(
  tasks: ReviewTask[],
  taskId: string,
  memo = new Map<string, number>()
): number {
  if (memo.has(taskId)) return memo.get(taskId)!;

  const task = findTask(tasks, taskId);
  if (!task) {
    memo.set(taskId, 0);
    return 0;
  }

  const upstreamIds = new Set<string>();
  task.depends_on.forEach((id) => upstreamIds.add(id));
  tasks.forEach((t) => {
    if (t.unlocks.includes(taskId)) upstreamIds.add(t.id);
  });

  const upstreamLeaves = Array.from(upstreamIds)
    .map((id) => findTask(tasks, id))
    .filter((t): t is ReviewTask => t !== undefined && t.kind === 'leaf');

  if (upstreamLeaves.length === 0) {
    memo.set(taskId, 0);
    return 0;
  }

  const depth = Math.max(...upstreamLeaves.map((up) => taskDepth(tasks, up.id, memo))) + 1;
  memo.set(taskId, depth);
  return depth;
}

export function roadmapMetrics(tasks: ReviewTask[]) {
  const leaves = leafTasks(tasks);
  const total = leaves.length || 1;
  const done = leaves.filter((leaf) => taskProgress(tasks, leaf.id) === 100).length;

  return {
    total,
    done,
    inReview: leaves.filter((leaf) => leaf.status === 'review').length,
    inProgress: leaves.filter((leaf) => leaf.status === 'in_progress').length,
    todo: leaves.filter((leaf) => leaf.status === 'todo').length
  };
}

export function statusCounts(tasks: ReviewTask[]) {
  return workflowOrder.map((status) => ({
    status,
    count: tasks.filter((task) => task.status === status).length
  }));
}
