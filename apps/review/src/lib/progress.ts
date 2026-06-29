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

export function taskProgress(task: ReviewTask) {
  const checks = Object.values(task.trust.checks);
  const checkCount = checks.length;
  const completedChecks = checks.filter((value) => doneValues.has(value)).length;
  const reviewRequired = task.reviews.required;
  const reviewCompleted = Math.min(task.reviews.completed, reviewRequired);
  const total = checkCount + reviewRequired;

  if (total === 0) {
    return task.kind === 'root' || task.kind === 'cluster' ? 0 : 100;
  }

  return Math.round(((completedChecks + reviewCompleted) / total) * 100);
}

export function roadmapMetrics(tasks: ReviewTask[]) {
  const leaves = leafTasks(tasks);
  const total = leaves.length || 1;

  const reviewed = leaves.filter((task) => task.reviews.completed >= task.reviews.required).length;
  const mathTrusted = leaves.filter((task) => doneValues.has(task.trust.checks.math)).length;
  const textTrusted = leaves.filter((task) => doneValues.has(task.trust.checks.transcription)).length;
  const crossRefsTrusted = leaves.filter((task) => doneValues.has(task.trust.checks.cross_refs)).length;
  const verified = leaves.filter((task) =>
    task.trust_level === 'verified' || task.trust_level === 'formalization_ready'
  ).length;

  const metrics = [
    { key: 'reviews', label: 'Reviews recorded', completed: reviewed, total },
    { key: 'text', label: 'Text trusted', completed: textTrusted, total },
    { key: 'math', label: 'Math semantics trusted', completed: mathTrusted, total },
    { key: 'refs', label: 'Cross refs trusted', completed: crossRefsTrusted, total },
    { key: 'verified', label: 'Verified cards', completed: verified, total }
  ].map((metric) => ({
    ...metric,
    percent: Math.round((metric.completed / metric.total) * 100)
  }));

  const overall = Math.round(
    metrics.reduce((sum, metric) => sum + metric.percent, 0) / metrics.length
  );

  return { metrics, overall };
}

export function statusCounts(tasks: ReviewTask[]) {
  return workflowOrder.map((status) => ({
    status,
    count: tasks.filter((task) => task.status === status).length
  }));
}

export function trustCounts(tasks: ReviewTask[]) {
  const counts = new Map<string, number>();
  for (const task of tasks) {
    counts.set(task.trust_level, (counts.get(task.trust_level) ?? 0) + 1);
  }
  return Array.from(counts, ([trust, count]) => ({ trust, count }));
}
