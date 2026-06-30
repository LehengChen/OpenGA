import type { ReviewProject, ReviewTask, TaskDataset, TaskSource } from './lib/taskSchema';

const API_BASE = '/api';

async function fetchWithTimeout(
  input: RequestInfo | URL,
  init?: RequestInit,
  timeoutMs = 8000
): Promise<Response> {
  const controller = new AbortController();
  const timeout = window.setTimeout(() => controller.abort(), timeoutMs);
  try {
    return await fetch(input, {
      ...init,
      signal: controller.signal
    });
  } finally {
    window.clearTimeout(timeout);
  }
}

function taskBase(projectId: string): string {
  return `${API_BASE}/projects/${encodeURIComponent(projectId)}/tasks`;
}

export async function fetchProjects(): Promise<ReviewProject[]> {
  const res = await fetchWithTimeout(`${API_BASE}/projects`);
  if (!res.ok) throw new Error(`Failed to fetch projects: ${res.statusText}`);
  return res.json();
}

export async function fetchTasks(projectId: string): Promise<TaskDataset> {
  const res = await fetchWithTimeout(taskBase(projectId));
  if (!res.ok) throw new Error(`Failed to fetch tasks: ${res.statusText}`);
  return res.json();
}

export async function fetchLeaves(projectId: string): Promise<ReviewTask[]> {
  const res = await fetchWithTimeout(`${taskBase(projectId)}/leaves`);
  if (!res.ok) throw new Error(`Failed to fetch leaves: ${res.statusText}`);
  return res.json();
}

export async function fetchAtom(projectId: string, taskId: string): Promise<string> {
  const res = await fetchWithTimeout(`${taskBase(projectId)}/${encodeURIComponent(taskId)}/atom`);
  if (!res.ok) throw new Error(`Failed to fetch atom: ${res.statusText}`);
  return res.text();
}

export async function fetchTaskSource(projectId: string, taskId: string): Promise<TaskSource> {
  const res = await fetchWithTimeout(
    `${taskBase(projectId)}/${encodeURIComponent(taskId)}/source`,
    undefined,
    60000
  );
  if (!res.ok) throw new Error(`Failed to fetch task source: ${res.statusText}`);
  return res.json();
}

export async function submitReview(
  projectId: string,
  taskId: string,
  payload: { checks: Record<string, boolean>; note: string; atomContent?: string }
): Promise<{ task: ReviewTask; nextId: string | null }> {
  const res = await fetchWithTimeout(`${taskBase(projectId)}/${encodeURIComponent(taskId)}/review`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload)
  });
  if (!res.ok) {
    const err = await res.json().catch(() => ({ error: res.statusText }));
    throw new Error(err.error ?? `Failed to submit review: ${res.statusText}`);
  }
  return res.json();
}

export async function fetchNeighbors(
  projectId: string,
  taskId: string
): Promise<{ prevId: string | null; nextId: string | null }> {
  const res = await fetchWithTimeout(`${taskBase(projectId)}/${encodeURIComponent(taskId)}/neighbors`);
  if (!res.ok) throw new Error(`Failed to fetch neighbors: ${res.statusText}`);
  return res.json();
}
