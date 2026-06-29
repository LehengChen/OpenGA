import type { ReviewTask, TaskDataset } from './lib/taskSchema';

const API_BASE = '/api';

export async function fetchTasks(): Promise<TaskDataset> {
  const res = await fetch(`${API_BASE}/tasks`);
  if (!res.ok) throw new Error(`Failed to fetch tasks: ${res.statusText}`);
  return res.json();
}

export async function fetchLeaves(): Promise<ReviewTask[]> {
  const res = await fetch(`${API_BASE}/tasks/leaves`);
  if (!res.ok) throw new Error(`Failed to fetch leaves: ${res.statusText}`);
  return res.json();
}

export async function fetchAtom(taskId: string): Promise<string> {
  const res = await fetch(`${API_BASE}/tasks/${encodeURIComponent(taskId)}/atom`);
  if (!res.ok) throw new Error(`Failed to fetch atom: ${res.statusText}`);
  return res.text();
}

export async function submitReview(
  taskId: string,
  payload: { mathReview: boolean; note: string; atomContent?: string }
): Promise<{ task: ReviewTask; nextId: string | null }> {
  const res = await fetch(`${API_BASE}/tasks/${encodeURIComponent(taskId)}/review`, {
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

export async function fetchNeighbors(taskId: string): Promise<{ prevId: string | null; nextId: string | null }> {
  const res = await fetch(`${API_BASE}/tasks/${encodeURIComponent(taskId)}/neighbors`);
  if (!res.ok) throw new Error(`Failed to fetch neighbors: ${res.statusText}`);
  return res.json();
}
