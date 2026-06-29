export type TaskKind = 'root' | 'cluster' | 'leaf';
export type TaskStatus = 'todo' | 'in_progress' | 'review' | 'done';
export type TrustLevel = 'seed' | 'unreviewed' | 'reviewed' | 'verified' | 'formalization_ready';
export type TaskRole = 'math' | 'lean' | 'tooling' | 'maintainer';

export type TaskFiles = {
  atom?: string;
  chapter_doc?: string;
  rendered_doc?: string;
};

export type TaskTrust = {
  source: string;
  checks: Record<string, string>;
  notes: string[];
};

export type TaskReviews = {
  required: number;
  completed: number;
  ids: string[];
};

export type TaskGithub = {
  issue: string | null;
  pr: string | null;
  discussion: string | null;
};

export type ReviewTask = {
  id: string;
  kind: TaskKind;
  parent: string | null;
  depends_on: string[];
  unlocks: string[];
  dcref: string | null;
  chapter: number | null;
  title: string;
  description: string;
  why_it_matters: string;
  status: TaskStatus;
  trust_level: TrustLevel;
  next_role: TaskRole;
  difficulty: string;
  insight: string;
  formalization_risk: string;
  files: TaskFiles;
  editable: string[];
  trust: TaskTrust;
  reviews: TaskReviews;
  github: TaskGithub;
};

export type TaskDataset = {
  schema: string;
  project: string;
  tasks: ReviewTask[];
};

export const statusLabels: Record<TaskStatus, string> = {
  todo: 'Todo',
  in_progress: 'In progress',
  review: 'Review',
  done: 'Done'
};

export const trustLabels: Record<TrustLevel, string> = {
  seed: 'Seed',
  unreviewed: 'Unreviewed',
  reviewed: 'Reviewed',
  verified: 'Verified',
  formalization_ready: 'Formalization ready'
};

export const workflowOrder: TaskStatus[] = ['todo', 'in_progress', 'review', 'done'];
