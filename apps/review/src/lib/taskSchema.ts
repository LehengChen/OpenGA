export type TaskKind = 'root' | 'cluster' | 'leaf';
export type TaskStatus = 'todo' | 'in_progress' | 'review' | 'done';

export type TaskFiles = {
  atom?: string;
  chapter_doc?: string;
  rendered_doc?: string;
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
  status: TaskStatus;
  checks?: Record<string, string>;
  review_notes: string[];
  files: TaskFiles;
  editable: string[];
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

export const workflowOrder: TaskStatus[] = ['todo', 'in_progress', 'review', 'done'];
