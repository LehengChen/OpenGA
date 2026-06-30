export type TaskKind = 'root' | 'cluster' | 'leaf';
export type TaskStatus = 'todo' | 'in_progress' | 'review' | 'done';
export type ReviewKind = 'atom_math' | 'lean_textbook';

export type TaskFiles = {
  atom?: string;
  chapter_doc?: string;
  rendered_doc?: string;
  lean_source?: string;
  textbook_json?: string;
};

export type TaskGithub = {
  issue: string | null;
  pr: string | null;
  discussion: string | null;
};

export type TaskSourceRef = {
  textbook_json?: string;
  textbook_label?: string;
  import_ref?: string;
  lean_file?: string;
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
  review_kind?: ReviewKind;
  source?: TaskSourceRef;
};

export type TaskDataset = {
  schema: string;
  project: string;
  title?: string;
  description?: string;
  review_kind?: ReviewKind;
  tasks: ReviewTask[];
};

export type ReviewProject = {
  id: string;
  title: string;
  description: string;
  taskPath: string;
  reviewKind: ReviewKind;
};

export type TaskSourcePanel = {
  id: string;
  title: string;
  kind: 'markdown' | 'lean' | 'text';
  language?: string;
  content: string;
  items?: TaskSourceItem[];
  editable: boolean;
};

export type TaskSourceItem = {
  id: string;
  title: string;
  kind: 'markdown' | 'lean' | 'text';
  language?: string;
  content: string;
  meta?: string[];
  description?: string;
};

export type TaskSource = {
  taskId: string;
  panels: TaskSourcePanel[];
};

export const statusLabels: Record<TaskStatus, string> = {
  todo: 'Todo',
  in_progress: 'In progress',
  review: 'Review',
  done: 'Done'
};

export const workflowOrder: TaskStatus[] = ['todo', 'in_progress', 'review', 'done'];
