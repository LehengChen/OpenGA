import express from 'express';
import {
  findTask,
  leafTasksInOrder,
  nextLeafId,
  prevLeafId,
  readAtom,
  readTaskSource,
  readTasks,
  withTaskLock,
  writeAtom,
  writeTasks
} from '../lib/taskStore.js';
import { ValidationError } from '../lib/errors.js';
import { hasLeanFormalization } from '../lib/sources/docarmoLean.js';
import type { ReviewTask } from '../../src/lib/taskSchema';

const defaultProjectId = 'riemannian-geometry';
const router = express.Router({ mergeParams: true });

function projectIdFromRequest(req: express.Request): string {
  return typeof req.params.projectId === 'string' ? req.params.projectId : defaultProjectId;
}

// The declaration kind (definition/theorem/remark/…) of a leaf task, read from
// its atom's `sort` frontmatter field.
function atomSort(atomPath: string | undefined): string | undefined {
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

router.get('/', (req, res, next) => {
  try {
    const dataset = readTasks(projectIdFromRequest(req));
    for (const task of dataset.tasks) {
      if (task.kind === 'leaf' && task.files.atom) {
        task.sort = atomSort(task.files.atom);
        task.formalized = hasLeanFormalization(task);
        // Formalized statements get a second review check so the Lean can be
        // reviewed independently of the informal math. Seeded pending here so the
        // checkbox renders; the first review submit persists it.
        if (task.formalized) {
          task.checks = { ...(task.checks ?? {}), lean_review: task.checks?.lean_review ?? 'pending' };
        }
      }
    }
    res.json(dataset);
  } catch (error) {
    next(error);
  }
});

router.get('/leaves', (req, res, next) => {
  try {
    const dataset = readTasks(projectIdFromRequest(req));
    res.json(leafTasksInOrder(dataset.tasks));
  } catch (error) {
    next(error);
  }
});

router.get('/:id/atom', (req, res, next) => {
  try {
    const dataset = readTasks(projectIdFromRequest(req));
    const task = findTask(dataset.tasks, req.params.id);
    if (!task) {
      res.status(404).json({ error: 'Task not found' });
      return;
    }
    if (!task.files.atom) {
      res.status(404).json({ error: 'No atom file for this task' });
      return;
    }
    const content = readAtom(task.files.atom);
    res.type('text/markdown').send(content);
  } catch (error) {
    next(error);
  }
});

router.get('/:id/source', (req, res, next) => {
  try {
    const projectId = projectIdFromRequest(req);
    const dataset = readTasks(projectId);
    const task = findTask(dataset.tasks, req.params.id);
    if (!task) {
      res.status(404).json({ error: 'Task not found' });
      return;
    }
    res.json(readTaskSource(projectId, task));
  } catch (error) {
    next(error);
  }
});

const MAX_NOTE_LENGTH = 10000;

function validateReviewBody(body: unknown): {
  mathReview?: boolean;
  checks?: Record<string, boolean>;
  note?: string;
  atomContent?: string;
} {
  if (body === null || typeof body !== 'object') {
    throw new ValidationError('Request body must be an object');
  }

  const { mathReview, checks, note, atomContent } = body as Record<string, unknown>;

  if (mathReview !== undefined && typeof mathReview !== 'boolean') {
    throw new ValidationError('mathReview must be a boolean');
  }

  if (checks !== undefined) {
    if (checks === null || typeof checks !== 'object' || Array.isArray(checks)) {
      throw new ValidationError('checks must be an object');
    }
    for (const [key, value] of Object.entries(checks as Record<string, unknown>)) {
      if (!/^[a-z][a-z0-9_]*$/.test(key)) {
        throw new ValidationError(`Invalid check key: ${key}`);
      }
      if (typeof value !== 'boolean') {
        throw new ValidationError(`Check ${key} must be a boolean`);
      }
    }
  }

  if (note !== undefined) {
    if (typeof note !== 'string') {
      throw new ValidationError('note must be a string');
    }
    if (note.length > MAX_NOTE_LENGTH) {
      throw new ValidationError(`note must be at most ${MAX_NOTE_LENGTH} characters`);
    }
  }

  if (atomContent !== undefined && typeof atomContent !== 'string') {
    throw new ValidationError('atomContent must be a string');
  }

  return { mathReview, checks: checks as Record<string, boolean> | undefined, note, atomContent };
}

router.post('/:id/review', express.json(), async (req, res, next) => {
  try {
    const projectId = projectIdFromRequest(req);
    const { mathReview, checks, note, atomContent } = validateReviewBody(req.body);
    const hasAtomEdit = atomContent !== undefined;
    const trimmedNote = note?.trim();

    const result = await withTaskLock(async () => {
      const dataset = readTasks(projectId);
      const taskIndex = dataset.tasks.findIndex((task) => task.id === req.params.id);
      if (taskIndex === -1) {
        return { status: 404, body: { error: 'Task not found' } };
      }

      const task = dataset.tasks[taskIndex];
      if (task.kind !== 'leaf') {
        return { status: 400, body: { error: 'Only leaf tasks can be reviewed.' } };
      }

      const checkUpdates: Record<string, boolean> = {
        ...(checks ?? {})
      };
      if (mathReview !== undefined) {
        checkUpdates.math_review = mathReview;
      }

      const hasCheckUpdate = Object.entries(checkUpdates).some(([key, value]) => {
        const currentValue = task.checks?.[key] ?? 'pending';
        return (value && currentValue !== 'done') || (!value && currentValue === 'done');
      });
      const hasReview = hasCheckUpdate || (trimmedNote && trimmedNote.length > 0);

      if (!hasReview && !hasAtomEdit) {
        return {
          status: 400,
          body: {
            error: 'Please update a review check, add a note, or edit the atom content.'
          }
        };
      }

      if (hasAtomEdit) {
        if (!task.files.atom) {
          return { status: 400, body: { error: 'No atom file available for this task.' } };
        }
        if (!task.editable.includes(task.files.atom)) {
          return { status: 400, body: { error: 'This task does not allow atom source edits.' } };
        }
        writeAtom(task.files.atom, atomContent);
      }

      const nextChecks = {
        ...(task.checks ?? {})
      };
      for (const [key, value] of Object.entries(checkUpdates)) {
        nextChecks[key] = value ? 'done' : 'pending';
      }

      const updatedTask: ReviewTask = {
        ...task,
        checks: nextChecks,
        review_notes: trimmedNote ? [...task.review_notes, trimmedNote] : task.review_notes
      };

      dataset.tasks[taskIndex] = updatedTask;
      writeTasks(projectId, dataset);

      return {
        status: 200,
        body: {
          task: updatedTask,
          nextId: nextLeafId(dataset.tasks, task.id)
        }
      };
    });

    res.status(result.status).json(result.body);
  } catch (error) {
    next(error);
  }
});

router.get('/:id/neighbors', (req, res, next) => {
  try {
    const dataset = readTasks(projectIdFromRequest(req));
    res.json({
      prevId: prevLeafId(dataset.tasks, req.params.id),
      nextId: nextLeafId(dataset.tasks, req.params.id)
    });
  } catch (error) {
    next(error);
  }
});

export default router;
