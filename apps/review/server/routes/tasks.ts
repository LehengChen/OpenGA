import express from 'express';
import {
  findTask,
  leafTasksInOrder,
  nextLeafId,
  prevLeafId,
  readAtom,
  readTasks,
  withTaskLock,
  writeAtom,
  writeTasks
} from '../lib/taskStore.js';
import { ValidationError } from '../lib/errors.js';
import type { ReviewTask } from '../../src/lib/taskSchema';

const router = express.Router();

router.get('/', (_req, res, next) => {
  try {
    const dataset = readTasks();
    res.json(dataset);
  } catch (error) {
    next(error);
  }
});

router.get('/leaves', (_req, res, next) => {
  try {
    const dataset = readTasks();
    res.json(leafTasksInOrder(dataset.tasks));
  } catch (error) {
    next(error);
  }
});

router.get('/:id/atom', (req, res, next) => {
  try {
    const dataset = readTasks();
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

const MAX_NOTE_LENGTH = 10000;

function validateReviewBody(body: unknown): {
  mathReview?: boolean;
  note?: string;
  atomContent?: string;
} {
  if (body === null || typeof body !== 'object') {
    throw new ValidationError('Request body must be an object');
  }

  const { mathReview, note, atomContent } = body as Record<string, unknown>;

  if (mathReview !== undefined && typeof mathReview !== 'boolean') {
    throw new ValidationError('mathReview must be a boolean');
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

  return { mathReview, note, atomContent };
}

router.post('/:id/review', express.json(), async (req, res, next) => {
  try {
    const { mathReview, note, atomContent } = validateReviewBody(req.body);
    const hasAtomEdit = atomContent !== undefined;
    const trimmedNote = note?.trim();

    const result = await withTaskLock(async () => {
      const dataset = readTasks();
      const taskIndex = dataset.tasks.findIndex((task) => task.id === req.params.id);
      if (taskIndex === -1) {
        return { status: 404, body: { error: 'Task not found' } };
      }

      const task = dataset.tasks[taskIndex];
      if (task.kind !== 'leaf') {
        return { status: 400, body: { error: 'Only leaf tasks can be reviewed.' } };
      }

      const currentMathReview = task.checks?.math_review ?? 'pending';
      const isRevert = mathReview === false && currentMathReview === 'done';
      const hasReview = mathReview === true || isRevert || (trimmedNote && trimmedNote.length > 0);

      if (!hasReview && !hasAtomEdit) {
        return {
          status: 400,
          body: {
            error: 'Please complete the math review, add a note, or edit the atom content.'
          }
        };
      }

      if (hasAtomEdit) {
        if (!task.files.atom) {
          return { status: 400, body: { error: 'No atom file available for this task.' } };
        }
        writeAtom(task.files.atom, atomContent);
      }

      const updatedTask: ReviewTask = {
        ...task,
        checks: {
          ...(task.checks ?? {}),
          math_review: mathReview ? 'done' : 'pending'
        },
        review_notes: trimmedNote ? [...task.review_notes, trimmedNote] : task.review_notes
      };

      dataset.tasks[taskIndex] = updatedTask;
      writeTasks(dataset);

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
    const dataset = readTasks();
    res.json({
      prevId: prevLeafId(dataset.tasks, req.params.id),
      nextId: nextLeafId(dataset.tasks, req.params.id)
    });
  } catch (error) {
    next(error);
  }
});

export default router;
