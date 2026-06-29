import express from 'express';
import {
  findTask,
  leafTasksInOrder,
  nextLeafId,
  prevLeafId,
  readAtom,
  readTasks,
  writeTasks
} from '../lib/taskStore.js';

const router = express.Router();

router.get('/', (_req, res) => {
  try {
    const dataset = readTasks();
    res.json(dataset);
  } catch (error) {
    res.status(500).json({ error: String(error) });
  }
});

router.get('/leaves', (_req, res) => {
  try {
    const dataset = readTasks();
    res.json(leafTasksInOrder(dataset.tasks));
  } catch (error) {
    res.status(500).json({ error: String(error) });
  }
});

router.get('/:id/atom', (req, res) => {
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
    res.status(500).json({ error: String(error) });
  }
});

router.post('/:id/review', express.json(), (req, res) => {
  try {
    const { mathReview, note } = req.body as { mathReview?: boolean; note?: string };

    if (!mathReview && (!note || note.trim().length === 0)) {
      res.status(400).json({ error: 'Either mathReview must be true or a note must be provided.' });
      return;
    }

    const dataset = readTasks();
    const taskIndex = dataset.tasks.findIndex((task) => task.id === req.params.id);
    if (taskIndex === -1) {
      res.status(404).json({ error: 'Task not found' });
      return;
    }

    const task = dataset.tasks[taskIndex];
    if (task.kind !== 'leaf') {
      res.status(400).json({ error: 'Only leaf tasks can be reviewed.' });
      return;
    }

    const updatedTask: typeof task = {
      ...task,
      checks: {
        ...(task.checks ?? {}),
        math_review: mathReview ? 'done' : 'pending'
      },
      review_notes: note?.trim() ? [...task.review_notes, note.trim()] : task.review_notes
    };

    dataset.tasks[taskIndex] = updatedTask;
    writeTasks(dataset);

    res.json({
      task: updatedTask,
      nextId: nextLeafId(dataset.tasks, task.id)
    });
  } catch (error) {
    res.status(500).json({ error: String(error) });
  }
});

router.get('/:id/neighbors', (req, res) => {
  try {
    const dataset = readTasks();
    res.json({
      prevId: prevLeafId(dataset.tasks, req.params.id),
      nextId: nextLeafId(dataset.tasks, req.params.id)
    });
  } catch (error) {
    res.status(500).json({ error: String(error) });
  }
});

export default router;
