import express from 'express';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import tasksRouter from './routes/tasks.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const app = express();
const PORT = process.env.PORT ?? 3001;

app.use(express.json());

app.use('/api/tasks', tasksRouter);

// In production, serve the built frontend statically.
const distPath = path.join(__dirname, '../dist');
app.use(express.static(distPath));
app.get(/.*/, (_req, res) => {
  res.sendFile(path.join(distPath, 'index.html'));
});

app.listen(PORT, () => {
  console.log(`Review API server listening on http://localhost:${PORT}`);
});
