import express, { type ErrorRequestHandler } from 'express';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import tasksRouter from './routes/tasks.js';
import { ValidationError } from './lib/errors.js';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const app = express();
const PORT = process.env.PORT ?? 3001;

function devCors(
  req: express.Request,
  res: express.Response,
  next: express.NextFunction
): void {
  if (process.env.NODE_ENV !== 'production') {
    const origin = req.headers.origin;
    if (origin && /^https?:\/\/localhost(?::\d+)?$/.test(origin)) {
      res.setHeader('Access-Control-Allow-Origin', origin);
      res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
      res.setHeader('Access-Control-Allow-Headers', 'Content-Type');
    }
    if (req.method === 'OPTIONS') {
      res.sendStatus(204);
      return;
    }
  }
  next();
}

app.use(devCors);
app.use(express.json());

app.use('/api/tasks', tasksRouter);

// In production, serve the built frontend statically.
const distPath = path.join(__dirname, '../dist');
app.use(express.static(distPath));
app.get(/.*/, (_req, res) => {
  res.sendFile(path.join(distPath, 'index.html'));
});

const errorHandler: ErrorRequestHandler = (err, _req, res, _next) => {
  if (err instanceof ValidationError) {
    res.status(400).json({ error: err.message });
    return;
  }
  if (err instanceof SyntaxError && 'body' in err) {
    res.status(400).json({ error: 'Invalid JSON' });
    return;
  }
  console.error(err);
  res.status(500).json({ error: 'Internal server error' });
};

app.use(errorHandler);

app.listen(PORT, () => {
  console.log(`Review API server listening on http://localhost:${PORT}`);
});
