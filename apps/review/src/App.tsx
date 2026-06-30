import { lazy, Suspense, useCallback, useEffect, useState } from 'react';
import { BrowserRouter, Navigate, Route, Routes, useParams } from 'react-router-dom';
import { fetchProjects, fetchTasks } from './api';
import styles from './App.module.css';
import { ProjectIndexPage } from './pages/ProjectIndexPage';
import type { ReviewProject, TaskDataset } from './lib/taskSchema';

const HomePage = lazy(() =>
  import('./pages/HomePage').then((module) => ({ default: module.HomePage }))
);
const ReviewPage = lazy(() =>
  import('./pages/ReviewPage').then((module) => ({ default: module.ReviewPage }))
);

function RouteFallback({ label }: { label: string }) {
  return (
    <main className={styles.appShell}>
      <p className={styles.emptyState} role="status">{label}</p>
    </main>
  );
}

function DatasetRoute({ mode }: { mode: 'home' | 'review' }) {
  const { projectId } = useParams<{ projectId: string }>();
  const resolvedProjectId = projectId ?? 'riemannian-geometry';
  const [dataset, setDataset] = useState<TaskDataset | null>(null);
  const [error, setError] = useState<string | null>(null);

  const refreshDataset = useCallback(async () => {
    try {
      const data = await fetchTasks(resolvedProjectId);
      setDataset(data);
      setError(null);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
    }
  }, [resolvedProjectId]);

  useEffect(() => {
    setDataset(null);
    refreshDataset();
  }, [refreshDataset]);

  if (error) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState} role="alert">Failed to load tasks: {error}</p>
      </main>
    );
  }

  if (!dataset) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState} role="status">Loading project…</p>
      </main>
    );
  }

  if (mode === 'review') {
    return (
      <Suspense fallback={<RouteFallback label="Loading review page…" />}>
        <ReviewPage
          projectId={resolvedProjectId}
          dataset={dataset}
          onRefresh={refreshDataset}
        />
      </Suspense>
    );
  }

  return (
    <Suspense fallback={<RouteFallback label="Loading project page…" />}>
      <HomePage
        projectId={resolvedProjectId}
        dataset={dataset}
        onRefresh={refreshDataset}
      />
    </Suspense>
  );
}

export default function App() {
  const [projects, setProjects] = useState<ReviewProject[] | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    fetchProjects()
      .then((data) => {
        setProjects(data);
        setError(null);
      })
      .catch((err) => setError(err instanceof Error ? err.message : String(err)));
  }, []);

  if (error) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState} role="alert">Failed to load projects: {error}</p>
      </main>
    );
  }

  if (!projects) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState} role="status">Loading projects…</p>
      </main>
    );
  }

  return (
    <BrowserRouter>
      <Routes>
        <Route path="/" element={<ProjectIndexPage projects={projects} />} />
        <Route path="/projects/:projectId" element={<DatasetRoute mode="home" />} />
        <Route path="/projects/:projectId/review/:taskId" element={<DatasetRoute mode="review" />} />
        <Route path="/review/:taskId" element={<Navigate to="/projects/riemannian-geometry" replace />} />
      </Routes>
    </BrowserRouter>
  );
}
