import { useCallback, useEffect, useState } from 'react';
import { BrowserRouter, Route, Routes } from 'react-router-dom';
import { fetchTasks } from './api';
import styles from './App.module.css';
import { HomePage } from './pages/HomePage';
import { ReviewPage } from './pages/ReviewPage';

export default function App() {
  const [dataset, setDataset] = useState<Awaited<ReturnType<typeof fetchTasks>> | null>(null);
  const [error, setError] = useState<string | null>(null);

  const refreshDataset = useCallback(async () => {
    try {
      const data = await fetchTasks();
      setDataset(data);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
    }
  }, []);

  useEffect(() => {
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
        <p className={styles.emptyState} role="status">Loading roadmap…</p>
      </main>
    );
  }

  return (
    <BrowserRouter>
      <Routes>
        <Route path="/" element={<HomePage dataset={dataset} onRefresh={refreshDataset} />} />
        <Route
          path="/review/:taskId"
          element={<ReviewPage dataset={dataset} onRefresh={refreshDataset} />}
        />
      </Routes>
    </BrowserRouter>
  );
}
