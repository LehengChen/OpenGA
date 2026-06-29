import { useEffect, useState } from 'react';
import { BrowserRouter, Route, Routes } from 'react-router-dom';
import { fetchTasks } from './api';
import styles from './App.module.css';
import { HomePage } from './pages/HomePage';
import { ReviewPage } from './pages/ReviewPage';

export default function App() {
  const [dataset, setDataset] = useState<Awaited<ReturnType<typeof fetchTasks>> | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    fetchTasks()
      .then(setDataset)
      .catch((err) => setError(err.message));
  }, []);

  if (error) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState}>Failed to load tasks: {error}</p>
      </main>
    );
  }

  if (!dataset) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState}>Loading roadmap…</p>
      </main>
    );
  }

  return (
    <BrowserRouter>
      <Routes>
        <Route path="/" element={<HomePage dataset={dataset} />} />
        <Route path="/review/:taskId" element={<ReviewPage dataset={dataset} />} />
      </Routes>
    </BrowserRouter>
  );
}
