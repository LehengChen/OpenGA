import { useMemo, useState } from 'react';

import { useNavigate } from 'react-router-dom';
import styles from '../App.module.css';
import { DagView } from '../components/DagView';
import { ProgressPanel } from '../components/ProgressPanel';
import { TaskDetail } from '../components/TaskDetail';
import { TaskList } from '../components/TaskList';
import { findTask, rootTasks } from '../lib/progress';
import type { TaskDataset } from '../lib/taskSchema';

type ViewMode = 'list' | 'dag';

type Props = {
  dataset: TaskDataset;
  onRefresh: () => Promise<void>;
};

function initialTaskId(tasks: TaskDataset['tasks']) {
  const requested = new URLSearchParams(window.location.search).get('task');
  if (requested && findTask(tasks, requested)) {
    return requested;
  }
  return rootTasks(tasks)[0]?.id ?? tasks[0]?.id ?? '';
}

export function HomePage({ dataset, onRefresh }: Props) {
  const navigate = useNavigate();
  const [viewMode, setViewMode] = useState<ViewMode>('list');
  const [selectedId, setSelectedId] = useState(() => initialTaskId(dataset.tasks));
  const [refreshing, setRefreshing] = useState(false);
  const [refreshError, setRefreshError] = useState<string | null>(null);

  const selectedTask = useMemo(() => {
    return findTask(dataset.tasks, selectedId) ?? rootTasks(dataset.tasks)[0] ?? dataset.tasks[0];
  }, [selectedId, dataset.tasks]);

  const setSelectedTask = (taskId: string) => {
    setSelectedId(taskId);
  };

  const startReview = (taskId: string) => {
    navigate(`/review/${encodeURIComponent(taskId)}`);
  };

  return (
    <main className={styles.appShell}>
      <header className={styles.header}>
        <div>
          <p className={styles.kicker}>OpenGA Review</p>
          <h1>Riemannian Geometry Review Roadmap</h1>
          <p className={styles.sourceLine}>
            Pilot roadmap from <code>projects/riemannian-geometry/tasks/pilot.tasks.yaml</code>
          </p>
          <button
            type="button"
            className={styles.refreshButton}
            onClick={async () => {
              setRefreshError(null);
              setRefreshing(true);
              try {
                await onRefresh();
              } catch (err) {
                setRefreshError(err instanceof Error ? err.message : String(err));
              } finally {
                setRefreshing(false);
              }
            }}
            disabled={refreshing}
            aria-busy={refreshing}
          >
            {refreshing ? 'Refreshing…' : 'Refresh roadmap'}
          </button>
          {refreshError ? <p className={styles.errorText}>{refreshError}</p> : null}
        </div>
        <ProgressPanel tasks={dataset.tasks} />
      </header>

      <nav className={styles.tabs} aria-label="Task views">
        <button
          className={viewMode === 'list' ? styles.activeTab : ''}
          type="button"
          onClick={() => setViewMode('list')}
          aria-pressed={viewMode === 'list'}
        >
          List
        </button>
        <button
          className={viewMode === 'dag' ? styles.activeTab : ''}
          type="button"
          onClick={() => setViewMode('dag')}
          aria-pressed={viewMode === 'dag'}
        >
          DAG
        </button>
      </nav>

      <section className={styles.contentGrid}>
        <div className={styles.workPanel}>
          {viewMode === 'list' ? (
            <TaskList
              tasks={dataset.tasks}
              selectedId={selectedId}
              onSelect={setSelectedTask}
            />
          ) : null}
          {viewMode === 'dag' ? (
            <DagView tasks={dataset.tasks} selectedId={selectedId} onSelect={setSelectedTask} />
          ) : null}
        </div>

        {selectedTask ? (
          <TaskDetail
            task={selectedTask}
            tasks={dataset.tasks}
            onSelect={setSelectedTask}
            onReview={startReview}
          />
        ) : null}
      </section>
    </main>
  );
}
