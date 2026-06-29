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
};

function initialTaskId(tasks: TaskDataset['tasks']) {
  const requested = new URLSearchParams(window.location.search).get('task');
  if (requested && findTask(tasks, requested)) {
    return requested;
  }
  return rootTasks(tasks)[0]?.id ?? tasks[0]?.id ?? '';
}

export function HomePage({ dataset }: Props) {
  const navigate = useNavigate();
  const [viewMode, setViewMode] = useState<ViewMode>('list');
  const [selectedId, setSelectedId] = useState(() => initialTaskId(dataset.tasks));

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
        </div>
        <ProgressPanel tasks={dataset.tasks} />
      </header>

      <nav className={styles.tabs} aria-label="Task views">
        <button
          className={viewMode === 'list' ? styles.activeTab : ''}
          type="button"
          onClick={() => setViewMode('list')}
        >
          List
        </button>
        <button
          className={viewMode === 'dag' ? styles.activeTab : ''}
          type="button"
          onClick={() => setViewMode('dag')}
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
              onReview={startReview}
            />
          ) : null}
          {viewMode === 'dag' ? (
            <DagView tasks={dataset.tasks} selectedId={selectedId} onSelect={startReview} />
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
