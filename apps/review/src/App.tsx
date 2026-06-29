import { useMemo, useState } from 'react';
import styles from './App.module.css';
import { DagView } from './components/DagView';
import { ProgressPanel } from './components/ProgressPanel';
import { TaskDetail } from './components/TaskDetail';
import { TaskList } from './components/TaskList';
import pilotTasks from './data/pilot.tasks.json';
import { findTask, rootTasks } from './lib/progress';
import { TaskDataset } from './lib/taskSchema';

type ViewMode = 'list' | 'dag';

const dataset = pilotTasks as TaskDataset;

function initialTaskId() {
  const requested = new URLSearchParams(window.location.search).get('task');
  if (requested && findTask(dataset.tasks, requested)) {
    return requested;
  }

  return rootTasks(dataset.tasks)[0]?.id ?? dataset.tasks[0]?.id ?? '';
}

export default function App() {
  const [viewMode, setViewMode] = useState<ViewMode>('list');
  const [selectedId, setSelectedId] = useState(initialTaskId);

  const selectedTask = useMemo(() => {
    return findTask(dataset.tasks, selectedId) ?? rootTasks(dataset.tasks)[0] ?? dataset.tasks[0];
  }, [selectedId]);

  const setSelectedTask = (taskId: string) => {
    setSelectedId(taskId);
    const nextUrl = new URL(window.location.href);
    nextUrl.searchParams.set('task', taskId);
    window.history.replaceState(null, '', nextUrl);
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
            <TaskList tasks={dataset.tasks} selectedId={selectedId} onSelect={setSelectedTask} />
          ) : null}
          {viewMode === 'dag' ? (
            <DagView tasks={dataset.tasks} selectedId={selectedId} onSelect={setSelectedTask} />
          ) : null}
        </div>

        {selectedTask ? (
          <TaskDetail task={selectedTask} tasks={dataset.tasks} onSelect={setSelectedTask} />
        ) : null}
      </section>
    </main>
  );
}
