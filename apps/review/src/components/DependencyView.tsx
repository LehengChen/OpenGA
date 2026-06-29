import styles from '../App.module.css';
import { findTask } from '../lib/progress';
import { ReviewTask } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

export function DependencyView({ tasks, selectedId, onSelect }: Props) {
  const edges = tasks.flatMap((task) =>
    task.depends_on.map((dependencyId) => ({
      from: dependencyId,
      to: task.id,
      fromTask: findTask(tasks, dependencyId),
      toTask: task
    }))
  );

  const independentTasks = tasks.filter((task) => task.depends_on.length === 0);

  return (
    <div className={styles.dependencyView}>
      <section className={styles.edgeSection}>
        <h2>Dependency edges</h2>
        {edges.length === 0 ? (
          <p className={styles.emptyState}>No dependencies declared.</p>
        ) : (
          <div className={styles.edgeList}>
            {edges.map((edge) => (
              <button
                className={`${styles.edgeRow} ${selectedId === edge.to ? styles.selectedEdge : ''}`}
                key={`${edge.from}-${edge.to}`}
                type="button"
                onClick={() => onSelect(edge.to)}
              >
                <span>
                  <strong>{edge.from}</strong>
                  <small>{edge.fromTask?.title ?? 'Missing task'}</small>
                </span>
                <span className={styles.edgeArrow}>to</span>
                <span>
                  <strong>{edge.to}</strong>
                  <small>{edge.toTask.title}</small>
                </span>
              </button>
            ))}
          </div>
        )}
      </section>

      <section className={styles.edgeSection}>
        <h2>Independent starts</h2>
        <div className={styles.independentList}>
          {independentTasks.map((task) => (
            <button
              className={`${styles.inlineTaskButton} ${
                selectedId === task.id ? styles.selectedInlineTask : ''
              }`}
              key={task.id}
              type="button"
              onClick={() => onSelect(task.id)}
            >
              {task.id}
            </button>
          ))}
        </div>
      </section>
    </div>
  );
}
