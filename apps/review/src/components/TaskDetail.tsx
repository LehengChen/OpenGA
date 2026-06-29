import styles from '../App.module.css';
import { dependentsFor, findTask, leafDescendants, taskProgress, tasksDone, tasksTotal } from '../lib/progress';
import { ReviewTask, statusLabels } from '../lib/taskSchema';

type Props = {
  task: ReviewTask;
  tasks: ReviewTask[];
  onSelect: (taskId: string) => void;
};

export function TaskDetail({ task, tasks, onSelect }: Props) {
  const dependents = dependentsFor(tasks, task.id);
  const fileEntries = Object.entries(task.files).filter(([, value]) => Boolean(value));
  const isGroup = task.kind !== 'leaf';
  const progress = taskProgress(tasks, task.id);
  const done = tasksDone(tasks, task.id);
  const total = tasksTotal(tasks, task.id);
  const leaves = leafDescendants(tasks, task.id);

  return (
    <aside className={styles.detailPanel}>
      <div className={styles.detailHeader}>
        <span className={styles.statusBadge}>{statusLabels[task.status]}</span>
        <span className={styles.cardMeta}>{task.kind}</span>
      </div>

      <h1>{task.title}</h1>
      <p className={styles.detailSummary}>{task.description}</p>

      {isGroup ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Progress</div>
          <div className={styles.progressRow}>
            <div className={styles.meter} aria-label={`${progress}% complete`}>
              <span style={{ width: `${progress}%` }} />
            </div>
            <strong>{progress}%</strong>
          </div>
          <p className={styles.detailSummary}>{done} of {total} leaf tasks done.</p>
        </section>
      ) : null}

      {!isGroup && task.checks?.math_review ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Review checklist</div>
          <div className={styles.checklist}>
            <label>
              <input checked={task.checks.math_review === 'done'} disabled readOnly type="checkbox" />
              <span>Math review</span>
            </label>
          </div>
          <p className={styles.detailSummary}>
            Read the atom and verify the mathematical statement and proof are correct.
          </p>
        </section>
      ) : null}

      {!isGroup && fileEntries.length > 0 ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Files</div>
          <div className={styles.fileList}>
            {fileEntries.map(([kind, path]) => (
              <code key={kind}>{path}</code>
            ))}
          </div>
        </section>
      ) : null}

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Dependencies</div>
        {task.depends_on.length === 0 && dependents.length === 0 ? (
          <p className={styles.emptyState}>No dependencies.</p>
        ) : (
          <div className={styles.linkList}>
            {task.depends_on.map((dependencyId) => {
              const dependency = findTask(tasks, dependencyId);
              return (
                <button key={dependencyId} type="button" onClick={() => onSelect(dependencyId)}>
                  {dependencyId}
                  {dependency ? <small>{dependency.title}</small> : null}
                </button>
              );
            })}
            {dependents.map((dependent) => (
              <button key={dependent.id} type="button" onClick={() => onSelect(dependent.id)}>
                {dependent.id}
                <small>{dependent.title}</small>
              </button>
            ))}
          </div>
        )}
      </section>

      {isGroup && leaves.length > 0 ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Leaf tasks</div>
          <div className={styles.linkList}>
            {leaves.map((leaf) => (
              <button key={leaf.id} type="button" onClick={() => onSelect(leaf.id)}>
                {leaf.id}
                <small>{leaf.title}</small>
              </button>
            ))}
          </div>
        </section>
      ) : null}

      {task.review_notes.length > 0 ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Review notes</div>
          <ul className={styles.detailList}>
            {task.review_notes.map((note, index) => (
              <li key={index}>{note}</li>
            ))}
          </ul>
        </section>
      ) : null}
    </aside>
  );
}
