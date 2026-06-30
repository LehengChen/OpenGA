import styles from '../App.module.css';
import { dependentsFor, findTask, leafDescendants, taskProgress, tasksDone, tasksTotal } from '../lib/progress';
import { ReviewTask, statusLabels } from '../lib/taskSchema';

type Props = {
  task: ReviewTask;
  tasks: ReviewTask[];
  onSelect: (taskId: string) => void;
  onReview?: (taskId: string) => void;
};

function checkLabel(key: string): string {
  return key
    .split('_')
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join(' ');
}

export function TaskDetail({ task, tasks, onSelect, onReview }: Props) {
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

      {!isGroup && task.checks && Object.keys(task.checks).length > 0 ? (
        <section className={styles.detailSection}>
          <div className={styles.sectionTitle}>Review checklist</div>
          <div className={styles.checklist}>
            {Object.entries(task.checks).map(([key, value]) => (
              <label key={key}>
                <input checked={value === 'done'} disabled readOnly type="checkbox" />
                <span>{checkLabel(key)}</span>
              </label>
            ))}
          </div>
          <p className={styles.detailSummary}>
            Open the task to review its declared source material and update the checklist.
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

      {!isGroup && onReview ? (
        <section className={styles.detailSection}>
          <button type="button" className={styles.primaryButton} onClick={() => onReview(task.id)}>
            Open review page
          </button>
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
                <button
                  key={dependencyId}
                  type="button"
                  onClick={() => onSelect(dependencyId)}
                  title={dependency ? `${dependencyId}: ${dependency.title}` : dependencyId}
                >
                  {dependencyId}
                  {dependency ? <small>{dependency.title}</small> : null}
                </button>
              );
            })}
            {dependents.map((dependent) => (
              <button
                key={dependent.id}
                type="button"
                onClick={() => onSelect(dependent.id)}
                title={`${dependent.id}: ${dependent.title}`}
              >
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
              <button
                key={leaf.id}
                type="button"
                onClick={() => onSelect(leaf.id)}
                title={`${leaf.id}: ${leaf.title}`}
              >
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
