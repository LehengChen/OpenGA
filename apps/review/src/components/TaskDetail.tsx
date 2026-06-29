import styles from '../App.module.css';
import { dependentsFor, findTask, taskProgress } from '../lib/progress';
import { ReviewTask, statusLabels, trustLabels } from '../lib/taskSchema';

type Props = {
  task: ReviewTask;
  tasks: ReviewTask[];
  onSelect: (taskId: string) => void;
};

export function TaskDetail({ task, tasks, onSelect }: Props) {
  const progress = taskProgress(task);
  const dependents = dependentsFor(tasks, task.id);
  const fileEntries = Object.entries(task.files).filter(([, value]) => Boolean(value));
  const trustEntries = Object.entries(task.trust.checks);

  return (
    <aside className={styles.detailPanel}>
      <div className={styles.detailHeader}>
        <span className={styles.statusBadge}>{statusLabels[task.status]}</span>
        <span className={styles.cardMeta}>{task.dcref ?? task.kind}</span>
      </div>

      <h1>{task.title}</h1>
      <p className={styles.detailSummary}>{task.description}</p>

      <div className={styles.detailGrid}>
        <div>
          <span>Task</span>
          <strong>{task.id}</strong>
        </div>
        <div>
          <span>Next role</span>
          <strong>{task.next_role}</strong>
        </div>
        <div>
          <span>Trust</span>
          <strong>{trustLabels[task.trust_level]}</strong>
        </div>
        <div>
          <span>Risk</span>
          <strong>{task.formalization_risk}</strong>
        </div>
      </div>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Progress</div>
        <div className={styles.progressRow}>
          <div className={styles.meter} aria-label={`${progress}% complete`}>
            <span style={{ width: `${progress}%` }} />
          </div>
          <strong>{progress}%</strong>
        </div>
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Trust criteria</div>
        <div className={styles.checklist}>
          {trustEntries.length === 0 ? <span className={styles.emptyState}>Aggregate task.</span> : null}
          {trustEntries.map(([key, value]) => (
            <label key={key}>
              <input checked={value === 'done' || value === 'accepted' || value === 'verified'} disabled readOnly type="checkbox" />
              <span>{key}: {value}</span>
            </label>
          ))}
        </div>
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Why this matters</div>
        <p className={styles.detailSummary}>{task.why_it_matters}</p>
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Files</div>
        {fileEntries.length === 0 ? (
          <p className={styles.emptyState}>No files listed.</p>
        ) : (
          <div className={styles.fileList}>
            {fileEntries.map(([kind, path]) => (
              <code key={kind}>{path}</code>
            ))}
          </div>
        )}
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Dependencies</div>
        <div className={styles.linkList}>
          {task.depends_on.length === 0 ? <span className={styles.emptyState}>None</span> : null}
          {task.depends_on.map((dependencyId) => {
            const dependency = findTask(tasks, dependencyId);
            return (
              <button key={dependencyId} type="button" onClick={() => onSelect(dependencyId)}>
                {dependencyId}
                {dependency ? <small>{dependency.title}</small> : null}
              </button>
            );
          })}
        </div>
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Review evidence</div>
        <div className={styles.detailGrid}>
          <div>
            <span>Required</span>
            <strong>{task.reviews.required}</strong>
          </div>
          <div>
            <span>Completed</span>
            <strong>{task.reviews.completed}</strong>
          </div>
        </div>
        {task.reviews.ids.length === 0 ? (
          <p className={styles.emptyState}>No review records linked yet.</p>
        ) : (
          <div className={styles.linkList}>
            {task.reviews.ids.map((id) => <span className={styles.chip} key={id}>{id}</span>)}
          </div>
        )}
      </section>

      <section className={styles.detailSection}>
        <div className={styles.sectionTitle}>Dependents</div>
        <div className={styles.linkList}>
          {dependents.length === 0 ? <span className={styles.emptyState}>None</span> : null}
          {dependents.map((dependent) => (
            <button key={dependent.id} type="button" onClick={() => onSelect(dependent.id)}>
              {dependent.id}
              <small>{dependent.title}</small>
            </button>
          ))}
        </div>
      </section>
    </aside>
  );
}
