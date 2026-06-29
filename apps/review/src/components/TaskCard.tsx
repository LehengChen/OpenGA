import styles from '../App.module.css';
import { taskProgress } from '../lib/progress';
import { ReviewTask, statusLabels, trustLabels } from '../lib/taskSchema';

type Props = {
  task: ReviewTask;
  childCount?: number;
  isSelected: boolean;
  onSelect: (taskId: string) => void;
};

export function TaskCard({ task, childCount = 0, isSelected, onSelect }: Props) {
  const progress = taskProgress(task);

  return (
    <button
      className={`${styles.taskCard} ${isSelected ? styles.selectedCard : ''}`}
      type="button"
      onClick={() => onSelect(task.id)}
    >
      <div className={styles.cardTopline}>
        <span className={styles.statusBadge}>{statusLabels[task.status]}</span>
        <span className={styles.cardMeta}>{task.chapter === null ? task.kind : `Ch. ${task.chapter}`}</span>
      </div>

      <div className={styles.cardTitle}>{task.title}</div>
      <div className={styles.cardId}>
        {task.id}{task.dcref ? ` · ${task.dcref}` : ''}
      </div>
      <p>{task.description}</p>

      <div className={styles.progressRow}>
        <div className={styles.meter} aria-label={`${progress}% complete`}>
          <span style={{ width: `${progress}%` }} />
        </div>
        <strong>{progress}%</strong>
      </div>

      <div className={styles.chipRow}>
        <span className={styles.chip}>{task.next_role}</span>
        <span className={styles.chip}>{trustLabels[task.trust_level]}</span>
        <span className={styles.chip}>{task.difficulty}</span>
        {childCount > 0 ? <span className={styles.chip}>{childCount} subtasks</span> : null}
        {task.depends_on.length > 0 ? (
          <span className={styles.chip}>{task.depends_on.length} deps</span>
        ) : null}
      </div>
    </button>
  );
}
