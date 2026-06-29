import styles from '../App.module.css';
import { roadmapMetrics, statusCounts } from '../lib/progress';
import { ReviewTask, statusLabels } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
};

export function ProgressPanel({ tasks }: Props) {
  const metrics = roadmapMetrics(tasks);
  const counts = statusCounts(tasks);

  return (
    <section className={styles.progressPanel} aria-label="Pilot progress">
      <div>
        <div className={styles.panelLabel}>Leaf tasks</div>
        <div className={styles.overallValue}>{metrics.total}</div>
      </div>

      <div className={styles.metricGrid}>
        <div className={styles.metric}>
          <span>Done</span>
          <strong>{metrics.done}</strong>
        </div>
        <div className={styles.metric}>
          <span>In review</span>
          <strong>{metrics.inReview}</strong>
        </div>
        <div className={styles.metric}>
          <span>In progress</span>
          <strong>{metrics.inProgress}</strong>
        </div>
        <div className={styles.metric}>
          <span>Todo</span>
          <strong>{metrics.todo}</strong>
        </div>
      </div>

      <div className={styles.statusStrip} aria-label="Status counts">
        {counts.map((item) => (
          <span className={styles.statusPill} key={item.status}>
            {statusLabels[item.status]}: {item.count}
          </span>
        ))}
      </div>
    </section>
  );
}
