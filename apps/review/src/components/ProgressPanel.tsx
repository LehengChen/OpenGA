import styles from '../App.module.css';
import { roadmapMetrics, statusCounts, trustCounts } from '../lib/progress';
import { ReviewTask, statusLabels, trustLabels } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
};

export function ProgressPanel({ tasks }: Props) {
  const progress = roadmapMetrics(tasks);
  const counts = statusCounts(tasks);
  const trusts = trustCounts(tasks);

  return (
    <section className={styles.progressPanel} aria-label="Pilot progress">
      <div>
        <div className={styles.panelLabel}>Overall</div>
        <div className={styles.overallValue}>{progress.overall}%</div>
      </div>

      <div className={styles.metricGrid}>
        {progress.metrics.map((metric) => (
          <div className={styles.metric} key={metric.key}>
            <span>{metric.label}</span>
            <strong>
              {metric.completed}/{metric.total}
            </strong>
            <div className={styles.meter} aria-hidden="true">
              <span style={{ width: `${metric.percent}%` }} />
            </div>
          </div>
        ))}
      </div>

      <div className={styles.statusStrip} aria-label="Status counts">
        {counts
          .filter((item) => item.count > 0)
          .map((item) => (
            <span className={styles.statusPill} key={item.status}>
              {statusLabels[item.status]}: {item.count}
            </span>
          ))}
        {trusts.map((item) => (
            <span className={styles.statusPill} key={item.trust}>
              {trustLabels[item.trust as keyof typeof trustLabels] ?? item.trust}: {item.count}
            </span>
          ))}
      </div>
    </section>
  );
}
