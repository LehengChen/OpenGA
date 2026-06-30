import { Link } from 'react-router-dom';
import styles from '../App.module.css';
import type { ReviewProject } from '../lib/taskSchema';

type Props = {
  projects: ReviewProject[];
};

function reviewKindLabel(kind: ReviewProject['reviewKind']): string {
  if (kind === 'lean_textbook') return 'Lean textbook review';
  return 'Atom math review';
}

export function ProjectIndexPage({ projects }: Props) {
  return (
    <main className={styles.appShell}>
      <header className={styles.projectHeader}>
        <p className={styles.kicker}>OpenGA Review</p>
        <h1>Review Projects</h1>
      </header>

      <section className={styles.projectGrid} aria-label="Review projects">
        {projects.map((project) => (
          <Link
            className={styles.projectCard}
            key={project.id}
            to={`/projects/${encodeURIComponent(project.id)}`}
          >
            <span className={styles.statusBadge}>{reviewKindLabel(project.reviewKind)}</span>
            <h2>{project.title}</h2>
            <p>{project.description}</p>
            <code>{project.taskPath}</code>
          </Link>
        ))}
      </section>
    </main>
  );
}
