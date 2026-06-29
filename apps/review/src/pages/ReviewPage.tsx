import { useEffect, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import styles from '../App.module.css';
import { fetchAtom, fetchNeighbors, submitReview } from '../api';
import { findTask } from '../lib/progress';
import type { TaskDataset } from '../lib/taskSchema';

type Props = {
  dataset: TaskDataset;
};

export function ReviewPage({ dataset }: Props) {
  const { taskId } = useParams<{ taskId: string }>();
  const navigate = useNavigate();
  const task = taskId ? findTask(dataset.tasks, taskId) : undefined;

  const [atomContent, setAtomContent] = useState<string>('');
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [mathReview, setMathReview] = useState(false);
  const [note, setNote] = useState('');
  const [submitting, setSubmitting] = useState(false);
  const [submitError, setSubmitError] = useState<string | null>(null);
  const [neighbors, setNeighbors] = useState<{ prevId: string | null; nextId: string | null }>({
    prevId: null,
    nextId: null
  });

  useEffect(() => {
    if (!taskId) return;

    setLoading(true);
    setError(null);
    setNote('');
    setSubmitError(null);

    Promise.all([fetchAtom(taskId), fetchNeighbors(taskId)])
      .then(([atom, neighborData]) => {
        setAtomContent(atom);
        setNeighbors(neighborData);
        const currentTask = findTask(dataset.tasks, taskId);
        setMathReview(currentTask?.checks?.math_review === 'done');
      })
      .catch((err) => setError(err.message))
      .finally(() => setLoading(false));
  }, [taskId, dataset.tasks]);

  if (!task) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState}>Task not found.</p>
        <button type="button" onClick={() => navigate('/')}>
          Back to list
        </button>
      </main>
    );
  }

  const canSubmit = mathReview || note.trim().length > 0;

  const handleSubmit = async () => {
    if (!canSubmit || !taskId) return;
    setSubmitting(true);
    setSubmitError(null);

    try {
      const result = await submitReview(taskId, { mathReview, note });
      if (result.nextId) {
        navigate(`/review/${encodeURIComponent(result.nextId)}`);
      } else {
        navigate('/');
      }
    } catch (err) {
      setSubmitError(err instanceof Error ? err.message : String(err));
    } finally {
      setSubmitting(false);
    }
  };

  const goTo = (id: string | null) => {
    if (id) navigate(`/review/${encodeURIComponent(id)}`);
  };

  return (
    <main className={styles.appShell}>
      <header className={styles.reviewHeader}>
        <button type="button" className={styles.backButton} onClick={() => navigate('/')}>
          ← Back to list
        </button>
        <div>
          <p className={styles.kicker}>{task.id}{task.dcref ? ` · ${task.dcref}` : ''}</p>
          <h1>{task.title}</h1>
        </div>
      </header>

      <section className={styles.reviewGrid}>
        <article className={styles.atomPanel}>
          <div className={styles.sectionTitle}>Atom source</div>
          {loading ? (
            <p className={styles.emptyState}>Loading atom…</p>
          ) : error ? (
            <p className={styles.emptyState}>Error: {error}</p>
          ) : (
            <pre className={styles.atomContent}>{atomContent}</pre>
          )}
        </article>

        <aside className={styles.reviewControls}>
          <div className={styles.sectionTitle}>Review checklist</div>
          <label className={styles.checklist}>
            <input
              checked={mathReview}
              onChange={(e) => setMathReview(e.target.checked)}
              type="checkbox"
            />
            <span>Math review done</span>
          </label>
          <p className={styles.detailSummary}>
            Read the atom and verify the mathematical statement and proof are correct.
          </p>

          <div className={styles.sectionTitle} style={{ marginTop: '18px' }}>
            Review notes
          </div>
          <textarea
            className={styles.reviewNoteInput}
            value={note}
            onChange={(e) => setNote(e.target.value)}
            placeholder="Add notes, corrections, or questions about this task…"
            rows={6}
          />

          {submitError ? <p className={styles.errorText}>{submitError}</p> : null}

          <div className={styles.reviewActions}>
            <button
              type="button"
              onClick={() => goTo(neighbors.prevId)}
              disabled={!neighbors.prevId}
            >
              Previous
            </button>
            <button
              type="button"
              className={styles.primaryButton}
              onClick={handleSubmit}
              disabled={!canSubmit || submitting}
            >
              {submitting ? 'Saving…' : 'Submit and continue'}
            </button>
            <button
              type="button"
              onClick={() => goTo(neighbors.nextId)}
              disabled={!neighbors.nextId}
            >
              Next
            </button>
          </div>
        </aside>
      </section>
    </main>
  );
}
