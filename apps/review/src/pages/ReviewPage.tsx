import { useEffect, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import styles from '../App.module.css';
import { AtomViewer } from '../components/AtomViewer';
import { fetchAtom, fetchNeighbors, submitReview } from '../api';
import { findTask } from '../lib/progress';
import type { TaskDataset } from '../lib/taskSchema';

type Props = {
  dataset: TaskDataset;
  onRefresh: () => Promise<void>;
};

export function ReviewPage({ dataset, onRefresh }: Props) {
  const { taskId } = useParams<{ taskId: string }>();
  const navigate = useNavigate();
  const task = taskId ? findTask(dataset.tasks, taskId) : undefined;

  const [atomContent, setAtomContent] = useState<string>('');
  const [originalAtom, setOriginalAtom] = useState<string>('');
  const [editAtom, setEditAtom] = useState(false);
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
    setEditAtom(false);

    Promise.all([fetchAtom(taskId), fetchNeighbors(taskId)])
      .then(([atom, neighborData]) => {
        setAtomContent(atom);
        setOriginalAtom(atom);
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
        <button type="button" className={styles.backButton} onClick={() => navigate('/')}>
          Back to list
        </button>
      </main>
    );
  }

  const savedMathReview = task.checks?.math_review === 'done';
  const isReviewStateModified = mathReview !== savedMathReview;
  const isAtomModified = atomContent !== originalAtom;
  const canSubmit = isReviewStateModified || note.trim().length > 0 || isAtomModified;

  const handleSubmit = async () => {
    if (!canSubmit || !taskId) return;
    setSubmitting(true);
    setSubmitError(null);

    try {
      const result = await submitReview(taskId, {
        mathReview,
        note,
        atomContent: isAtomModified ? atomContent : undefined
      });
      await onRefresh();
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
          <span
            className={`${styles.reviewStatusBadge} ${savedMathReview ? styles.reviewStatusDone : styles.reviewStatusPending}`}
          >
            {savedMathReview ? '✓ Math review done' : '○ Math review pending'}
          </span>
        </div>
      </header>

      <section className={styles.reviewGrid}>
        <article className={styles.atomPanel}>
          <div className={styles.sectionTitle}>
            <span>Atom source</span>
            {!loading && !error ? (
              <button
                type="button"
                className={styles.atomEditToggle}
                onClick={() => setEditAtom((prev) => !prev)}
              >
                {editAtom ? 'Preview' : 'Edit source'}
                {isAtomModified && !editAtom ? ' · modified' : ''}
              </button>
            ) : null}
          </div>
          {loading ? (
            <p className={styles.emptyState}>Loading atom…</p>
          ) : error ? (
            <p className={styles.emptyState} role="alert">Error: {error}</p>
          ) : editAtom ? (
            <textarea
              className={styles.atomEditor}
              value={atomContent}
              onChange={(e) => setAtomContent(e.target.value)}
              rows={24}
              spellCheck={false}
              aria-label="Atom source editor"
            />
          ) : (
            <AtomViewer content={atomContent} />
          )}
        </article>

        <aside className={styles.reviewControls}>
          <div className={styles.sectionTitle}>Review checklist</div>
          <p className={styles.detailSummary}>
            Current state:{' '}
            <strong>{savedMathReview ? 'Math review done' : 'Math review pending'}</strong>.
            Toggle the checkbox to change it.
          </p>
          <label className={styles.checklist}>
            <input
              checked={mathReview}
              onChange={(e) => setMathReview(e.target.checked)}
              type="checkbox"
            />
            <span>Math review done</span>
          </label>

          <div className={styles.sectionTitle} style={{ marginTop: '18px' }}>
            Review notes
          </div>
          {task.review_notes.length > 0 ? (
            <ul className={styles.reviewNoteList}>
              {task.review_notes.map((item, index) => (
                <li key={index}>{item}</li>
              ))}
            </ul>
          ) : (
            <p className={styles.detailSummary}>No review notes yet.</p>
          )}
          <textarea
            className={styles.reviewNoteInput}
            value={note}
            onChange={(e) => setNote(e.target.value)}
            placeholder="Add a new note, correction, or question…"
            rows={4}
            aria-label="Add a review note"
          />

          {submitError ? <p className={styles.errorText} role="alert">{submitError}</p> : null}

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
