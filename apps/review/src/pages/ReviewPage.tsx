import { lazy, Suspense, useEffect, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import styles from '../App.module.css';
import { LeanCodeBlock } from '../components/LeanCodeBlock';
import { SourceItemCards } from '../components/SourceItemCards';
import { fetchNeighbors, fetchTaskSource, submitReview } from '../api';
import { findTask } from '../lib/progress';
import type { TaskDataset, TaskSource } from '../lib/taskSchema';

const AtomViewer = lazy(() =>
  import('../components/AtomViewer').then((module) => ({ default: module.AtomViewer }))
);

type Props = {
  projectId: string;
  dataset: TaskDataset;
  onRefresh: () => Promise<void>;
};

function checkLabel(key: string): string {
  const labels: Record<string, string> = {
    informal_review: 'Informal statement reviewed',
    formal_review: 'Formal statement reviewed'
  };
  if (labels[key]) return labels[key];

  return key
    .split('_')
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join(' ');
}

function allChecksDone(checks: Record<string, boolean>): boolean {
  const values = Object.values(checks);
  return values.length > 0 && values.every(Boolean);
}

export function ReviewPage({ projectId, dataset, onRefresh }: Props) {
  const { taskId } = useParams<{ taskId: string }>();
  const navigate = useNavigate();
  const task = taskId ? findTask(dataset.tasks, taskId) : undefined;

  const [source, setSource] = useState<TaskSource | null>(null);
  const [activePanelId, setActivePanelId] = useState<string | null>(null);
  const [activeItemByPanelId, setActiveItemByPanelId] = useState<Record<string, string>>({});
  const [editedContent, setEditedContent] = useState<Record<string, string>>({});
  const [originalContent, setOriginalContent] = useState<Record<string, string>>({});
  const [editSource, setEditSource] = useState(false);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [checkStates, setCheckStates] = useState<Record<string, boolean>>({});
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
    setEditSource(false);
    setSource(null);
    setActivePanelId(null);
    setActiveItemByPanelId({});

    Promise.all([fetchTaskSource(projectId, taskId), fetchNeighbors(projectId, taskId)])
      .then(([sourceData, neighborData]) => {
        setSource(sourceData);
        const contentById = Object.fromEntries(
          sourceData.panels.map((panel) => [panel.id, panel.content])
        );
        setEditedContent(contentById);
        setOriginalContent(contentById);
        setActivePanelId(sourceData.panels[0]?.id ?? null);
        setActiveItemByPanelId(
          Object.fromEntries(
            sourceData.panels.flatMap((panel) =>
              panel.items?.[0] ? [[panel.id, panel.items[0].id]] : []
            )
          )
        );
        setNeighbors(neighborData);
        const currentTask = findTask(dataset.tasks, taskId);
        setCheckStates(
          Object.fromEntries(
            Object.entries(currentTask?.checks ?? {}).map(([key, value]) => [
              key,
              value === 'done'
            ])
          )
        );
      })
      .catch((err) => setError(err.message))
      .finally(() => setLoading(false));
  }, [projectId, taskId, dataset.tasks]);

  if (!task) {
    return (
      <main className={styles.appShell}>
        <p className={styles.emptyState}>Task not found.</p>
        <button
          type="button"
          className={styles.backButton}
          onClick={() => navigate(`/projects/${encodeURIComponent(projectId)}`)}
        >
          Back to list
        </button>
      </main>
    );
  }

  const activePanel = source?.panels.find((panel) => panel.id === activePanelId) ?? source?.panels[0];
  const activeContent = activePanel ? editedContent[activePanel.id] ?? activePanel.content : '';
  const atomPanel = source?.panels.find((panel) => panel.id === 'atom');
  const isAtomModified = atomPanel ? editedContent.atom !== originalContent.atom : false;
  const isReviewStateModified = Object.entries(checkStates).some(([key, value]) => {
    return value !== (task.checks?.[key] === 'done');
  });
  const canSubmit = isReviewStateModified || note.trim().length > 0 || isAtomModified;
  const savedChecks = Object.fromEntries(
    Object.entries(task.checks ?? {}).map(([key, value]) => [key, value === 'done'])
  );
  const savedAllDone = allChecksDone(savedChecks);

  const handleSubmit = async () => {
    if (!canSubmit || !taskId) return;
    setSubmitting(true);
    setSubmitError(null);

    try {
      const result = await submitReview(projectId, taskId, {
        checks: checkStates,
        note,
        atomContent: isAtomModified ? editedContent.atom : undefined
      });
      await onRefresh();
      if (result.nextId) {
        navigate(`/projects/${encodeURIComponent(projectId)}/review/${encodeURIComponent(result.nextId)}`);
      } else {
        navigate(`/projects/${encodeURIComponent(projectId)}`);
      }
    } catch (err) {
      setSubmitError(err instanceof Error ? err.message : String(err));
    } finally {
      setSubmitting(false);
    }
  };

  const goTo = (id: string | null) => {
    if (id) navigate(`/projects/${encodeURIComponent(projectId)}/review/${encodeURIComponent(id)}`);
  };

  return (
    <main className={styles.appShell}>
      <header className={styles.reviewHeader}>
        <button
          type="button"
          className={styles.backButton}
          onClick={() => navigate(`/projects/${encodeURIComponent(projectId)}`)}
        >
          ← Back to list
        </button>
        <div>
          <p className={styles.kicker}>{task.id}{task.dcref ? ` · ${task.dcref}` : ''}</p>
          <h1>{task.title}</h1>
          <span
            className={`${styles.reviewStatusBadge} ${savedAllDone ? styles.reviewStatusDone : styles.reviewStatusPending}`}
          >
            {savedAllDone ? 'Review checks done' : 'Review checks pending'}
          </span>
        </div>
      </header>

      <section className={styles.reviewGrid}>
        <article className={styles.atomPanel}>
          <div className={styles.sectionTitle}>
            <span>{activePanel?.title ?? 'Task source'}</span>
            {source && source.panels.length > 1 ? (
              <div className={styles.sourceTabs} aria-label="Source panels">
                {source.panels.map((panel) => (
                  <button
                    key={panel.id}
                    type="button"
                    className={panel.id === activePanel?.id ? styles.activeSourceTab : ''}
                    onClick={() => {
                      setActivePanelId(panel.id);
                      setEditSource(false);
                    }}
                  >
                    {panel.title}
                  </button>
                ))}
              </div>
            ) : null}
            {!loading && !error && activePanel?.editable ? (
              <button
                type="button"
                className={styles.atomEditToggle}
                onClick={() => setEditSource((prev) => !prev)}
              >
                {editSource ? 'Preview' : 'Edit source'}
                {isAtomModified && !editSource ? ' · modified' : ''}
              </button>
            ) : null}
          </div>
          {loading ? (
            <p className={styles.emptyState}>Loading source…</p>
          ) : error ? (
            <p className={styles.emptyState} role="alert">Error: {error}</p>
          ) : editSource && activePanel?.editable ? (
            <textarea
              className={styles.atomEditor}
              value={activeContent}
              onChange={(e) => {
                if (!activePanel) return;
                setEditedContent((prev) => ({
                  ...prev,
                  [activePanel.id]: e.target.value
                }));
              }}
              rows={24}
              spellCheck={false}
              aria-label="Source editor"
            />
          ) : activePanel?.items?.length ? (
            <SourceItemCards
              items={activePanel.items}
              activeItemId={activeItemByPanelId[activePanel.id] ?? activePanel.items[0]?.id ?? null}
              onActiveItemChange={(itemId) => {
                setActiveItemByPanelId((prev) => ({
                  ...prev,
                  [activePanel.id]: itemId
                }));
              }}
            />
          ) : activePanel?.kind === 'lean' ? (
            <LeanCodeBlock
              code={activeContent}
              language={activePanel.language}
              className={styles.codeSource}
              aria-label={`${activePanel.title} Lean source`}
            />
          ) : (
            <Suspense fallback={<p className={styles.emptyState}>Loading markdown renderer...</p>}>
              <AtomViewer content={activeContent} />
            </Suspense>
          )}
        </article>

        <aside className={styles.reviewControls}>
          <div className={styles.sectionTitle}>Review checklist</div>
          <p className={styles.detailSummary}>
            Review this task against its declared source material and update the checks that apply.
          </p>
          <div className={styles.checklist}>
            {Object.keys(checkStates).length > 0 ? (
              Object.entries(checkStates).map(([key, value]) => (
                <label key={key}>
                  <input
                    checked={value}
                    onChange={(e) => {
                      setCheckStates((prev) => ({
                        ...prev,
                        [key]: e.target.checked
                      }));
                    }}
                    type="checkbox"
                  />
                  <span>{checkLabel(key)}</span>
                </label>
              ))
            ) : (
              <p className={styles.detailSummary}>No review checks are configured for this task.</p>
            )}
          </div>

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
