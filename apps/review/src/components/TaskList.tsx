import { useState } from 'react';
import styles from '../App.module.css';
import { childrenFor, rootTasks, taskProgress, tasksDone, tasksTotal } from '../lib/progress';
import { ReviewTask, sortAbbrev, statusLabels } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

type NestedItemProps = {
  task: ReviewTask;
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
  level: number;
  openSet: Set<string>;
  toggle: (id: string) => void;
};

function NestedItem({
  task,
  tasks,
  selectedId,
  onSelect,
  level,
  openSet,
  toggle
}: NestedItemProps) {
  const children = childrenFor(tasks, task.id);
  const isOpen = openSet.has(task.id);
  const isSelected = selectedId === task.id;
  const isGroup = task.kind !== 'leaf';
  const progress = taskProgress(tasks, task.id);
  const done = tasksDone(tasks, task.id);
  const total = tasksTotal(tasks, task.id);

  const handleRowClick = () => {
    onSelect(task.id);
  };

  return (
    <div className={styles.nestedItem} style={{ marginLeft: `${level * 18}px` }}>
      <div className={styles.nestedRow}>
        {children.length > 0 ? (
          <button
            type="button"
            className={styles.nestedToggle}
            onClick={(e) => {
              e.stopPropagation();
              toggle(task.id);
            }}
            aria-label={isOpen ? `Collapse ${task.title}` : `Expand ${task.title}`}
            aria-expanded={isOpen}
          >
            {isOpen ? '▾' : '▸'}
          </button>
        ) : (
          <span className={styles.nestedSpacer} />
        )}

        <button
          className={`${styles.nestedRowButton} ${isSelected ? styles.selectedNestedRow : ''} ${isGroup ? styles.nestedGroupRow : ''}`}
          type="button"
          onClick={handleRowClick}
          aria-pressed={isSelected}
        >
          <span className={styles.nestedStatus}>{statusLabels[task.status]}</span>
          {!isGroup && task.sort ? (
            <span className={styles.kindTag} title={task.sort}>
              {sortAbbrev[task.sort] ?? task.sort}
            </span>
          ) : null}
          {!isGroup && task.formalized ? (
            <span className={styles.formalizedTag} title="Formalized in Lean">⊢ Lean</span>
          ) : null}
          <span className={styles.nestedTitle} title={task.title}>{task.title}</span>
          <span className={styles.nestedMeta} title={task.id}>{task.id}</span>

          {isGroup ? (
            <span className={styles.nestedProgress}>{done}/{total} · {progress}%</span>
          ) : (
            <span
              className={`${styles.nestedProgress} ${progress === 100 ? styles.nestedProgressDone : styles.nestedProgressPending}`}
            >
              {progress === 100 ? 'Review done' : `${progress}% pending`}
            </span>
          )}
        </button>
      </div>

      {isOpen && children.length > 0 ? (
        <div className={styles.nestedChildren}>
          {children.map((child) => (
            <NestedItem
              key={child.id}
              task={child}
              tasks={tasks}
              selectedId={selectedId}
              onSelect={onSelect}
              level={level + 1}
              openSet={openSet}
              toggle={toggle}
            />
          ))}
        </div>
      ) : null}
    </div>
  );
}

export function TaskList({ tasks, selectedId, onSelect }: Props) {
  const [openSet, setOpenSet] = useState<Set<string>>(() => {
    const set = new Set<string>();
    rootTasks(tasks).forEach((root) => {
      set.add(root.id);
      childrenFor(tasks, root.id).forEach((cluster) => set.add(cluster.id));
    });
    return set;
  });

  const toggle = (id: string) => {
    const next = new Set(openSet);
    if (next.has(id)) {
      next.delete(id);
    } else {
      next.add(id);
    }
    setOpenSet(next);
  };

  const roots = rootTasks(tasks);

  if (roots.length === 0) {
    return <p className={styles.emptyState}>No tasks available.</p>;
  }

  return (
    <div className={styles.nestedList}>
      {roots.map((task) => (
        <NestedItem
          key={task.id}
          task={task}
          tasks={tasks}
          selectedId={selectedId}
          onSelect={onSelect}
          level={0}
          openSet={openSet}
          toggle={toggle}
        />
      ))}
    </div>
  );
}
