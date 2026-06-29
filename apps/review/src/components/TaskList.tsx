import { useState } from 'react';
import styles from '../App.module.css';
import { childrenFor, rootTasks, taskProgress, tasksDone, tasksTotal } from '../lib/progress';
import { ReviewTask, statusLabels } from '../lib/taskSchema';

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

function NestedItem({ task, tasks, selectedId, onSelect, level, openSet, toggle }: NestedItemProps) {
  const children = childrenFor(tasks, task.id);
  const isOpen = openSet.has(task.id);
  const isSelected = selectedId === task.id;
  const isGroup = task.kind !== 'leaf';
  const progress = taskProgress(tasks, task.id);
  const done = tasksDone(tasks, task.id);
  const total = tasksTotal(tasks, task.id);
  const mathReview = task.checks?.math_review ?? null;

  return (
    <div className={styles.nestedItem} style={{ marginLeft: `${level * 18}px` }}>
      <button
        className={`${styles.nestedRow} ${isSelected ? styles.selectedNestedRow : ''} ${isGroup ? styles.nestedGroupRow : ''}`}
        type="button"
        onClick={() => onSelect(task.id)}
      >
        {children.length > 0 ? (
          <span
            className={styles.nestedToggle}
            onClick={(e) => {
              e.stopPropagation();
              toggle(task.id);
            }}
            role="button"
            tabIndex={0}
            onKeyDown={(e) => {
              if (e.key === 'Enter' || e.key === ' ') toggle(task.id);
            }}
          >
            {isOpen ? '▾' : '▸'}
          </span>
        ) : (
          <span className={styles.nestedSpacer} />
        )}

        <span className={styles.nestedStatus}>{statusLabels[task.status]}</span>
        <span className={styles.nestedTitle}>{task.title}</span>
        <span className={styles.nestedMeta}>{task.id}</span>

        {isGroup ? (
          <span className={styles.nestedProgress}>{done}/{total} · {progress}%</span>
        ) : mathReview ? (
          <span className={styles.nestedProgress}>
            {mathReview === 'done' ? 'Review done' : 'Review pending'}
          </span>
        ) : null}
      </button>

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

  return (
    <div className={styles.nestedList}>
      {rootTasks(tasks).map((task) => (
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
