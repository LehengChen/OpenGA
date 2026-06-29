import styles from '../App.module.css';
import { childrenFor, rootTasks, taskProgress } from '../lib/progress';
import { ReviewTask, statusLabels } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

function TreeNode({ task, tasks, selectedId, onSelect, level }: Props & { task: ReviewTask; level: number }) {
  const children = childrenFor(tasks, task.id);
  const progress = taskProgress(task);

  return (
    <div className={styles.treeNode}>
      <button
        className={`${styles.treeButton} ${selectedId === task.id ? styles.selectedTreeButton : ''}`}
        style={{ paddingLeft: `${12 + level * 22}px` }}
        type="button"
        onClick={() => onSelect(task.id)}
      >
        <span className={styles.treeTitle}>{task.title}</span>
        <span className={styles.treeMeta}>
          {task.id} · {task.kind} · {statusLabels[task.status]} · {progress}%
        </span>
      </button>

      {children.map((child) => (
        <TreeNode
          key={child.id}
          task={child}
          tasks={tasks}
          selectedId={selectedId}
          onSelect={onSelect}
          level={level + 1}
        />
      ))}
    </div>
  );
}

export function TaskTree({ tasks, selectedId, onSelect }: Props) {
  return (
    <div className={styles.treeView}>
      {rootTasks(tasks).map((task) => (
        <TreeNode
          key={task.id}
          task={task}
          tasks={tasks}
          selectedId={selectedId}
          onSelect={onSelect}
          level={0}
        />
      ))}
    </div>
  );
}
