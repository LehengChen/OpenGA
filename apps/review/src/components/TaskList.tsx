import styles from '../App.module.css';
import { childrenFor } from '../lib/progress';
import { ReviewTask } from '../lib/taskSchema';
import { TaskCard } from './TaskCard';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

export function TaskList({ tasks, selectedId, onSelect }: Props) {
  return (
    <div className={styles.listView}>
      {tasks.map((task) => (
        <TaskCard
          key={task.id}
          task={task}
          childCount={childrenFor(tasks, task.id).length}
          isSelected={selectedId === task.id}
          onSelect={onSelect}
        />
      ))}
    </div>
  );
}
