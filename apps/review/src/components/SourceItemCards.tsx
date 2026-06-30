import type { TaskSourceItem } from '../lib/taskSchema';
import { LeanCodeBlock } from './LeanCodeBlock';
import styles from './SourceItemCards.module.css';

type Props = {
  items: TaskSourceItem[];
  activeItemId: string | null;
  onActiveItemChange: (itemId: string) => void;
};

function itemLabel(item: TaskSourceItem, index: number): string {
  return `${index + 1}. ${item.title}`;
}

function clampIndex(index: number, itemCount: number): number {
  if (itemCount === 0) return 0;
  if (index < 0) return itemCount - 1;
  if (index >= itemCount) return 0;
  return index;
}

export function SourceItemCards({ items, activeItemId, onActiveItemChange }: Props) {
  const selectedIndex = Math.max(0, items.findIndex((item) => item.id === activeItemId));
  const activeIndex = clampIndex(selectedIndex, items.length);
  const activeItem = items[activeIndex];

  if (!activeItem) {
    return <p className={styles.empty}>No statements are available.</p>;
  }

  const moveSelection = (offset: number) => {
    const nextItem = items[clampIndex(activeIndex + offset, items.length)];
    if (nextItem) onActiveItemChange(nextItem.id);
  };

  return (
    <div className={styles.statementLayout}>
      <nav className={styles.statementRail} aria-label="Formal statements">
        {items.map((item, index) => (
          <button
            key={item.id}
            type="button"
            className={item.id === activeItem.id ? styles.activeStatementButton : ''}
            onClick={() => onActiveItemChange(item.id)}
          >
            <span>{itemLabel(item, index)}</span>
            {item.meta?.[0] ? <small>{item.meta[0]}</small> : null}
          </button>
        ))}
      </nav>

      <article className={styles.statementCard}>
        <header className={styles.statementHeader}>
          <div>
            <p className={styles.statementCount}>
              Statement {activeIndex + 1} of {items.length}
            </p>
            <h2>{activeItem.title}</h2>
            {activeItem.meta?.length ? (
              <div className={styles.statementMeta}>
                {activeItem.meta.map((item) => (
                  <span key={item}>{item}</span>
                ))}
              </div>
            ) : null}
          </div>
          <div className={styles.statementNav}>
            <button
              type="button"
              aria-label="Previous formal statement"
              onClick={() => moveSelection(-1)}
            >
              Previous
            </button>
            <button
              type="button"
              aria-label="Next formal statement"
              onClick={() => moveSelection(1)}
            >
              Next
            </button>
          </div>
        </header>

        {activeItem.description ? (
          <p className={styles.statementDescription}>{activeItem.description}</p>
        ) : null}

        {activeItem.kind === 'lean' ? (
          <LeanCodeBlock
            code={activeItem.content}
            language={activeItem.language}
            className={styles.statementCode}
            aria-label={`${activeItem.title} Lean statement`}
          />
        ) : (
          <pre className={styles.statementCode}>
            <code>{activeItem.content}</code>
          </pre>
        )}
      </article>
    </div>
  );
}
