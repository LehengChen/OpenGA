import type { LeanDependencyNode, TaskSourceItem } from '../lib/taskSchema';
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

function sourceLabel(source: LeanDependencyNode['source']): string {
  if (source === 'lee') return 'Lee';
  if (source === 'mathlib') return 'Mathlib';
  return 'Other';
}

function DependencyNode({ node, depth = 0 }: { node: LeanDependencyNode; depth?: number }) {
  const childCount = node.children?.length ?? 0;
  const hasChildren = childCount > 0;

  return (
    <details className={styles.dependencyNode} open={depth === 0}>
      <summary>
        <span className={styles.dependencyName}>{node.name}</span>
        <span className={styles.dependencyBadge}>{sourceLabel(node.source)}</span>
        <span className={styles.dependencyKind}>{node.kind}</span>
        {node.repeated ? <span className={styles.dependencyKind}>repeated</span> : null}
        {node.truncated ? <span className={styles.dependencyKind}>truncated</span> : null}
      </summary>
      <div className={styles.dependencyBody}>
        <p className={styles.dependencyModule}>{node.module}</p>
        {node.doc ? <p className={styles.dependencyDoc}>{node.doc}</p> : null}
        {node.docsUrl || node.sourceUrl ? (
          <div className={styles.dependencyLinks}>
            {node.docsUrl ? (
              <a href={node.docsUrl} target="_blank" rel="noreferrer">
                Docs
              </a>
            ) : null}
            {node.sourceUrl ? (
              <a href={node.sourceUrl} target="_blank" rel="noreferrer">
                Source
              </a>
            ) : null}
          </div>
        ) : null}
        <LeanCodeBlock
          code={node.type}
          language="lean"
          className={styles.dependencyCode}
          aria-label={`${node.name} Lean type`}
        />
        {hasChildren ? (
          <div className={styles.dependencyChildren}>
            {node.children?.map((child) => (
              <DependencyNode key={child.id} node={child} depth={depth + 1} />
            ))}
          </div>
        ) : null}
      </div>
    </details>
  );
}

function DependencyTree({ nodes }: { nodes: LeanDependencyNode[] | undefined }) {
  if (!nodes?.length) return null;

  return (
    <section className={styles.dependencies}>
      <header>
        <h3>Statement dependencies</h3>
        <span>{nodes.length} root{nodes.length === 1 ? '' : 's'}</span>
      </header>
      <div className={styles.dependencyTree}>
        {nodes.map((node) => (
          <DependencyNode key={node.id} node={node} />
        ))}
      </div>
    </section>
  );
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

        <DependencyTree nodes={activeItem.dependencies} />
      </article>
    </div>
  );
}
