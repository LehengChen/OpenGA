import styles from '../App.module.css';
import { dagEdges, leafTasks, taskDepth, upstreamTasks } from '../lib/progress';
import { ReviewTask } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

const NODE_WIDTH = 168;
const NODE_HEIGHT = 64;
const COLUMN_GAP = 64;
const ROW_GAP = 24;
const PADDING = 20;

export function DagView({ tasks, selectedId, onSelect }: Props) {
  const leaves = leafTasks(tasks);
  const edges = dagEdges(tasks);

  const depthMap = new Map<string, number>();
  for (const task of leaves) {
    depthMap.set(task.id, taskDepth(tasks, task.id));
  }

  const rows = new Map<number, ReviewTask[]>();
  const maxDepth = Math.max(0, ...depthMap.values());
  for (let d = 0; d <= maxDepth; d++) {
    rows.set(
      d,
      leaves.filter((t) => depthMap.get(t.id) === d)
    );
  }

  const maxRows = Math.max(...Array.from(rows.values()).map((r) => r.length), 1);

  const width = (maxDepth + 1) * (NODE_WIDTH + COLUMN_GAP) + PADDING * 2 - COLUMN_GAP;
  const height = maxRows * (NODE_HEIGHT + ROW_GAP) + PADDING * 2 - ROW_GAP;

  const nodePositions = new Map<string, { x: number; y: number }>();

  for (let d = 0; d <= maxDepth; d++) {
    const row = rows.get(d) ?? [];
    const rowHeight = row.length * NODE_HEIGHT + (row.length - 1) * ROW_GAP;
    const startY = (height - rowHeight) / 2;
    for (let i = 0; i < row.length; i++) {
      const task = row[i];
      nodePositions.set(task.id, {
        x: PADDING + d * (NODE_WIDTH + COLUMN_GAP),
        y: startY + i * (NODE_HEIGHT + ROW_GAP)
      });
    }
  }

  function pathFor(edge: { from: string; to: string }) {
    const fromPos = nodePositions.get(edge.from);
    const toPos = nodePositions.get(edge.to);
    if (!fromPos || !toPos) return '';

    const x1 = fromPos.x + NODE_WIDTH;
    const y1 = fromPos.y + NODE_HEIGHT / 2;
    const x2 = toPos.x;
    const y2 = toPos.y + NODE_HEIGHT / 2;
    const c1x = x1 + COLUMN_GAP / 2;
    const c2x = x2 - COLUMN_GAP / 2;

    return `M ${x1} ${y1} C ${c1x} ${y1}, ${c2x} ${y2}, ${x2} ${y2}`;
  }

  return (
    <div className={styles.dagView}>
      <svg width={width} height={height} viewBox={`0 0 ${width} ${height}`}>
        <defs>
          <marker
            id="dag-arrow"
            markerWidth="10"
            markerHeight="10"
            refX="9"
            refY="3"
            orient="auto"
            markerUnits="strokeWidth"
          >
            <path d="M0,0 L0,6 L9,3 z" fill="#94a3b8" />
          </marker>
        </defs>

        {edges.map((edge) => {
          const isSelected = selectedId === edge.to || selectedId === edge.from;
          return (
            <path
              key={`${edge.from}-${edge.to}`}
              d={pathFor(edge)}
              className={`${styles.dagEdge} ${isSelected ? styles.selectedDagEdge : ''}`}
              markerEnd="url(#dag-arrow)"
            />
          );
        })}

        {leaves.map((task) => {
          const pos = nodePositions.get(task.id);
          if (!pos) return null;

          const isSelected = selectedId === task.id;
          const upstream = upstreamTasks(tasks, task.id);
          const isDimmed = selectedId && selectedId !== task.id && !upstream.some((t) => t.id === selectedId);

          return (
            <g
              key={task.id}
              transform={`translate(${pos.x}, ${pos.y})`}
              className={`${styles.dagNode} ${isSelected ? styles.selectedDagNode : ''} ${isDimmed ? styles.dimmedDagNode : ''}`}
              onClick={() => onSelect(task.id)}
              role="button"
              tabIndex={0}
              onKeyDown={(e) => {
                if (e.key === 'Enter' || e.key === ' ') onSelect(task.id);
              }}
            >
              <rect width={NODE_WIDTH} height={NODE_HEIGHT} rx={8} ry={8} />
              <foreignObject x={8} y={8} width={NODE_WIDTH - 16} height={NODE_HEIGHT - 16}>
                <div className={styles.dagNodeContent}>
                  <strong>{task.id}</strong>
                  <span>{task.title}</span>
                </div>
              </foreignObject>
            </g>
          );
        })}
      </svg>

      <div className={styles.dagLegend}>
        <span>
          <span className={styles.dagLegendDot} /> Selected
        </span>
        <span>
          <span className={`${styles.dagLegendDot} ${styles.dagLegendUpstream}`} /> Upstream
        </span>
        <span>
          <span className={`${styles.dagLegendDot} ${styles.dagLegendOther}`} /> Other
        </span>
      </div>
    </div>
  );
}
