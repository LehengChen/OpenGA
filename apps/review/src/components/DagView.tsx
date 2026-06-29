import { useEffect, useMemo, useRef, useState } from 'react';
import styles from '../App.module.css';
import { leafTasks } from '../lib/progress';
import type { ReviewTask } from '../lib/taskSchema';

type Props = {
  tasks: ReviewTask[];
  selectedId: string;
  onSelect: (taskId: string) => void;
};

type Scope = 'chapter' | 'focus' | 'all';
type DagNode = {
  task: ReviewTask;
  x: number;
  y: number;
  depth: number;
};

const NODE_WIDTH = 138;
const NODE_HEIGHT = 44;
const COLUMN_GAP = 56;
const ROW_GAP = 18;
const PADDING = 24;
const MAX_NODES_PER_ROW = 5;

function parseDcref(dcref: string | null): { chapter: number; section: number; index: number } {
  if (!dcref) return { chapter: 0, section: 0, index: 0 };
  const chPart = dcref.split(':')[0];
  const rest = dcref.split(':')[1] ?? '0.0';
  const [sectionStr, indexStr] = rest.split('.');
  return {
    chapter: parseInt(chPart.replace('ch', ''), 10) || 0,
    section: parseInt(sectionStr, 10) || 0,
    index: parseInt(indexStr, 10) || 0
  };
}

function computeDepthInScope(
  taskId: string,
  nodeIds: Set<string>,
  tasksMap: Map<string, ReviewTask>,
  memo = new Map<string, number>()
): number {
  if (memo.has(taskId)) return memo.get(taskId)!;
  const task = tasksMap.get(taskId);
  if (!task) {
    memo.set(taskId, 0);
    return 0;
  }
  const upstreamIds = task.depends_on.filter((id) => nodeIds.has(id));
  if (upstreamIds.length === 0) {
    memo.set(taskId, 0);
    return 0;
  }
  const depth = 1 + Math.max(...upstreamIds.map((id) => computeDepthInScope(id, nodeIds, tasksMap, memo)));
  memo.set(taskId, depth);
  return depth;
}

function buildNodes(
  visibleTasks: ReviewTask[],
  tasksMap: Map<string, ReviewTask>
): DagNode[] {
  const nodeIds = new Set(visibleTasks.map((t) => t.id));
  const depths = new Map<string, number>();
  for (const task of visibleTasks) {
    depths.set(task.id, computeDepthInScope(task.id, nodeIds, tasksMap));
  }

  const byDepth = new Map<number, ReviewTask[]>();
  let maxDepth = 0;
  for (const task of visibleTasks) {
    const d = depths.get(task.id) ?? 0;
    maxDepth = Math.max(maxDepth, d);
    if (!byDepth.has(d)) byDepth.set(d, []);
    byDepth.get(d)!.push(task);
  }

  const positions = new Map<string, { x: number; y: number }>();
  let currentY = 0;

  for (let d = 0; d <= maxDepth; d++) {
    const row = (byDepth.get(d) ?? []).sort((a, b) => {
      const pa = parseDcref(a.dcref);
      const pb = parseDcref(b.dcref);
      if (pa.section !== pb.section) return pa.section - pb.section;
      return pa.index - pb.index;
    });

    const rows = Math.ceil(row.length / MAX_NODES_PER_ROW);
    const layerHeight = rows * NODE_HEIGHT + (rows - 1) * ROW_GAP;
    const layerWidth = Math.min(row.length, MAX_NODES_PER_ROW) * NODE_WIDTH +
      (Math.min(row.length, MAX_NODES_PER_ROW) - 1) * ROW_GAP;
    const startX = PADDING;

    row.forEach((task, i) => {
      const rowIndex = Math.floor(i / MAX_NODES_PER_ROW);
      const colIndex = i % MAX_NODES_PER_ROW;
      const nodesInThisRow = Math.min(row.length - rowIndex * MAX_NODES_PER_ROW, MAX_NODES_PER_ROW);
      const rowWidth = nodesInThisRow * NODE_WIDTH + (nodesInThisRow - 1) * ROW_GAP;
      const centeredStartX = startX + (layerWidth - rowWidth) / 2;
      positions.set(task.id, {
        x: centeredStartX + colIndex * (NODE_WIDTH + ROW_GAP),
        y: currentY + rowIndex * (NODE_HEIGHT + ROW_GAP)
      });
    });

    currentY += layerHeight + COLUMN_GAP;
  }

  return visibleTasks.map((task) => ({
    task,
    x: positions.get(task.id)!.x,
    y: positions.get(task.id)!.y,
    depth: depths.get(task.id) ?? 0
  }));
}

function pathFor(from: { x: number; y: number }, to: { x: number; y: number }): string {
  const x1 = from.x + NODE_WIDTH;
  const y1 = from.y + NODE_HEIGHT / 2;
  const x2 = to.x;
  const y2 = to.y + NODE_HEIGHT / 2;
  const c1x = x1 + COLUMN_GAP / 2;
  const c2x = x2 - COLUMN_GAP / 2;
  return `M ${x1} ${y1} C ${c1x} ${y1}, ${c2x} ${y2}, ${x2} ${y2}`;
}

export function DagView({ tasks, selectedId, onSelect }: Props) {
  const tasksMap = useMemo(() => {
    const map = new Map<string, ReviewTask>();
    for (const task of tasks) map.set(task.id, task);
    return map;
  }, [tasks]);

  const leaves = useMemo(() => leafTasks(tasks), [tasks]);
  const chapters = useMemo(
    () => Array.from(new Set(leaves.map((t) => t.chapter).filter((c): c is number => c !== null))).sort((a, b) => a - b),
    [leaves]
  );

  const [scope, setScope] = useState<Scope>('chapter');
  const [chapterFilter, setChapterFilter] = useState<number>(() => {
    const selected = tasksMap.get(selectedId);
    return selected?.chapter ?? chapters[0] ?? 0;
  });

  useEffect(() => {
    if (scope === 'chapter') {
      const selected = tasksMap.get(selectedId);
      if (selected?.chapter !== null && selected?.chapter !== undefined) {
        setChapterFilter(selected.chapter);
      }
    }
  }, [selectedId, scope, tasksMap]);

  const visibleTasks = useMemo(() => {
    if (scope === 'all') return leaves;
    if (scope === 'chapter') return leaves.filter((t) => t.chapter === chapterFilter);

    // focus scope: selected node + ancestors + descendants up to 2 hops
    const selected = tasksMap.get(selectedId);
    if (!selected || selected.kind !== 'leaf') return leaves.slice(0, 20);

    const included = new Set<string>();
    included.add(selectedId);

    for (let i = 0; i < 2; i++) {
      const next = new Set<string>();
      for (const id of included) {
        const task = tasksMap.get(id);
        if (!task) continue;
        task.depends_on.forEach((dep) => { if (tasksMap.get(dep)?.kind === 'leaf') next.add(dep); });
        task.unlocks.forEach((down) => { if (tasksMap.get(down)?.kind === 'leaf') next.add(down); });
      }
      next.forEach((id) => included.add(id));
    }

    return leaves.filter((t) => included.has(t.id));
  }, [leaves, scope, chapterFilter, selectedId, tasksMap]);

  const nodes = useMemo(() => buildNodes(visibleTasks, tasksMap), [visibleTasks, tasksMap]);
  const nodeById = useMemo(() => {
    const map = new Map<string, DagNode>();
    for (const n of nodes) map.set(n.task.id, n);
    return map;
  }, [nodes]);

  const edges = useMemo(() => {
    const visibleIds = new Set(visibleTasks.map((t) => t.id));
    const result: { from: string; to: string }[] = [];
    const seen = new Set<string>();
    for (const task of visibleTasks) {
      for (const depId of task.depends_on) {
        if (!visibleIds.has(depId)) continue;
        const key = `${depId}->${task.id}`;
        if (seen.has(key)) continue;
        seen.add(key);
        result.push({ from: depId, to: task.id });
      }
    }
    return result;
  }, [visibleTasks]);

  const upstreamMap = useMemo(() => {
    const unlockers = new Map<string, string[]>();
    for (const task of visibleTasks) unlockers.set(task.id, []);
    for (const task of tasks) {
      for (const unlockedId of task.unlocks) {
        if (unlockers.has(unlockedId)) {
          unlockers.get(unlockedId)!.push(task.id);
        }
      }
    }

    const map = new Map<string, Set<string>>();
    for (const task of visibleTasks) {
      const upstream = new Set<string>();
      if (task.parent) upstream.add(task.parent);
      task.depends_on.forEach((id) => upstream.add(id));
      unlockers.get(task.id)!.forEach((id) => upstream.add(id));
      map.set(task.id, upstream);
    }
    return map;
  }, [visibleTasks, tasks]);

  const bounds = useMemo(() => {
    if (nodes.length === 0) return { width: 400, height: 300 };
    const maxX = Math.max(...nodes.map((n) => n.x + NODE_WIDTH));
    const maxY = Math.max(...nodes.map((n) => n.y + NODE_HEIGHT));
    return {
      width: Math.max(maxX + PADDING, 400),
      height: Math.max(maxY + PADDING, 300)
    };
  }, [nodes]);

  const [zoom, setZoom] = useState(1);
  const [pan, setPan] = useState({ x: 0, y: 0 });
  const dragRef = useRef<{ dragging: boolean; startX: number; startY: number; panX: number; panY: number } | null>(null);
  const svgRef = useRef<SVGSVGElement>(null);

  const resetView = () => {
    setZoom(1);
    setPan({ x: 0, y: 0 });
  };

  useEffect(() => {
    resetView();
  }, [scope, chapterFilter]);

  const handleWheel = (e: React.WheelEvent) => {
    e.preventDefault();
    const delta = e.deltaY > 0 ? 0.9 : 1.1;
    setZoom((z) => Math.min(Math.max(z * delta, 0.25), 3));
  };

  const handleMouseDown = (e: React.MouseEvent) => {
    if (e.target === svgRef.current || (e.target as Element).tagName === 'svg') {
      dragRef.current = {
        dragging: true,
        startX: e.clientX,
        startY: e.clientY,
        panX: pan.x,
        panY: pan.y
      };
    }
  };

  const handleMouseMove = (e: React.MouseEvent) => {
    if (!dragRef.current?.dragging) return;
    const dx = e.clientX - dragRef.current.startX;
    const dy = e.clientY - dragRef.current.startY;
    setPan({ x: dragRef.current.panX + dx, y: dragRef.current.panY + dy });
  };

  const handleMouseUp = () => {
    if (dragRef.current) dragRef.current.dragging = false;
  };

  const handleMouseLeave = () => {
    if (dragRef.current) dragRef.current.dragging = false;
  };

  const nodeCountInfo = `${visibleTasks.length} nodes · ${edges.length} edges`;

  return (
    <div className={styles.dagView}>
      <div className={styles.dagToolbar}>
        <div className={styles.dagScopeGroup}>
          <button
            type="button"
            className={scope === 'chapter' ? styles.dagScopeActive : ''}
            onClick={() => setScope('chapter')}
            aria-pressed={scope === 'chapter'}
          >
            Chapter
          </button>
          <button
            type="button"
            className={scope === 'focus' ? styles.dagScopeActive : ''}
            onClick={() => setScope('focus')}
            aria-pressed={scope === 'focus'}
          >
            Focus
          </button>
          <button
            type="button"
            className={scope === 'all' ? styles.dagScopeActive : ''}
            onClick={() => setScope('all')}
            aria-pressed={scope === 'all'}
          >
            All
          </button>
        </div>

        {scope === 'chapter' ? (
          <select
            className={styles.dagChapterSelect}
            value={chapterFilter}
            onChange={(e) => setChapterFilter(parseInt(e.target.value, 10))}
            aria-label="Filter by chapter"
          >
            {chapters.map((ch) => (
              <option key={ch} value={ch}>
                Chapter {ch}
              </option>
            ))}
          </select>
        ) : null}

        <span className={styles.dagMeta}>{nodeCountInfo}</span>

        <button
          type="button"
          className={styles.dagResetButton}
          onClick={resetView}
          aria-label="Reset DAG view"
        >
          Reset view
        </button>
      </div>

      {scope === 'all' && visibleTasks.length > 80 ? (
        <p className={styles.dagWarning}>
          Showing all {visibleTasks.length} leaf tasks. The graph may be dense; use Chapter or Focus
          mode for easier navigation.
        </p>
      ) : null}

      {visibleTasks.length === 0 ? (
        <p className={styles.emptyState}>No tasks match the current scope.</p>
      ) : (
        <>
          <div
            className={styles.dagCanvas}
            onWheel={handleWheel}
            onMouseDown={handleMouseDown}
            onMouseMove={handleMouseMove}
            onMouseUp={handleMouseUp}
            onMouseLeave={handleMouseLeave}
          >
            <svg
              ref={svgRef}
              width={bounds.width}
              height={bounds.height}
              viewBox={`0 0 ${bounds.width} ${bounds.height}`}
              style={{ transform: `translate(${pan.x}px, ${pan.y}px) scale(${zoom})`, transformOrigin: '0 0' }}
            >
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
                const fromNode = nodeById.get(edge.from);
                const toNode = nodeById.get(edge.to);
                if (!fromNode || !toNode) return null;
                const isSelected = selectedId === edge.to || selectedId === edge.from;
                return (
                  <path
                    key={`${edge.from}-${edge.to}`}
                    d={pathFor(fromNode, toNode)}
                    className={`${styles.dagEdge} ${isSelected ? styles.selectedDagEdge : ''}`}
                    markerEnd="url(#dag-arrow)"
                  />
                );
              })}

              {nodes.map((node) => {
                const isSelected = selectedId === node.task.id;
                const upstream = upstreamMap.get(node.task.id)!;
                const isDimmed = selectedId.length > 0 &&
                  selectedId !== node.task.id &&
                  !upstream.has(selectedId) &&
                  !node.task.depends_on.includes(selectedId) &&
                  !node.task.unlocks.includes(selectedId);

                return (
                  <g
                    key={node.task.id}
                    transform={`translate(${node.x}, ${node.y})`}
                    className={`${styles.dagNode} ${isSelected ? styles.selectedDagNode : ''} ${isDimmed ? styles.dimmedDagNode : ''}`}
                    onClick={() => onSelect(node.task.id)}
                    role="button"
                    tabIndex={0}
                    aria-label={`${node.task.id}: ${node.task.title}`}
                    aria-pressed={isSelected}
                    onKeyDown={(e) => {
                      if (e.key === 'Enter' || e.key === ' ') {
                        e.preventDefault();
                        onSelect(node.task.id);
                      }
                    }}
                  >
                    <rect width={NODE_WIDTH} height={NODE_HEIGHT} rx={6} ry={6} />
                    <foreignObject x={6} y={5} width={NODE_WIDTH - 12} height={NODE_HEIGHT - 10}>
                      <div className={styles.dagNodeContent}>
                        <strong title={node.task.id}>{node.task.id}</strong>
                        <span title={node.task.title}>{node.task.title}</span>
                      </div>
                    </foreignObject>
                  </g>
                );
              })}
            </svg>
          </div>

          <div className={styles.dagLegend}>
            <span>
              <span className={styles.dagLegendDot} /> Selected
            </span>
            <span>
              <span className={`${styles.dagLegendDot} ${styles.dagLegendUpstream}`} /> Upstream / downstream
            </span>
            <span>
              <span className={`${styles.dagLegendDot} ${styles.dagLegendOther}`} /> Other
            </span>
            <span className={styles.dagHint}>Scroll to zoom · drag background to pan</span>
          </div>
        </>
      )}
    </div>
  );
}
