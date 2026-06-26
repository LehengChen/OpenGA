/**
 * Decoupling invariants — the two workspace "spec theorems".
 *
 * Source-level fitness functions: any change that breaks a theorem fails CI.
 * Prose statements + rationale: ../workspace/INVARIANTS.md
 *
 *   Theorem 1 (Container–Content): switching layout/view never unmounts a view;
 *             view internals are independent of container position.
 *   Theorem 2 (Selection–Document): selecting a hash only updates the card
 *             window (Detail); it never moves the main document.
 */
import { describe, it, expect } from 'vitest'
import * as fs from 'fs'

const ws = fs.readFileSync('src/panels/workspace/WorkspacePanel.tsx', 'utf-8')
const rv = fs.readFileSync('src/panels/workspace/ReadView.tsx', 'utf-8')
const dv = fs.readFileSync('src/panels/workspace/DetailView.tsx', 'utf-8')

describe('Theorem 1 — 切换容器不影响视图内部 (keep-alive)', () => {
    it('每个视图在 JSX 中只挂载一次', () => {
        expect(ws.match(/<ReadView\s*\/>/g)).toHaveLength(1)
        expect(ws.match(/<NetworkView\s*\/>/g)).toHaveLength(1)
        expect(ws.match(/<DetailView\s*\/>/g)).toHaveLength(1)
    })

    it('视图通过 portal 挂载一次（位置在 React 树中固定）', () => {
        expect(ws).toContain('createPortal')
    })

    it('容器是稳定 DOM 节点（命令式创建，React 不会重建）', () => {
        expect(ws).toContain('document.createElement')
    })

    it('布局切换靠搬运 DOM 节点（appendChild），而非重挂', () => {
        expect(ws).toContain('appendChild')
    })
})

describe('Theorem 2 — 选中 hash 只改卡片窗口，不动主文档', () => {
    it('主文档(ReadView)不依赖选中态（selection-agnostic）', () => {
        expect(rv).not.toContain('selectObjStore')
    })

    it('全工作区禁止 scrollIntoView（会连带滚动 window/容器）', () => {
        expect(rv).not.toContain('.scrollIntoView(')
        expect(ws).not.toContain('.scrollIntoView(')
    })

    it('卡片窗口(DetailView)才是选中的唯一接收方', () => {
        expect(dv).toContain('selectedHash')
    })
})
