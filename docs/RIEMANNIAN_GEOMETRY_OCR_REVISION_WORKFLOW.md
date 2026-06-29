# Riemannian Geometry OCR Revision Workflow

This document defines the working rules for revising
`projects/riemannian-geometry/.astrolabe` from the Markdown extracted from the
newer OCR archive `doCarmo-RiemannianGeometry-20260628093607.zip`. In this
review run, the extracted Markdown was staged outside the repository at
`/tmp/docarmo-ocr-review/doCarmo-RiemannianGeometry.md`; the zip archive is an
input artifact and should not be committed.

The goal is correction of the existing Astrolabe content, not expansion of scope.
The existing do Carmo `dcref` identities are the authority for what belongs in
the current graph.

## Scope

- Revise existing do Carmo text atoms and chapter docs.
- Preserve the current set of do Carmo `dcref` entries unless an explicit review
  decision says otherwise.
- Preserve Lean atoms, Lean edges, Lean-to-tex `formalizes` edges, and manual
  concept edges.
- Do not import exercises, prefaces, references, or index content in the first
  large run.
- Do not commit during this workflow unless the user explicitly asks for a git
  commit.

## Data Model Rules

- `docs-src/*.mdx` is the human-readable source for do Carmo chapter text.
- `docs/*.mdx` is the rendered/readable Astrolabe document layer using
  `\entryblock{...}` and `\entryref{...}`.
- `atoms/*.md` stores atom records. Existing do Carmo atoms are keyed by stable
  identity:

```json
{"source":"tex","src":"docarmo","dcref":"chN:S.I"}
```

- `edges/*.md` stores relations. Automatically regenerated do Carmo-to-do Carmo
  edges may be rebuilt, but cross-source and manual edges must be preserved.
- A text change to an atom must not accidentally change its identity. If a tool
  computes a different hash for the same `dcref`, the tool is wrong for this
  workflow unless the whole reference graph is intentionally migrated.

## Roles

### Orchestrator

The main agent owns all writes to the canonical `.astrolabe` store.

Responsibilities:

- Parse the OCR Markdown into chapter/section/statement chunks.
- Maintain the `dcref -> existing hash` map.
- Merge approved candidate text into `docs-src`.
- Regenerate or update `docs`, do Carmo atoms, and do Carmo internal edges.
- Preserve non-do Carmo tex nodes, Lean nodes, Lean edges, cross-source bridges,
  and manual concept edges.
- Run validation and summarize unresolved risks.

### Worker Agents

Worker agents may revise bounded chapter ranges or small statement sets.

Rules:

- Each worker must have a disjoint write scope.
- Workers must not edit canonical `.astrolabe/atoms` or `.astrolabe/edges`
  directly unless the orchestrator explicitly gives a single-file repair task.
- Workers should output candidate changes plus a concise rationale:
  - affected `dcref` values,
  - OCR passages used,
  - formulas checked,
  - cross-references checked,
  - suspected OCR artifacts not adopted.
- Workers must not revert unrelated changes.

### Reviewer Agents

Reviewer agents are read-only by default. They compare candidate text against
the OCR source and existing Astrolabe text.

Preferred reviewer output is structured JSON:

```json
{
  "missing_dcref": [],
  "extra_dcref": [],
  "dropped_paragraph": [],
  "formula_mismatch": [],
  "unresolved_reference": [],
  "bad_ocr_artifact": [],
  "recommendation": "accept|revise|reject"
}
```

Reviewers may use prose after the JSON, but the JSON is the artifact consumed by
the orchestrator.

Reviewer findings are advisory, not automatic edits. In particular,
`dropped_paragraph` findings must be triaged by the orchestrator as one of:

- **error**: lost mathematical content or an undefined symbol;
- **acceptable compression**: existing text is faithful enough for the current
  Astrolabe style;
- **scope expansion**: useful for a fuller transcription pass, but outside a
  correction-only run.

## Revision Procedure

1. Snapshot the worktree status and validate the current store.
2. Extract the OCR Markdown to a temporary location outside git-tracked paths.
3. Build a full-chapter OCR statement index keyed by `chN:S.I`.
4. Compare OCR keys with existing do Carmo atom `dcref` keys.
5. For a small test, select a narrow statement set and produce candidate
   `docs-src` edits only.
6. Run at least one independent review on the candidate.
7. Merge accepted candidates into `docs-src`.
8. Regenerate/update dependent Astrolabe layers using the stable `dcref` map.
9. Validate:
   - store well-formedness,
   - all existing do Carmo `dcref` keys still present,
   - no dangling `\entryref{...}`,
   - Lean-to-tex `formalizes` edge count unchanged unless intentionally edited,
   - an independent custom audit, or an explicitly reviewed project validator,
     reports no structural regressions.
10. Inspect `git diff --stat` and sample diffs before expanding scope.

## Tooling Rules

- During OCR workflow tests, do not rely on existing repository extraction or
  audit tools. Use purpose-built one-off checks or agent review.
- Existing tools may be read to understand the data model, but they are not an
  authority for the OCR correction run until explicitly adapted and reviewed.
- Headless Codex review must not run with write access to the canonical repo.
  If read-only sandboxing is unavailable, create a minimal temporary package
  under `/tmp` containing only the OCR zip and the target chapter file, then run
  headless review there.
- The temporary headless package must not contain `tools/`.

## Chunk Boundary Rules

- Even for a tiny sample, parse the whole chapter first and use the next
  numbered heading as the end boundary.
- Do not delimit a local sample by matching only the sample headings. That can
  cause the final sample item to swallow later statements.
- Chapter body markers must be found after the front matter and table of
  contents, and the chosen chapter starts must be monotonically increasing.
  Some body chapter titles have no Markdown `##` prefix, e.g. Chapter 10
  `THE RAUCH COMPARISON THEOREM` and Chapter 12
  `THE FUNDAMENTAL GROUP OF MANIFOLDS OF NEGATIVE CURVATURE`; the table of
  contents contains the same strings and must not be accepted as a body start.
- A bare chapter-title candidate should be accepted only when nearby following
  lines look like body content, e.g. `## 1. Introduction`. Directory entries like
  `CHAPTER 10-THE RAUCH COMPARISON THEOREM 210` followed by `§1. Introduction
  210` are table-of-contents lines, not body starts.
- OCR headings can be glued to the previous sentence, e.g.
  `... in the following way. 2.5 Proposition.`; heading detection must handle
  this form.
- OCR headings can contain punctuation variants, e.g. `2.7. Corollary`.
- OCR headings can use a named-heading form where the kind word is not
  immediately after the number, e.g. `2.2 Index Theorem. (Morse).`; accept a
  short title ending in `Theorem`, `Proposition`, `Lemma`, `Corollary`,
  `Definition`, `Example`, or `Remark`.
- OCR headings can contain prime suffixes, e.g. `\( {2.6}^{\prime} \) REMARK`
  or `2.6′ Remark`. Prime-suffixed headings are valid chunk boundaries, but in
  correction-only runs they must not create new `dcref`/atom entries unless the
  existing store already has that `dcref` or an explicit review decision expands
  the scope.
- Existing synthetic `dcref` chunks must be preserved even when the OCR text has
  no explicit numbered heading. Example: current `ch8:5.4` packages the
  unnumbered Chapter 8 closing discussion of the ball model, horospheres, and
  hyperspheres after Theorem 5.3 and before `EXERCISES`; correction-only runs
  should revise this chunk, not delete it or require OCR to contain a literal
  `5.4` heading.
- Transitional prose between two numbered statements belongs in the chapter doc
  outside atom bodies unless it is clearly part of a statement or proof.
- OCR headings may appear as `2.1 Definition.`, while `docs-src` headings use
  `### 2.1 Definition (...)`; parsers must support both forms.
- A no-change decision is valid when the existing Astrolabe text is already a
  faithful correction of noisy OCR.
- OCR page headers and footers, such as `sec. 2] ... 147`, are never content.

## Acceptance Criteria

For each revised statement:

- The statement keeps the same `dcref`.
- The kind and title still match the intended do Carmo item.
- Mathematical formulas are not dropped.
- Equation labels and explicit references remain readable.
- Existing `\entryref{...}` links are preserved or correctly regenerated.
- Obvious OCR artifacts are corrected rather than copied.
- No unrelated Lean or non-do Carmo graph content changes.

## Risk Tiers

### Low-Risk Automatic Candidates

These may be proposed by workers and accepted after one independent review:

- short definitions whose symbols are all bound;
- short examples with no proof;
- text-only corrections of obvious OCR noise;
- preservation of existing `\entryref` targets where the target `dcref` is clear.

### Human-Review Required

These require explicit orchestrator review, usually with a second reviewer:

- long proofs;
- proofs using local existence or domain-of-definition hypotheses;
- statements with boundary cases such as `v=0`;
- multi-equivalence theorems;
- statements with nonstandard numbering or inserted prime headings;
- any item where a reviewer reports a formula or condition mismatch.

For multi-equivalence theorems, reviewers must list the proof directions present
in both OCR and current text. Example: Hopf-Rinow `ch7:2.8` should preserve
`a=>f`, `a=>b`, `b=>c`, `c=>d`, `d=>a`, and `b<=>e`; item `f` is an additional
consequence, not one of the equivalent assertions.

## Stop Conditions

Stop and discuss before large-scale execution if any of these occur:

- OCR parsing cannot reliably recover chapter boundaries.
- A chapter has missing or duplicate `dcref` keys.
- A generated update would delete Lean-to-tex bridges.
- `validate_store` fails after a controlled regeneration.
- Reviewers disagree on whether a candidate dropped mathematical content.
- A validation or extraction tool still has a hard-coded project path that does
  not exist in the current workspace.

## Small-Test Protocol

Use a sample with limited blast radius before any full run.

Recommended first sample:

- Chapter 1, statements `ch1:2.1`, `ch1:2.2`, and `ch1:2.3`.

The sample is small enough to review manually, but includes a definition, an
equation label, and a cross-reference target used elsewhere in the graph.

Expected test outputs:

- a refined workflow note,
- candidate edits or a decision to postpone edits,
- validation output,
- a list of changes needed before the large run.

## First Sample Lessons

The first sample (`ch1:2.1`-`ch1:2.3`) established these local policies:

- Undefined mathematical symbols are correction targets. Example: `ch1:2.1`
  used `q` in the displayed metric formula without first binding
  `q=\mathbf{x}(x_1,\dots,x_n)`.
- Parenthetical explanations that are omitted only because the current text is
  compressed are not automatically correction targets. Example: `ch1:2.2`
  omits do Carmo's parenthetical explanation of "diffeomorphism"; this is not a
  blocking mathematical error.
- When OCR notation is mathematically ambiguous, prefer a cleaned expression
  that matches the intended meaning over copying the OCR artifact verbatim.

The second test batch established these policies:

- Existing atom-level `\entryref` links must be preserved even when `docs-src`
  keeps the corresponding source text as plain prose. Example: `ch1:2.5`
  references Definition 2.1 in the atom layer.
- Long examples can still be acceptable if the current compressed text preserves
  the definitions, formulas, and referenced results. Example: `ch1:2.6` preserves
  formulas `(2)` and `(3)` and the Chapter 0 Proposition 5.4 reference.
- Some proof compressions are mathematical risks, not OCR noise. Example:
  domain conditions for expressions such as `\exp_p(t v(s))` should be restored
  only after checking the OCR statement boundary and leaving the surrounding proof
  structure unchanged.
- Prime-suffixed headings such as `ch13:2.6′` are boundary markers in the text,
  but do not become new atoms during correction-only runs.
- Headless review is useful, but sandbox behavior must be tested first. If
  read-only sandboxing fails, use a `/tmp` minimal package with no repo tools.

The third boundary test established these policies:

- Full-chapter coverage should be tested against three sets: current do Carmo
  atoms, current `docs-src` headings, and OCR-detected headings. With the
  current detector, all chapters match except the expected synthetic
  `ch8:5.4` exception.
- The detector must include fixture cases for Chapter 10 and Chapter 12 body
  titles without `##`; otherwise Chapter 10 can be swallowed by Chapter 9 and
  Chapter 12 can be swallowed by Chapter 11.
- The detector must reject the corresponding Chapter 10 and Chapter 12
  table-of-contents lines, which contain the same title strings plus page
  numbers.
- The detector must include a fixture for `ch11:2.2 Index Theorem. (Morse).`,
  because requiring the kind word immediately after the number misses named
  theorem headings.
- The detector must include a fixture for `ch13:2.6′`, because prime headings
  are real boundaries but not new atoms in correction-only mode.
- Synthetic existing `dcref` values can be valid even when OCR has no literal
  numbered heading. Headless review accepted preserving `ch8:5.4` for the
  unnumbered Chapter 8 closing discussion after Theorem 5.3 and before
  `EXERCISES`.
- When OCR writes `\sum` but the symbol is clearly a named hypersurface variable,
  normalize it to `\Sigma` rather than copying the OCR artifact.
- `EXERCISES` is a hard end boundary for the first correction-only run; exercise
  text can justify a reference but should not be imported as atoms in this pass.

The first chapter-level batch trial established these policies:

- Proof-end markers are semantic boundaries. If OCR states that a following
  characterization is not proved, do not let a proof marker imply otherwise.
  Example: in `ch1:2.6`, the proof of (3) ends before the characterization of
  bi-invariant metrics.
- Transitional source material must stay in source order even when it is not an
  atom. Example: the oriented-volume construction with equations (4) and (5)
  belongs between `ch1:2.10` and `ch1:2.11`, because `ch1:2.11` refers back to
  those equations.
- Partition-of-unity arguments should preserve support hypotheses precisely
  enough that local metrics are not evaluated outside their coordinate
  neighborhoods.
- Ambiguous but nonblocking source notation should be queued for human review
  rather than rewritten automatically. Examples from Chapter 1: the meaning of
  `x_t^{-1}(e)` in the Lie-group example, and the Jacobian direction in equation
  (4) of the oriented-volume construction.

The first wider batch trial (`ch2`, `ch4`, `ch6`) established these policies:

- Variables introduced only in OCR proof text should be restored when the
  current text uses them without binding. Example: `ch2:2.6` must introduce
  `t_1\in I` before using `c([t_0,t_1])`.
- Delayed proofs that cross numbered atom boundaries are structural cases, not
  automatic text moves. Example: OCR places the proof of `ch2:2.2` after
  Remark 2.4; changing this faithfully requires a reviewed atom/rendering
  strategy rather than simply moving text inside one atom.
- Local moving frames should live on their local domain. Example: in `ch4:5.1`,
  write `E_i\in\mathcal{X}(U)`, not `\mathcal{X}(M^n)`.
- Operator trace conditions should not make the zero-operator statement look
  like the object being traced. Example: in `ch6:2.10`, write that the trace of
  `S_\eta` is zero.
- In codimension one, `\nabla_X^\perp\eta=0` is automatic only for a local unit
  normal field. State that hypothesis when deriving the hypersurface Codazzi
  formula, and keep tensor covariant-derivative notation parenthesized as
  `(\overline{\nabla}_X B)(Y,Z,\eta)`.

The second wider batch trial (`ch0`, `ch5`) established these policies:

- Explanatory dimension equalities should not be placed inside a rendered
  exponent. Example: replace `\mathbb{R}^{n=m+k}` with a clean target such as
  `\mathbb{R}^{m+k}` when the surrounding text already states `n=m+k`.
- Set notation involving named points should use a set of points, not a union
  expression. Example: write `S^n-\{N,S\}`, not `S^n-\{N\cup S\}`.
- Group actions should name the acting element or otherwise avoid writing the
  group itself as if it were one map. Example: for the integral translations of
  `\mathbb{R}^k`, say that the translation corresponding to
  `(n_1,\dots,n_k)\in\mathbb{Z}^k` sends `x_i` to `x_i+n_i`.
- When a symbol has had a local meaning earlier, redefine it if the new atom
  uses a broader meaning. Example: in `ch0:5.1`, define `\mathcal{D}` and
  `\mathcal{F}` before viewing a vector field as
  `X:\mathcal{D}\to\mathcal{F}`.
- Smooth bump formulas with denominator factors that vanish at endpoints should
  state the open support interval and zero elsewhere. Example: define
  `\alpha(t)=\exp(-1/((t+2)(-1-t)))` for `-2<t<-1`, zero otherwise.
- Atom-local symbol binding remains a correction target even when the chapter
  context makes the symbol clear. Example: `ch5:2.5` should bind
  `p=\gamma(0)` before using `\exp_p`.

The third wider batch trial (`ch3`, `ch7`) established these policies:

- In do Carmo's local-coordinate convention, a coordinate system may be written as
  `\mathbf{x}:U\subset\mathbb{R}^n\to M`. Therefore expressions such as
  `q\in\mathbf{x}(U)` or `V\subset\mathbf{x}(U)` are not automatic type errors;
  reviewers must check the local convention before rewriting them.
- Rendered `docs/*.mdx` can contain wrong `\entryref` targets even when
  `docs-src` prose is correct. Cross-reference repairs are low risk only when the
  intended `dcref` target is uniquely identified.
- Empty-set OCR artifacts should be normalized. Example: `C(p)=\phi` in the
  conjugate-locus statement should be `C(p)=\varnothing`.
- Definitions used immediately by a following lemma should not be compressed past
  symbol binding. Example: the Chapter 3 parametrized-surface definition should
  define vector fields along a surface and the covariant derivatives
  `DV/\partial u`, `DV/\partial v`.
- Exponential-map examples and proofs should preserve domain-of-definition
  clauses when a manifold is incomplete or the proof builds a two-parameter
  surface.
- Parametrization changes that affect whether a curve is itself a geodesic or only
  the image of a geodesic are proof-sensitive and stay in human review.

The fourth wider batch trial (`ch8`, `ch9`, `ch10`) established these policies:

- Type-level phrasing such as "basis in a tangent space" should be cleaned when the
  current Markdown turns it into a false membership assertion. Example:
  `orthonormal bases \{e_j\} of T_pM`, not `\{e_j\}\in T_pM`.
- Quotient metrics should bind the chosen lift and state independence of the lift
  when the displayed formula uses `d\pi^{-1}`. This is a definition, not an
  optional explanatory aside.
- Named axioms introduced in source prose should not be reduced to only a name
  when their content is used immediately. Example: restore the Axiom of free
  mobility before invoking side-angle-side and constant curvature.
- Mathematical OCR can preserve a typo from the scan. If a sentence is ill-typed
  but the intended object is unique, it may be corrected. Example: hyperplanes
  `P` and `h(P)` are tangent at the point `p`, not at `P`.
- Piecewise differentiability hypotheses should be kept local to the intervals on
  which derivatives are taken. Example: index-form derivative identities hold on
  each interval where `V` is differentiable.
- Wrong `\entryref` targets inside atoms are correction targets even when the
  visible prose names the right chapter. Example: a reference to "Example 2.7,
  Chap. 1" should point to the Chapter 1 flat torus atom, not a Chapter 10 remark.
- Bibliographic paragraphs in the non-exercise chapter body may be restored when
  they are bounded and do not alter theorem/proof content. Keep proof-sensitive
  variable repairs separate.

The final chapter batch trial (`ch11`, `ch12`, `ch13`) established these policies:

- OCR confusions between the letter `o` and the digit `0` are low-risk only when
  the surrounding indexing pattern fixes the intended symbol. Examples:
  `h_0=\mathrm{ident.}` in a homotopy `h_s`, and `H=H_0\supset H_1\supset\cdots`
  in a subgroup series.
- Cross-chapter `\entryref` repairs must be checked by target `dcref`, not by
  visible statement number alone. Chapter 13 had several links whose prose named
  Chapter 10 or 11 while the hash pointed to a same-numbered Chapter 13 atom.
- Interstitial definitions needed by a following numbered statement belong in
  `docs-src` and `docs` outside the atom body. Example: the Morse-theory
  definitions before `ch13:3.3` should be restored without creating a new atom.
- Bounded bibliographic details remain low-risk when they do not affect theorem
  content. Example: the full Eberlein survey citation in `ch12:3.11`.
- Constants, inequalities, and proof quantifiers in comparison-geometry or group
  theory arguments are human-review items even when the OCR looks suggestive.
  Examples: the energy inequality in `ch11:2.9`, the `\pi/(2\sqrt\delta)` radius
  convention in `ch13:4.2`, and nonidentity/finite-index assumptions in
  `ch12:3.10`.

The human-queue reduction pass established these refinements:

- Items originally marked human-review can be promoted to low-risk edits after a
  second independent OCR/headless review when the correction is local and
  type-forced. Examples: `\mathrm{Ad}((x_t(e))^{-1})` in `ch1:2.6`,
  `\tilde\gamma` in the final formula of `ch12:2.6`, and
  `\langle\tilde J(0),\tilde\gamma'(0)\rangle` in `ch10:4.9`.
- A source typo may be corrected when the current text is mathematically
  ill-typed and the intended object is uniquely fixed by the surrounding proof.
  This applied to the Jacobian direction in the oriented-volume construction
  before `ch1:2.11`.
- Ambiguous OCR parentheticals should be expanded into explicit prose rather than
  retained in compressed notation. This applied to the strict-inequality clauses
  in `ch12:3.1`.
- Proof-structure repairs that add missing hypotheses or extra cases remain human
  review until they receive independent subagent analysis and headless arbitration.
  This was the policy used before closing the `ch12:3.10`
  subgroup-series/finite-index issues.
- Some queue items require no edit after review. Example: `ch12:2.1` keeps the
  OCR/current one-direction definition of free homotopy class; no maximality or
  if-and-only-if clause was added.

The final queue-closure pass established these refinements:

- Atom-centric rendering may intentionally keep a proof attached to its
  proposition even when the printed/OCR page delays the proof past intervening
  remarks. Example: `ch2:2.2` stays unchanged; the delayed printed location is a
  rendering-policy issue, not a content correction.
- Local domain clauses may be added when a proof uses an inverse exponential map
  on a compact family of nearby geodesics. Example: `ch3:4.1` shrinks the totally
  normal neighborhood and the geodesic-flow interval before defining
  `u=\exp_p^{-1}(\gamma(t,q,v))`.
- Source/OCR formulas may be corrected when the surrounding proof uniquely fixes
  a missing scale factor. Example: in `ch5:2.4`, the curve in
  `T_{\gamma(0)}M` must satisfy `v'(0)=aw` because
  `f(t,s)=\exp_p((t/a)v(s))` and the proof uses
  `(d\exp_p)_{tv}(tw)`.
- In dimension two, conformal/isometry classifications must distinguish the
  orientation-preserving Mobius maps from the orientation-reversing
  anti-holomorphic maps. Example: in `ch8:5.3`, formula (12) uses
  `ad-bc>0`, with the remaining isometries obtained by composing with
  `z\mapsto-\bar z`.
- Printed/OCR mathematical typos may be repaired when the theorem statement is
  otherwise impossible. Examples: `ch11:2.9` states local minimality as
  `E(0)\leq E(s)`, and `ch13:4.2` writes the radius as
  `\pi/(2\sqrt\delta)`.
- Proof-structure repairs can be applied after arbitration when they only make
  hypotheses already required by earlier lemmas explicit. Example: `ch12:3.10`
  now makes the nontrivial subgroup, nonidentity element, and finite-index power
  arguments explicit before invoking uniqueness of the invariant geodesic.

## Current Human Review Queue

No open items after the final queue-closure pass.
