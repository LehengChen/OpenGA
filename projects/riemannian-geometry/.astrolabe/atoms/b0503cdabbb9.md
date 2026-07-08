---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {G\
  \ : Type u_7} [inst_3 : Group G] [inst_4 : TopologicalSpace G]\n  [inst_5 : ChartedSpace\
  \ H G] [LieGroup I (↑⊤) G] (b : E →L[ℝ] E →L[ℝ] ℝ),\n  (∀ (u : E), u ≠ 0 → 0 < (b\
  \ u) u) →\n    ∀ (x : G) (u : TangentSpace I x), u ≠ 0 → 0 < ((Riemannian.DCLeftInvariantForm\
  \ b x) u) u"
file: Riemannian/Manifold/DoCarmoCh1.lean
line: 557
name: Riemannian.DCLeftInvariantForm_pos
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean
ref:
- b0503cdabbb9
sort: theorem
source: lean
state: proven
title: DCLeftInvariantForm_pos
---
