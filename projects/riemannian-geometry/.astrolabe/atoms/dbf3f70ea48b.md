---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {G\
  \ : Type u_7} [inst_3 : Group G] [inst_4 : TopologicalSpace G]\n  [inst_5 : ChartedSpace\
  \ H G] [inst_6 : LieGroup I (↑⊤) G] (b : E →L[ℝ] E →L[ℝ] ℝ),\n  ContMDiff I (I.prod\
  \ (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) ↑⊤ fun x => ⟨x, Riemannian.DCLeftInvariantForm\
  \ b x⟩"
file: Riemannian/Manifold/DoCarmoCh1.lean
line: 567
name: Riemannian.DCLeftInvariantForm_contMDiff
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean
ref:
- dbf3f70ea48b
sort: theorem
source: lean
state: proven
title: DCLeftInvariantForm_contMDiff
---
