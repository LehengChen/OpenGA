---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (X : Riemannian.SmoothVectorField I M) {F : M → ℝ},\n \
  \ ContMDiff I (modelWithCornersSelf ℝ ℝ) (↑⊤) F → ContMDiff I (modelWithCornersSelf\
  \ ℝ ℝ) (↑⊤) (X.dir F)"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 940
name: Riemannian.SmoothVectorField.dir_contMDiff
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- 56fd4cba0ab0
sort: theorem
source: lean
state: proven
title: dir_contMDiff
---
