---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (X Y Z : Riemannian.SmoothVectorField\
  \ I M)\n  (p : M), g.koszulRHS Y X Z p - g.koszulRHS X Y Z p = 2 * g.metricInner\
  \ p (Riemannian.DCLieBracket X Y p) (Z.toFun p)"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 773
name: Riemannian.RiemannianMetric.koszulRHS_antisymm_diff
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- fbfe23fbc087
sort: theorem
source: lean
state: proven
title: koszulRHS_antisymm_diff
---
