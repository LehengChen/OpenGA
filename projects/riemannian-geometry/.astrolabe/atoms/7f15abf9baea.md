---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M) (Y Z : Riemannian.SmoothVectorField\
  \ I M) (p : M),\n  (MDiffAt fun q => g.metricInner q (Y.toFun q) (Z.toFun q)) p"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 365
name: Riemannian.RiemannianMetric.metricInner_field_mdifferentiableAt
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- 7f15abf9baea
sort: theorem
source: lean
state: proven
title: metricInner_field_mdifferentiableAt
---
