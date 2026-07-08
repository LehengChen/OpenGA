---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [inst_2 : CompleteSpace E] {H : Type u_2}\n  [inst_3 : TopologicalSpace H] {I\
  \ : ModelWithCorners ℝ E H} {M : Type u_3} [inst_4 : TopologicalSpace M]\n  [inst_5\
  \ : ChartedSpace H M] [inst_6 : IsManifold I (↑⊤) M] [inst_7 : FiniteDimensional\
  \ ℝ E]\n  (g : Riemannian.RiemannianMetric I M) (X Y Z : Riemannian.SmoothVectorField\
  \ I M) (p : M),\n  (g.koszulCovec X Y p) (Z.toFun p) = g.koszulRHS X Y Z p"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 711
name: Riemannian.RiemannianMetric.koszulCovec_apply
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- fa78a4ba27cd
sort: theorem
source: lean
state: proven
title: koszulCovec_apply
---
