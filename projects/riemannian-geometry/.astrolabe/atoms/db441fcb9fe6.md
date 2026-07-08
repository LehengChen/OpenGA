---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [CompleteSpace E] {H : Type u_2}\n  [inst_3 : TopologicalSpace H] {I : ModelWithCorners\
  \ ℝ E H} {M : Type u_3} [inst_4 : TopologicalSpace M]\n  [inst_5 : ChartedSpace\
  \ H M] [inst_6 : IsManifold I (↑⊤) M] (g : Riemannian.RiemannianMetric I M)\n  (X\
  \ Y Z₁ Z₂ : Riemannian.SmoothVectorField I M) (p : M),\n  g.koszulRHS X Y (Z₁ +\
  \ Z₂) p = g.koszulRHS X Y Z₁ p + g.koszulRHS X Y Z₂ p"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 451
name: Riemannian.RiemannianMetric.koszulRHS_add_right
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- db441fcb9fe6
sort: theorem
source: lean
state: proven
title: koszulRHS_add_right
---
