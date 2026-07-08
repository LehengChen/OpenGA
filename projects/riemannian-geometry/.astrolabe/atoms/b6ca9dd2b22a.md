---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_4} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (self : Riemannian.AffineConnection I M) (X Y Z : Riemannian.SmoothVectorField\
  \ I M),\n  self.cov X (Y + Z) = self.cov X Y + self.cov X Z"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 153
name: Riemannian.AffineConnection.add_right
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- b6ca9dd2b22a
sort: theorem
source: lean
state: proven
title: add_right
---
