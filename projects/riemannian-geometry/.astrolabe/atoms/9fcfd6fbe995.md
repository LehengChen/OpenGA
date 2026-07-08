---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] (f : M →\
  \ ℝ)\n  (Z : (y : M) → TangentSpace I y) (q : M),\n  Riemannian.DCApply f Z q =\
  \ (NormedSpace.fromTangentSpace (f q)) ((mfderiv% f q) (Z q))"
file: Riemannian/Manifold/DoCarmoCh0.lean
line: 0
name: Riemannian.DCApply.eq_1
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh0.lean
ref:
- 9fcfd6fbe995
sort: theorem
source: lean
state: proven
title: eq_1
---
