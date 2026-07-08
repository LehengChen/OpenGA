---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {M\
  \ : Type u_3} [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M]\n  [inst_5\
  \ : IsManifold I (↑⊤) M] (X : Riemannian.SmoothVectorField I M) {f h : M → ℝ} (p\
  \ : M),\n  MDiffAt f p → MDiffAt h p → X.dir (fun q => f q * h q) p = f p * X.dir\
  \ h p + h p * X.dir f p"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 353
name: Riemannian.SmoothVectorField.dir_mul
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- 1f7af3efca4a
sort: theorem
source: lean
state: proven
title: dir_mul
---
