---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ [CompleteSpace E] {H : Type u_2}\n  [inst_3 : TopologicalSpace H] {I : ModelWithCorners\
  \ ℝ E H} {M : Type u_3} [inst_4 : TopologicalSpace M]\n  [inst_5 : ChartedSpace\
  \ H M] [inst_6 : IsManifold I (↑⊤) M] {f : M → ℝ}\n  (hf : ContMDiff I (modelWithCornersSelf\
  \ ℝ ℝ) (↑⊤) f) (X Z : Riemannian.SmoothVectorField I M) (p : M),\n  Riemannian.DCLieBracket\
  \ X (Riemannian.SmoothVectorField.smul f hf Z) p =\n    X.dir f p • Z.toFun p +\
  \ f p • Riemannian.DCLieBracket X Z p"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 376
name: Riemannian.DCLieBracket_smul_right
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- 5fb60bebadcc
sort: theorem
source: lean
state: proven
title: DCLieBracket_smul_right
---
