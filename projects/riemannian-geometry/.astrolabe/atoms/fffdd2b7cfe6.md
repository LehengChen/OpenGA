---
content: "{E : Type u_1} →\n  [inst : NormedAddCommGroup E] →\n    [inst_1 : NormedSpace\
  \ ℝ E] →\n      {H : Type u_2} →\n        [inst_2 : TopologicalSpace H] →\n    \
  \      {I : ModelWithCorners ℝ E H} →\n            {M : Type u_4} →\n          \
  \    [inst_3 : TopologicalSpace M] →\n                [inst_4 : ChartedSpace H M]\
  \ →\n                  [inst_5 : IsManifold I (↑⊤) M] →\n                    (cov\
  \ :\n                        Riemannian.SmoothVectorField I M →\n              \
  \            Riemannian.SmoothVectorField I M → Riemannian.SmoothVectorField I M)\
  \ →\n                      (∀ (X Y Z : Riemannian.SmoothVectorField I M), cov (X\
  \ + Y) Z = cov X Z + cov Y Z) →\n                        (∀ (f : M → ℝ) (hf : ContMDiff\
  \ I (modelWithCornersSelf ℝ ℝ) (↑⊤) f)\n                            (X Z : Riemannian.SmoothVectorField\
  \ I M),\n                            cov (Riemannian.SmoothVectorField.smul f hf\
  \ X) Z =\n                              Riemannian.SmoothVectorField.smul f hf (cov\
  \ X Z)) →\n                          (∀ (X Y Z : Riemannian.SmoothVectorField I\
  \ M), cov X (Y + Z) = cov X Y + cov X Z) →\n                            (∀ (f :\
  \ M → ℝ) (hf : ContMDiff I (modelWithCornersSelf ℝ ℝ) (↑⊤) f)\n                \
  \                (X Y : Riemannian.SmoothVectorField I M) (p : M),\n           \
  \                     (cov X (Riemannian.SmoothVectorField.smul f hf Y)).toFun p\
  \ =\n                                  f p • (cov X Y).toFun p + X.dir f p • Y.toFun\
  \ p) →\n                              Riemannian.AffineConnection I M"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 142
name: Riemannian.AffineConnection.mk
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- fffdd2b7cfe6
sort: other
source: lean
state: proven
title: mk
---
