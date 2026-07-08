---
content: "{P : Sort u} →\n  {E : Type u_1} →\n    {inst : NormedAddCommGroup E} →\n\
  \      {inst_1 : NormedSpace ℝ E} →\n        {H : Type u_2} →\n          {inst_2\
  \ : TopologicalSpace H} →\n            {I : ModelWithCorners ℝ E H} →\n        \
  \      {M : Type u_4} →\n                {inst_3 : TopologicalSpace M} →\n     \
  \             {inst_4 : ChartedSpace H M} →\n                    {inst_5 : IsManifold\
  \ I (↑⊤) M} →\n                      {t : Riemannian.AffineConnection I M} →\n \
  \                       {E' : Type u_1} →\n                          {inst' : NormedAddCommGroup\
  \ E'} →\n                            {inst'_1 : NormedSpace ℝ E'} →\n          \
  \                    {H' : Type u_2} →\n                                {inst'_2\
  \ : TopologicalSpace H'} →\n                                  {I' : ModelWithCorners\
  \ ℝ E' H'} →\n                                    {M' : Type u_4} →\n          \
  \                            {inst'_3 : TopologicalSpace M'} →\n               \
  \                         {inst'_4 : ChartedSpace H' M'} →\n                   \
  \                       {inst'_5 : IsManifold I' (↑⊤) M'} →\n                  \
  \                          {t' : Riemannian.AffineConnection I' M'} →\n        \
  \                                      E = E' →\n                              \
  \                  inst ≍ inst' →\n                                            \
  \      inst_1 ≍ inst'_1 →\n                                                    H\
  \ = H' →\n                                                      inst_2 ≍ inst'_2\
  \ →\n                                                        I ≍ I' →\n        \
  \                                                  M = M' →\n                  \
  \                                          inst_3 ≍ inst'_3 →\n                \
  \                                              inst_4 ≍ inst'_4 →\n            \
  \                                                    inst_5 ≍ inst'_5 →\n      \
  \                                                            t ≍ t' →\n        \
  \                                                            Riemannian.AffineConnection.noConfusionType\
  \ P t t'"
file: Riemannian/Manifold/DoCarmoCh2.lean
line: 129
name: Riemannian.AffineConnection.noConfusion
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh2.lean
ref:
- aed08eefab06
sort: definition
source: lean
state: proven
title: noConfusion
---
