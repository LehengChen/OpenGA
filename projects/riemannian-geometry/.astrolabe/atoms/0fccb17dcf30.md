---
content: "∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]\
  \ {H : Type u_2} [inst_2 : TopologicalSpace H]\n  {I : ModelWithCorners ℝ E H} {G\
  \ : Type u_7} [inst_3 : Group G] [inst_4 : TopologicalSpace G]\n  [inst_5 : ChartedSpace\
  \ H G] (b : E →L[ℝ] E →L[ℝ] ℝ),\n  (∀ (u v : E), (b u) v = (b v) u) →\n    ∀ (x\
  \ : G) (u v : TangentSpace I x),\n      ((Riemannian.DCLeftInvariantForm b x) u)\
  \ v = ((Riemannian.DCLeftInvariantForm b x) v) u"
file: Riemannian/Manifold/DoCarmoCh1.lean
line: 550
name: Riemannian.DCLeftInvariantForm_symm
path: /Users/moqian/OpenGALib/OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean
ref:
- 0fccb17dcf30
sort: theorem
source: lean
state: proven
title: DCLeftInvariantForm_symm
---
