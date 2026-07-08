---
dcref: ch1:2.5
label: ex:dc-ch1-2-5
lean: Riemannian.DCInducedForm, Riemannian.DCInducedMetric
lean_status: exists
proof_ok: false
provenance: docarmo
ref:
- 2f2d9e16eadd
sort: example
source: tex
statement_ok: true
title: immersed manifolds
---
Let $f:M^n\to N^{n+k}$ be an immersion ($f$ differentiable, $df_p$ injective for
  all $p$). If $N$ is Riemannian, $f$ induces a metric on $M$ by
  $\langle u,v\rangle_p=\langle df_p(u),df_p(v)\rangle_{f(p)}$; this is positive
  definite because $df_p$ is injective, and the other conditions of \cref{def:dc-ch1-2-1}
  are easily verified. This is the *metric induced by $f$*, and $f$ is an *isometric
  immersion*. In particular, if $h:M^{n+k}\to N^k$ is differentiable and $q\in N$
  is a regular value, then $h^{-1}(q)$ is a submanifold of dimension $n$ carrying
  the metric induced by inclusion. E.g. with $h:\mathbb{R}^n\to\mathbb{R}$,
  $h(x)=\sum_i x_i^2-1$, the value $0$ is regular and $h^{-1}(0)=S^{n-1}$; the
  induced metric is the \emph{canonical metric} of $S^{n-1}$.