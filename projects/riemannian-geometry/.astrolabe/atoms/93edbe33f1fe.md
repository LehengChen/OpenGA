---
dcref: ch0:5.4
label: prop:dc-ch0-5-4
lean: Riemannian.DCLieBracket_eq_flow_lieDerivative
lean_status: exists
proof_ok: false
provenance: docarmo
ref:
- 93edbe33f1fe
sort: proposition
source: tex
statement_ok: true
title: bracket as Lie derivative along the flow
---
Let $X,Y$ be differentiable vector fields on $M$, $p\in M$, and $\varphi_t$ the
  local flow of $X$ in a neighborhood $U$ of $p$. Then

  $$
  [X,Y](p)=\lim_{t\to0}\frac1t\,[Y-d\varphi_t Y](\varphi_t(p)).
  $$
  (The machine-checked form is a derivation-level identity tested against a smooth
  $f$: writing $A(t)=(Yf)(\varphi_t p)$ and $B(t)=(Y(f\circ\varphi_t))(p)=((d\varphi_t
  Y)f)(\varphi_t p)$, the claim is $\lim_{t\to0}\frac1t(A(t)-B(t))=([X,Y]f)(p)$. The
  local flow $\varphi$ is taken as data via the project-local predicate
  \texttt{Riemannian.IsLocalFlow} — $\varphi_0=\mathrm{id}$, each trajectory an
  integral curve of $X$, and joint $C^\infty$ dependence — since the smooth
  dependence-on-initial-conditions theorem (the variational equation) is not yet
  available from Mathlib's Picard–Lindelöf theory.)