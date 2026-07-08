---
dcref: ch0:2.9
label: def:dc-ch0-2-9
lean: Riemannian.DCDiffeomorph
lean_status: exists
proof_ok: false
provenance: docarmo
ref:
- 1ecdbfdc8ffc
sort: definition
source: tex
statement_ok: true
title: diffeomorphism; local diffeomorphism
---
$\varphi:M_1\to M_2$ is a \emph{diffeomorphism} if it is differentiable, bijective, and
  $\varphi^{-1}$ is differentiable. It is a \emph{local diffeomorphism at} $p$ if there
  exist neighborhoods $U$ of $p$ and $V$ of $\varphi(p)$ with $\varphi:U\to V$ a
  diffeomorphism. By the chain rule, if $\varphi$ is a diffeomorphism then
  $d\varphi_p:T_pM_1\to T_{\varphi(p)}M_2$ is an isomorphism for all $p$; in
  particular $\dim M_1=\dim M_2$.