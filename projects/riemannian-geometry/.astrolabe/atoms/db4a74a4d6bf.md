---
dcref: ch10:2.1
label: lem:dc-ch10-2-1
lean: null
lean_status: informal_only
proof_ok: false
provenance: docarmo
ref:
- db4a74a4d6bf
sort: lemma
source: tex
statement_ok: false
title: Lemma 2.1
---
Let $h:[0,1]\to\mathbb{R}$ be a differentiable function with $h(0)=0$. Then there
  exists a differentiable function $\phi:[0,1]\to\mathbb{R}$, with
  $\phi(0)=\frac{dh}{dt}(0)$, $h(t)=t\phi(t)$, $t\in[0,1]$.
  
  Let $M$ be a Riemannian manifold and let $\gamma:[0,a]\to M$ be a geodesic of
  $M$. Let $V$ be a piecewise differentiable vector field along $\gamma$. For all
  $t_o\in[0,a]$, we write
  
  $$
  \int_0^{t_o}\{\langle V',V'\rangle-\langle R(\gamma',V)\gamma',V\rangle\}\,dt=I_{t_o}(V,V).
  $$