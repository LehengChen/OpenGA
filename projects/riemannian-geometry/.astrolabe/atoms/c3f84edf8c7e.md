---
dcref: ch2:3.7
label: def:dc-ch2-3-7-christoffel
lean: Riemannian.chartChristoffel
lean_status: exists
proof_ok: false
provenance: docarmo
ref:
- c3f84edf8c7e
sort: definition
source: tex
statement_ok: true
title: Christoffel symbols
---
In a coordinate neighborhood $U$ with metric coefficients
  $g_{ij}=\langle X_i,X_j\rangle$ and inverse matrix $(g^{km})$, the
  \emph{Christoffel symbols} (of the second kind) are the functions on $U$ given
  by the classical formula

  $$
  \Gamma_{ij}^m=\tfrac{1}{2}\sum_k\Big\{\frac{\partial}{\partial x_i}g_{jk}+\frac{\partial}{\partial x_j}g_{ki}-\frac{\partial}{\partial x_k}g_{ij}\Big\}g^{km}.\qquad(10)
  $$