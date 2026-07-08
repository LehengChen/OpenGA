---
dcref: ch9:2.8
label: prop:dc-ch9-2-8
lean: null
lean_status: informal_only
proof_ok: false
provenance: docarmo
ref:
- c4be3a46efe4
sort: proposition
source: tex
statement_ok: false
title: formula for the second variation
---
Let $\gamma:[0,a]\to M$ be a geodesic and let
  $f:(-\varepsilon,\varepsilon)\times[0,a]\to M$ be a proper variation of $\gamma$. Let $E$
  be the energy function of the variation. Then
  
  $$
  \frac{1}{2}E''(0)=-\int_0^a\Big\langle V(t),\frac{D^2 V}{dt^2}+R\Big(\frac{d\gamma}{dt},V\Big)\frac{d\gamma}{dt}\Big\rangle dt-\sum_{i=1}^k\Big\langle V(t_i),\frac{DV}{dt}(t_i^+)-\frac{DV}{dt}(t_i^-)\Big\rangle,\qquad(3)
  $$
  
  where $V$ is the variational field of $f$, $R$ is the curvature of $M$ and
  $\frac{DV}{dt}(t_i^+)=\lim_{t\to t_i,\,t>t_i}\frac{DV}{dt}$,
  $\frac{DV}{dt}(t_i^-)=\lim_{t\to t_i,\,t<t_i}\frac{DV}{dt}$.