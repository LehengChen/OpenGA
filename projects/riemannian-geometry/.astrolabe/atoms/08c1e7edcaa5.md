---
dcref: ch0:5.2
label: lem:dc-ch0-5-2-commutator
lean: Riemannian.mfderiv_mlieBracket_eq_commutator
lean_status: exists
proof_ok: false
provenance: docarmo
ref:
- 08c1e7edcaa5
sort: lemma
source: tex
statement_ok: true
title: 'existence characterization: the bracket acts as the commutator of derivations'
---
Let $X,Y$ be smooth vector fields on a boundaryless manifold $M$ and $f$ a smooth
  real function. Then the bracket field $[X,Y]=\texttt{mlieBracket}$ acts on $f$ as the
  commutator of the derivations $X$ and $Y$:
  $$
  [X,Y]f = X(Yf)-Y(Xf), \qquad\text{i.e.}\qquad
  \mathrm{d}f_p([X,Y]_p) = \mathrm{d}(\mathrm{d}f\,Y)_p(X_p)-\mathrm{d}(\mathrm{d}f\,X)_p(Y_p).
  $$
  This is the existence half of \cref{lem:dc-ch0-5-2}: the field $[X,Y]$ realizes the
  derivation $(XY-YX)$.