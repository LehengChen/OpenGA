# Atom Boundary Review Checklist

This file lists atoms where substantial content appears after the proof-ending
symbol (`\square` or `\blacksquare`). In many cases this is just a concluding
remark of the same statement, but some entries may have accidentally included
the beginning of the next statement during extraction/OCR.

Total atoms scanned: 264. Entries with >200 chars after QED: 16.
Entries flagged as "likely belongs to next dcref" are the highest priority.

| dcref | atom | title | after QED (chars) | flag | trailing preview |
|-------|------|-------|-------------------|------|------------------|
| ch0:4.2 | 2a37e4843dff | regular surfaces in $\mathbb{R}^n$ | 210 | - | $ It follows (as in \entryref{55d1687874f4}) that $M^k$ is a differentiable manifold of dimension $k$ and the inclusion $i:M^k\subset\mathbb{R}^n$ is an embedding, i.e. $M^k$ is a submanifold of $\mathbb{R}^n$.... |
| ch0:5.3 | c20e049fba4e | properties of the bracket | 774 | likely belongs to ch0:5.4 | $  The bracket $[X,Y]$ can also be interpreted as a derivative of $Y$ along the "trajectories" of $X$. Since a differentiable manifold is locally diffeomorphic to $\mathbb{R}^n$, the fundamental theorem on existence, uniqueness and dependence on initial conditions of ODEs extends... |
| ch0:5.5 | fc5a1bb299dd | Hadamard-type lemma from calculus | 1484 | - | $  *Topology of manifolds.* Up to here no restriction was put on the topology. Two axioms may fail: **A) Hausdorff Axiom** — distinct points have disjoint neighborhoods; **B) Countable Basis Axiom** — $M$ is covered by countably many coordinate neighborhoods. Axiom A is essential... |
| ch4:2.5 | 91101fb52f8d | symmetries of the curvature | 1251 | - | $  It is convenient to express what was seen above in a coordinate system $(U,\mathbf{x})$ based at $p\in M$. Indicating $\frac{\partial}{\partial x_i}=X_i$, we put  $$ R(X_i,X_j)X_k=\sum_\ell R_{ijk}^\ell X_\ell, $$  so the $R_{ijk}^\ell$ are the components of the curvature $R$ ... |
| ch6:2.1 | 73bbdba0e0a8 | the second fundamental form mapping $B$ | 315 | - | $  Because $B$ is bilinear, the value $B(X,Y)(p)$ depends only on the values $X(p)$ and $Y(p)$. Now let $p\in M$ and $\eta\in(T_pM)^\perp$. The mapping $H_\eta:T_pM\times T_pM\to\mathbb{R}$ given by  $$ H_\eta(x,y)=\langle B(x,y),\eta\rangle,\quad x,y\in T_pM, $$  is, by Proposit... |
| ch6:2.9 | 1bc6577d8e3a | totally geodesic criterion | 865 | - | $  Proposition 2.9 gives the geometric interpretation of sectional curvature. Let $B\subset T_pM$ be an open ball on which $\exp_p$ is a diffeomorphism, and $\sigma\subset T_pM$ a two-dimensional subspace. Then $\exp_p(\sigma\cap B)=S$ is a two-dimensional submanifold of $M$ thro... |
| ch7:2.3 | b293201bcf35 | Proposition 2.3 | 609 | - | $  It can be shown by an example that the converse is *not* true (cf. Exercise 4), so the class of non-extendible manifolds is actually larger than the class of complete manifolds.  At this stage it is convenient to introduce a distance function on a Riemannian manifold (not nece... |
| ch8:2.1 | 4a37954c3621 | E. Cartan | 446 | - | $  Observe that the same proof shows that if $\exp_p$ and $\exp_{\tilde{p}}$ are diffeomorphisms, then, under the conditions of Theorem 2.1, $f$ is defined on all of $M$ and is an isometry. The theorem implies that the metric is, in a certain sense, determined locally by the curv... |
| ch8:3.1 | b1bc4979d87f | geodesics of $H^n$ | 470 | - | $  It follows from the existence and uniqueness theorem for geodesics that all the geodesics of $H^n$ are of the type described in Proposition 3.1, and are contained in planes perpendicular to the hyperplane $x_n=0$. Since such planes are clearly isometric to the hyperbolic plane... |
| ch8:4.2 | ed5c99ea7483 | uniqueness of a local isometry from a point datum | 1686 | likely belongs to ch8:4.3 | $  The complete manifolds with constant sectional curvature are called *space forms*. The last theorem reduces the determination of all the space forms to a problem in group theory. Recall: a group $G$ *acts* on a set $M$ if there is a map $G\times M\to M$, $(g,x)\mapsto gx$, wit... |
| ch8:4.3 | 25c5af8cc0f8 | every space form is a quotient of a model | 347 | likely belongs to ch8:4.4 | $  The last proposition reduces the problem of finding all the space forms to that of determining all the subgroups of the group of isometries that act in a totally discontinuous manner on each of the simply connected models. The spherical problem ($\tilde{M}=S^n$) was solved dur... |
| ch8:4.5 | b9cdcdcd003d | metric of constant negative curvature on surfaces of genus $>1$ | 1023 | - | $  The spaces of constant curvature have an important role in the historical development of Riemannian Geometry, due to their relationship with non-Euclidean geometry. A non-Euclidean geometry is a complete Riemannian manifold $M$ together with a transitive group of isometries $G... |
| ch8:5.3 | 8a57517fee19 | isometries of $H^n$ are conformal transformations preserving $H^n$ | 494 | - | $  To conclude this section, we identify some important hypersurfaces of $H^n$. The intersection with $H^n$ of hyperplanes of $\mathbb{R}^n$ orthogonal to $\partial H^n$, and of spheres with center on $\partial H^n$, are totally geodesic submanifolds of $H^n$ (Exercise 2). To det... |
| ch9:2.2 | d19dfbacb4d5 | existence of a variation with given variational field | 819 | - | $  To compare the arc length of $c$ with that of neighboring curves we define $L:(-\varepsilon,\varepsilon)\to\mathbf{R}$ by  $$ L(s)=\int_0^a\Big\|\frac{\partial f}{\partial t}(s,t)\Big\|\,dt, $$  the length of the curve $f_s(t)$. It is more convenient to work with the *energy fun... |
| ch10:4.9 | 8286f921d5a2 | extension of Rauch to focal points | 1416 | - | $  Other useful extensions of the Rauch comparison theorem can be found in F. Warner, "Extensions of the Rauch comparison theorem to submanifolds", Trans. A.M.S. 122 (1966), 341-356, and in E. Heintze and H. Karcher, "A general comparison theorem with applications to volume estim... |
| ch12:3.1 | 167b9abd6797 | comparison for geodesic triangles, $K\leq 0$ | 234 | - | $  From now on, $M$ will denote a complete Riemannian manifold with sectional curvature $K<0$. As always, $\pi:\tilde{M}\to M$ denotes the universal covering of $M$ with the covering metric. Our goal is to prove the following theorem.... |

## Priority fixes to check first

The following were flagged because their trailing content shares multiple keywords
with the next atom in the book order:

- **ch0:5.3** `c20e049fba4e.md` — likely belongs to ch0:5.4
- **ch8:4.2** `ed5c99ea7483.md` — likely belongs to ch8:4.3
- **ch8:4.3** `25c5af8cc0f8.md` — likely belongs to ch8:4.4

## How to use this list

1. Open the atom file (the `atom` column gives the 12-character file stem).
2. Check whether the text after `\square` is a follow-up remark of the current
   statement or the start of the next one.
3. If it is the next statement, move that text to the correct atom file (or delete
   if it duplicates the next atom).
4. After fixing, update this checklist.
