---
chapter: '8'
dcref: ch8:4.3
ref:
- fcf67ee3deff
sort: proposition
source: tex
src: docarmo
title: every space form is a quotient of a model
---
Let $M$ be a complete Riemannian manifold with constant sectional curvature $K$
($1,0,-1$). Then $M$ is isometric to $\tilde{M}/\Gamma$, where $\tilde{M}$ is $S^n$
(if $K=1$), $\mathbb{R}^n$ (if $K=0$) or $H^n$ (if $K=-1$), $\Gamma$ is a subgroup
of the group of isometries of $\tilde{M}$ which acts in a totally discontinuous
manner on $\tilde{M}$, and the metric on $\tilde{M}/\Gamma$ is induced from the
covering $\pi:\tilde{M}\to\tilde{M}/\Gamma$.

*Proof.* Consider the universal covering $p:\tilde{M}\to M$ with the covering
metric. Let $\Gamma$ be the group of covering transformations of $p$. Then
$\Gamma$ is a subgroup of the isometries of $\tilde{M}$ and acts in a totally
discontinuous manner. Introduce on $\tilde{M}/\Gamma$ the metric induced by
$\pi:\tilde{M}\to\tilde{M}/\Gamma$. Since the covering $p$ is regular, given
$\tilde{x},\tilde{y}\in\tilde{M}$, $p(\tilde{x})=p(\tilde{y})$ iff
$\Gamma\tilde{x}=\Gamma\tilde{y}$, equivalently $\pi(\tilde{x})=\pi(\tilde{y})$.
The equivalence classes given by $p$ and $\pi$ are the same, which induces a
bijection $\xi:M\to\tilde{M}/\Gamma$ such that $\pi=\xi\circ p$. Since $\pi$ and
$p$ are local isometries, $\xi$ is a local isometry, and being a bijection, is an
isometry of $M$ onto $\tilde{M}/\Gamma$. $\square