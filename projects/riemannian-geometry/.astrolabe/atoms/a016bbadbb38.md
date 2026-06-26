---
chapter: '12'
dcref: ch12:3.10
ref:
- a016bbadbb38
sort: theorem
source: tex
src: docarmo
title: Byers
---
If $M$ is compact, $K<0$, and $H$ is a solvable subgroup of $\pi_1(M)$,
$H\neq\{e\}$, then $H$ is infinite cyclic. In addition, $\pi_1(M)$ does not have a
cyclic subgroup of finite index.

*Proof.* Since $H$ is solvable, there exists a finite sequence of subgroups

$$
H=H_o\supset H_1\supset\cdots\supset H_{k-1}\supset H_k=\{e\}
$$

such that $H_{i+1}$ is normal in $H_i$ and $H_i/H_{i+1}$ is abelian. Then
$H_{k-1}$ is abelian, hence, by Preissman's Theorem (3.2), infinite cyclic.

Let $g\in\pi_1(M)$ be a generator of $H_{k-1}$ and let $\tilde{\gamma}$ be the
geodesic in $\tilde{M}$ invariant under $g$. Let $a\in H_{k-2}$ and $b\in H_{k-1}$.
Since $a^{-1}b^{-1}ab\in H_{k-1}$, we have, for some integer $n$,

$$
a^{-1}b^{-1}ab=g^n.
$$

It follows that

$$
a^{-1}b^{-1}ab(\tilde{\gamma})=g^n(\tilde{\gamma})=\tilde{\gamma}.
$$

Since $b\in H_{k-1}$, $b(\tilde{\gamma})=\tilde{\gamma}$. Therefore
$b^{-1}a(\tilde{\gamma})=a(\tilde{\gamma})$, that is, $b^{-1}$ leaves invariant the
geodesic $a(\tilde{\gamma})$. By uniqueness, $a(\tilde{\gamma})=\tilde{\gamma}$.
Therefore, all the elements of $H_{k-2}$ leave $\tilde{\gamma}$ invariant. By
\entryref{46baf7fab729}, $H_{k-2}$ is infinite cyclic.

Repeating the argument above a finite number of times, we conclude that $H$ is
infinite cyclic, which proves the first statement of the theorem.

To prove the final assertion, suppose that there exists a subgroup
$H\subset\pi_1(M)$, cyclic and of finite index. Let $g$ be a generator of $H$ and
let $\tilde{\gamma}$ be the geodesic of $\tilde{M}$ invariant under $g$. Let
$a\in\pi_1(M)-H$. Since $H$ has finite index, there exist integers $m$ and $n$
such that $a^n=g^m$. Therefore

$$
a^n(\tilde{\gamma})=g^m(\tilde{\gamma})=\tilde{\gamma}.
$$

By uniqueness, $a(\tilde{\gamma})=\tilde{\gamma}$, for all $a\in\pi_1(M)-H$. It
follows that every element of $\pi_1(M)$ leaves invariant the geodesic
$\tilde{\gamma}$. By \entryref{46baf7fab729}, $\pi_1(M)$ is infinite cyclic, which contradicts
\entryref{f8456cb22b9d}. $\blacksquare$