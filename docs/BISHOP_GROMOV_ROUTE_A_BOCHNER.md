# Bishop–Gromov — Route A (Bochner) completion plan

**Goal.** Make the Bishop–Gromov volume comparison theorem **unconditional** in
OpenGALib, following **Route A (the Bochner route)**: keep the already-proved
Bochner analytic core, and pay its two costs — the $\exp$ $C^1\!\to\!C^\infty$ lift
and the eikonal identity $|\nabla r|^2 = 1$.

This is a split math/engineering work order. Every still-missing piece below is
written as a triple — **File** (where the Lean goes), **Principle** (how to fill
it), **Reference** (the precise textbook place) — so the math group can verify the
references and the engineering group can build against them.

---

## 0. Current state

`Comparison/BishopGromov/` is **0-sorry modulo two interface structures**. The two
headlines are proved *conditionally*:

- `bishopGromov_volume_comparison` (`Comparison/BishopGromov/VolumeComparison.lean`)
  takes a `BishopGromovVolumeData g K p` and concludes that
  $\displaystyle f_p(R) = \frac{\operatorname{vol}_M(B_p(R))}{\operatorname{vol}_{\mathbb M_\kappa}(B(R))}$
  is non-increasing.
- `laplacian_comparison` (`Comparison/BishopGromov/LaplacianComparison.lean`)
  takes a `RadialLaplacianProfile g K p x` and concludes
  $\Delta_g r \le m_\kappa(r)$.

**The remaining work is to construct those two structures** for a real manifold
with $\operatorname{Ric} \ge (n-1)\kappa\, g$. Until they are *constructed*, BG is
geometrically vacuous (the structure fields are effectively axioms).

### Why Route A, and what it costs

Both classical routes reach the **same scalar Riccati inequality**
$$ a' + a^2 + \kappa \le 0, \qquad a = \frac{\Delta r}{\,n-1\,}, $$
then apply the (already-proved) Riccati comparison $a \le \bar a = \operatorname{ct}_\kappa$.

| | **Route A — Bochner (this plan)** | Route B — Jacobi / matrix-Riccati |
|---|---|---|
| How $a'+a^2+\kappa\le 0$ is obtained | Bochner formula on $\tfrac12|\nabla r|^2$ + eikonal $|\nabla r|=1$ | trace the matrix Riccati $S' + S^2 + R_{\dot\gamma}=0$ of the shape operator $S$ |
| Already built (0 sorry) | `bochner_radial_riccati`, `riccati_le_model`, refined Cauchy–Schwarz | — |
| Extra cost | $\exp$ $C^1\!\to\!C^\infty$ (**B1**) + eikonal $|\nabla r|=1$ (**B2**) | Jacobi fields + shape operator + conjugate/cut-locus cone |

The project's own BG notes `references/arXiv-2404.09792v2/CH21.tex` use **Route B**
(it never needs $C^\infty$ of $\operatorname{dist}$). We deliberately use Route A
for the Laplacian leg (reusing our Bochner core), and follow CH21 only for the
volume leg `[C]` (which is already Jacobi-determinant based).

> Engineering: re-confirm live status before starting —
> `grep -rn "sorry" OpenGALib/Comparison OpenGALib/Riemannian/{Exponential,Volume,Operators,Connection}`.
> Status tags below are accurate as of 2026-06-15.

---

## 1. Leg [B] — Laplacian comparison $\Delta_g r \le m_\kappa$ ⇒ `RadialLaplacianProfile`

where the model mean curvature is $m_\kappa(r) = (n-1)\dfrac{s_\kappa'(r)}{s_\kappa(r)}$
(`modelMeanCurvature`, `Comparison/BishopGromov/RiccatiComparison.lean:34`;
$s_\kappa = $ `snakeFunction`, `Comparison/Util/SpaceForm.lean:22`).

### ✅ already done
- **B3.** Bochner radial Riccati $a' + a^2 + \kappa \le 0$ — `bochner_radial_riccati`
  (`Comparison/BishopGromov/RadialRiccati.lean:138`).
- **B4.** Riccati comparison $a \le \operatorname{ct}_\kappa$ — `riccati_le_model`
  (`Comparison/BishopGromov/RiccatiComparison.lean`).
- Refined Cauchy–Schwarz $(\operatorname{tr} S)^2 \le (n-1)|S|^2$ —
  `Comparison/Util/RefinedCauchySchwarz.lean`.

### ❌ B1 — lift $\exp_p$ from $C^1$ to $C^\infty$ &nbsp;(⚠ large, but "not new math")
- **What.** $\exp_p : T_pM \to M$ is $C^\infty$. Today it is only $C^1$:
  `expMap_contMDiffAt_zero` is hard-coded to order $1$.
  This is the gate for the whole of leg [B], because `bochner_radial_riccati`
  requires $r = \operatorname{dist}(p,\cdot) \in C^\infty$ (it differentiates the
  Hessian of $r$), and $r \in C^\infty$ on the normal ball iff $\exp_p$ is.
- **File.** `Exponential/Smoothness/*` (7 files: `AtZero`, `MatchDataReduction`,
  `ZeroSectionConstancy`, `UniformChartFlowBridge`, `ChartFlowVelocitySlice`,
  `MfderivZero`) + `Exponential/LocalDiffeomorphism.lean`. Parameterize the whole
  chain by the smoothness order instead of the constant $1$.
- **Principle.** The geodesic ODE flow is genuinely $C^\infty$:
  `SmoothFlow.lean` already proves arbitrary-order regularity
  (`chartPhaseVFTime_uncurry_contDiffOn_univ_nat`). Thread an order parameter
  $n$ (or $\infty$) through `MatchDataReduction`/`ZeroSectionConstancy`/
  `UniformChartFlowBridge`; the `ContMDiffAt.congr_of_eventuallyEq` step is
  order-agnostic. **Possible shortcut (math group, please assess):**
  `bochner_radial_riccati` only assumes `[IsManifold I 2 M]`, so its $\infty$
  hypothesis on $r$ can likely weaken to a fixed finite order $\approx C^3$; then
  B1 only needs a *finite-order* lift, which the SmoothFlow `…_univ_nat` result
  gives directly.
- **Reference.** Smooth dependence of geodesics / smoothness of $\exp$:
  **Lee 2e, Ch. 5** (The Exponential Map). **Petersen 3e, Ch. 5** (Geodesics and
  Distance). Smooth dependence on initial conditions for ODEs: Lee, *Smooth
  Manifolds* (ODE appendix).

### 🔶 B2 — eikonal identity $|\nabla r|^2 = 1$ &nbsp;(⚠ $\ge 1$ half is the open risk)
- **What.** On the punctured normal ball, $|\nabla r|^2_g = 1$. Equivalently the
  triple $|\nabla r|^2 = 1,\ d|\nabla r|^2 = 0,\ \Delta|\nabla r|^2 = 0$ that
  `bochner_radial_riccati` consumes (the last two are derivatives of a constant,
  so the whole package reduces to the single identity).
- **$\le 1$ half — done:** `manifoldGradient_metricInner_self_le_one`
  (`Operators/Gradient.lean`): from $(dr(v))^2 \le |v|^2_g$ conclude
  $\langle\nabla r,\nabla r\rangle \le 1$.
  - **Still missing for $\le 1$** — *File:* `Operators/Gradient.lean`.
    *What:* the differential bound $(d(\operatorname{dist}(p,\cdot))(v))^2 \le |v|^2_g$.
    *Principle:* $\operatorname{dist}(p,\cdot)$ is $1$-Lipschitz w.r.t. the
    `riemannianEDist` (infimum of $g$-lengths of paths); build the
    `riemannianEDist` $\leftrightarrow$ $g$-norm infinitesimal bridge.
    *Reference:* **Lee 2e, Ch. 6** (lengths and the Riemannian distance).
- **$\ge 1$ half — ❌ ⚠ HIGHEST RISK ("the open question"):**
  - **What.** $|\nabla r| \ge 1$, equivalently the **Gauss lemma + radial
    isometry** $\operatorname{dist}(p, \exp_p v) = |v|$: along a unit radial
    geodesic $\gamma$, $dr(\gamma') = 1$ and $|\gamma'| = 1$, so Cauchy–Schwarz
    gives $|\nabla r| \ge 1$.
  - **File.** *New file* (none exists), e.g. `Exponential/GaussLemma.lean` (radial
    isometry / Gauss lemma) feeding `Operators/Gradient.lean` for the final
    $|\nabla r| \ge 1$.
  - **Principle.** Gauss lemma: $d\exp_p|_v$ sends the radial direction to a unit
    tangent and is an isometry on the radial line, with radial $\perp$ spherical.
    Then radial geodesics are locally minimizing $\Rightarrow$ radial isometry.
    This is first-variation machinery; build it *in our conventions*, do **not**
    migrate external's variation cone (per the standing decision).
  - **Reference.** **Lee 2e, Ch. 6** (the Gauss Lemma; geodesics are locally
    minimizing). **Petersen 3e, Ch. 5** (the Gauss lemma & first variation).
    **Math group: this is where to find and pin the cleanest reference proof.**

### ❌ B5 — construct `RadialLaplacianProfile` (the leg-[B] discharge)
- **What / File.** Provide a term of `RadialLaplacianProfile g K p x`
  (`Comparison/BishopGromov/LaplacianComparison.lean`); its fields:
  - `profile : ℝ → ℝ` and `eval : profile (dist p x) = scalarLaplacian g (dist p ·) x`
    — the radial profile is $m(s) = \Delta_g r$
    (`scalarLaplacian`, `Operators/Laplacian.lean:99`).
  - `riccati_sub`: $\;m'(s) + \dfrac{m(s)^2}{n-1} + (n-1)\kappa \le 0$.
  - `asymptotic`: $m(s) - \dfrac{n-1}{s} \to 0$ as $s\to 0^+$.
- **Principle.** `riccati_sub` $\Leftarrow$ **B3** (`bochner_radial_riccati`) once
  $r\in C^\infty$ (**B1**) and the eikonal holds (**B2**). `eval`/`differentiableAt`
  $\Leftarrow$ smoothness of $r$ off the cut locus + the radial structure.
  `asymptotic` $\Leftarrow$ the Euclidean base-point behaviour ($d\exp_p|_0 = \mathrm{id}$).
- **Reference.** Laplacian comparison and the asymptotic $\Delta r \sim \tfrac{n-1}{r}$:
  **Petersen 3e, Ch. 9** (Ricci Curvature Comparison). **Lee 2e, Ch. 11**
  (comparisons based on Ricci curvature).

---

## 2. Leg [C] — polar volume formula ⇒ `BishopGromovVolumeData`

Leg [C] needs only $C^1$ $\exp$ (it does **not** depend on B1). It is the
CH21-aligned (Jacobi-determinant) leg.

### ✅ already done
- **C1.** Exp-volume change of variables + volume-measure substrate:
  `exists_volumeMeasure_expImage_eq_setLIntegral_jacobian` (`Volume/ExpBridge.lean`),
  chart-pullback keystone (`Volume/ChartPullbackFormula.lean`), local-finiteness &
  `volumeFormAt` (`Volume/ChartPullback.lean`, `Volume/VolumeForm.lean`).
- **C5.** Monotone average integral: $q$ non-increasing $\Rightarrow$
  $\dashint_0^t q$ non-increasing — `ratio_intervalIntegral_le`
  (`Comparison/BishopGromov/VolumeMonotone.lean`),
  `ratio_spaceFormBallVolume_le` (`Comparison/BishopGromov/PolarVolumeReduction.lean`).

### 🔶 C2 — polar Jacobian factorization $\det d\exp_p(t\xi) = t^{n-1} J_\xi(t)$
- **What.** In polar coordinates $(t,\xi)\in\mathbb R_{>0}\times S^{n-1}$, the
  volume Jacobian factors as $\det d\exp_p(t\xi) = t^{n-1} J_\xi(t)$, where
  $J_\xi(t)$ is the determinant of the $(n-1)\times(n-1)$ Jacobi-field matrix along
  $\gamma_\xi(t) = \exp_p(t\xi)$.
- **File.** `Volume/Exponential.lean` (partial: `det_dExpMap_jacobiField_decomp`,
  `det_dExpMap_pos` present; the main `volumeMeasure_eq_pushforward_expMap` still
  has sorries). Positivity helper in `Volume/ExpBridge.lean`
  (`chartExp_volumeJacobian_pos`).
- **Principle.** $d\exp_p(t\xi)$ maps the flat Jacobi fields $\bar J_i(t)=t v_i$ to
  the manifold Jacobi fields $J_i(t)$ with $J_i(0)=0,\ J_i'(0)=v_i$; the radial
  direction contributes the unit $\dot\gamma$, giving the block-triangular
  determinant $\Rightarrow$ the $t^{n-1}$ factor.
- **Reference.** **CH21** lines 84–134 (the $j(v,t)$ density). **Lee 2e, Ch. 10**
  (Jacobi fields, basic computations). **Petersen 3e, Ch. 9**.

### ❌ C3 — radial log-derivative bridge $\partial_t \log J_\xi(t) = \Delta_g r$
- **What.** $\partial_t \log J_\xi(t) = \operatorname{tr} S(t) = \Delta_g r(\gamma_\xi(t))$
  — the derivative of the volume density equals the mean curvature of the geodesic
  sphere, which is the Laplacian of $r$. This is the bridge that lets leg-[B]'s
  $\Delta r \le m_\kappa$ produce the antitone density ratio.
- **File.** `Volume/Exponential.lean` (extend it), or a new `Volume/RadialJacobian.lean`.
- **Principle.** From $J' = SJ$ (shape operator) and the matrix-determinant
  derivative $\partial_t \det = \det \cdot \operatorname{tr}(J^{-1}J')$ get
  $\partial_t \log J = \operatorname{tr} S$; identify $\operatorname{tr} S$ with
  $\Delta_g r$ (mean curvature of the $t$-sphere $=$ Laplacian of the distance).
- **Reference.** **CH21** lines 156–189 ($\partial_t j = \operatorname{tr}(S)\, j$).
  **Petersen 3e, Ch. 9** ($\Delta r =$ mean curvature). **Lee 2e, Ch. 11**.

### ❌ C4 — cut locus has measure zero + polar volume formula
- **What.** $\exp_p : (B(0,r)\cap C_p) \to (B(p,r)\setminus \operatorname{cut}(p))$
  is a diffeomorphism, $\operatorname{cut}(p)$ has measure zero, hence
  $$ \operatorname{vol}(B(p,R)) = \int_0^R\!\!\int_{S^{n-1}} J_\xi(t)\,d\xi\,dt = \int_0^R A(t)\,dt, \qquad A(t) = \int_{S^{n-1}} J_\xi(t)\,d\xi. $$
- **File.** *New file* (no cut-locus layer exists): `Exponential/CutLocus.lean`
  (definition + measure-zero) and a `Volume/Polar.lean` (or extend
  `Volume/Exponential.lean`) for the polar integral assembly.
- **Principle.** Define $\operatorname{cut}(v)$ / $C_p$; cut locus is the image of a
  Lipschitz graph over $S^{n-1}$ $\Rightarrow$ measure zero; combine with **C1**
  (change of variables) + **C2** (polar factorization) to integrate in polar form.
- **Reference.** **CH21** lines 248–264 (the measure-zero Fact + polar volume).
  **Lee 2e, Ch. 10** (cut points). **Petersen 3e, Ch. 5 / Ch. 9**.

### ❌ C6 — construct `BishopGromovVolumeData` (the leg-[C] discharge)
- **What / File.** Provide a term of `BishopGromovVolumeData g K p`
  (`Comparison/BishopGromov/VolumeComparison.lean`); fields:
  - `area : ℝ → ℝ` $= A(t)$, and `vol_eq`: $\operatorname{vol}_g(B(p,R)) = \int_0^R A$
    $\Leftarrow$ **C4**.
  - `area_integrable`.
  - `ratio_antitone`: $t \mapsto A(t)/\max(0, s_\kappa(t))^{\,n-1}$ antitone on
    $(0,R]$ $\Leftarrow$ **C3** + leg-[B] $\Delta r \le m_\kappa$ (so
    $\partial_t \log(A/\bar j) = \Delta r - m_\kappa \le 0$).
- **Reference.** **CH21** lines 272–293 (the ratio assembly). **Petersen 3e, Ch. 9**.

---

## 3. Finish

- [ ] Drop the `(data : …)` arguments from `bishopGromov_volume_comparison` and
  `laplacian_comparison` (their proof bodies are already written against the
  interfaces) ⇒ BG unconditional.

---

## 4. References & PDFs

- **John M. Lee, _Introduction to Riemannian Manifolds_, 2nd ed. (GTM 176, 2018).**
  Book page: <https://sites.math.washington.edu/~lee/Books/RM/> ·
  Full PDF: <https://link.springer.com/content/pdf/10.1007/978-3-319-91755-9.pdf>.
  Used: **Ch. 5** (exponential map — B1), **Ch. 6** (Riemannian distance, Gauss
  lemma — B2), **Ch. 10** (Jacobi fields, cut points — C2, C4), **Ch. 11**
  (comparison theory, Ricci — B5, C3).
- **Peter Petersen, _Riemannian Geometry_, 3rd ed. (GTM 171, 2016).**
  Author PDF: <https://www.math.ucla.edu/~petersen/RG.pdf>.
  Used: **Ch. 5** (Geodesics and Distance — B1, B2), **Ch. 7** (The Bochner
  Technique — B3), **Ch. 9** (Ricci Curvature Comparison; Bishop–Gromov, relative
  volume, Laplacian/mean-curvature comparison — B5, C3–C6).
- **Project notes** `references/arXiv-2404.09792v2/CH21.tex` (Bishop–Gromov
  chapter) — primary source for leg [C] and the monotone-average lemma.

> **Math group:** verify each "Reference" above against the linked PDFs, pin the
> exact section/page, and flag any hypothesis mismatch (completeness, smoothness
> order, cut-locus treatment) vs. what the OpenGALib lemma needs — especially
> **B1's finite-order shortcut** and **B2's $\ge 1$ Gauss-lemma route**.

---

## 5. Owners & roles

- **Engineering** (build the Lean on `feat/bishop-gromov`): Leheng Chen `@LehengChen`.
- **Math** (verify references accurate, pin sections, resolve B1 finite-order
  shortcut & B2 $\ge 1$ Gauss route): Zhifei Zhu `@imathwy` / `@zhifeizhu92`,
  Chunlei Liu `@Spring-1211`.

*Generated 2026-06-15. Route A = Bochner. Branch `feat/bishop-gromov`.*
