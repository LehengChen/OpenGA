# Bishop–Gromov — Route A (Bochner) completion plan

**Goal.** Make the Bishop–Gromov volume comparison theorem **unconditional** in
OpenGALib by discharging the two interface structures it currently depends on,
following **Route A: the Bochner route** (keep the already-built Bochner analytic
core; pay the two costs that route incurs — the `exp` C¹→C∞ lift and the eikonal
identity).

This is a planning + reference document for a split math/engineering effort. It
lists the mathematical content involved, the current formalization status of each
piece, and the textbook cross-references the math group should verify.

---

## 0. Status quo (read first)

`Comparison/BishopGromov/` is **0-sorry _modulo two interfaces_**. The headline
theorems are proved as *conditional* statements:

- `bishopGromov_volume_comparison` (VolumeComparison.lean) takes a
  `BishopGromovVolumeData g K p` and concludes the volume-ratio monotonicity.
- `laplacian_comparison` (LaplacianComparison.lean) takes a
  `RadialLaplacianProfile g K p x` and concludes `Δ_g r ≤ m_κ`.

**The remaining work = constructing those two structures from a real manifold
with `Ric ≥ (n−1)κ g`.** Until then BG is geometrically vacuous (the interface
fields are effectively axioms). This document scopes exactly that construction
via Route A.

> Engineering note: before starting, re-confirm the live sorry/interface status
> with `grep -rn "sorry" OpenGALib/Comparison OpenGALib/Riemannian/{Exponential,Volume,Operators,Connection}`
> — statuses below are accurate as of 2026-06-15 but the branch moves.

### The two routes (why "A")

Both routes reach the **same scalar Riccati inequality** `a' + a² + κ ≤ 0` with
`a = Δr/(n−1)`, then apply the (already-proved) Riccati comparison.

| | Route A — **Bochner** (this doc) | Route B — Jacobi / matrix-Riccati |
|---|---|---|
| How `a' + a² + κ ≤ 0` is obtained | Bochner formula on `½|∇r|²` + eikonal `|∇r|=1` | trace of the matrix Riccati `Ṡ + S² + R = 0` for the shape operator `S` |
| Already built in OpenGALib | `bochner_radial_riccati`, `riccati_le_model`, refined Cauchy–Schwarz — **0 sorry** | not built |
| Extra cost | **`exp` C¹→C∞ lift (L0)** + **eikonal `|∇r|=1`** | Jacobi fields + shape operator + conjugate/cut-locus cone |
| Reference text route | Petersen Ch 7 (Bochner) + Ch 9 (Ricci comparison) | the user's notes `references/.../CH21.tex` |

**Route A keeps the analytic core we already have.** Its price is L0 + eikonal.
(For the record: the user's own BG notes, `CH21.tex`, follow Route B — the
Jacobi/shape-operator route — and therefore never need L0 or the Hessian of
`dist`. We are deliberately *not* matching CH21 on the Laplacian leg; we match it
only on the volume/Jacobian leg `[C]`, which already uses Jacobi-field
determinant decomposition.)

---

## 1. Math content, in dependency order

Legend: ✅ done (0 sorry) · 🔶 partial · ❌ to build · ⚠ highest-risk.

### Leg [B] — Laplacian comparison `Δ_g r ≤ m_κ` ⇒ `RadialLaplacianProfile`

#### B1. `exp` C¹ → C∞ lift  (L0)  ❌  ⚠ large but "not new math"
- **Statement.** `expMap g p : T_pM → M` is `C^∞` (currently only `C¹`:
  `expMap_contMDiffAt_zero` is hard-coded to order `1`, and the whole proof chain
  `Exponential/Smoothness/*` (~7 files) + `LocalDiffeomorphism.lean` is built for
  `C¹`).
- **Why needed.** `bochner_radial_riccati` requires `f = dist` to be
  `ContMDiff I 𝓘(ℝ,ℝ) ∞` (it uses the Hessian of `dist`); `dist` is `C∞` on the
  normal ball iff `exp` is. This is the *gate* for all of leg [B].
- **How.** Parameterize the existing `C¹` chain by an arbitrary order. The
  underlying geodesic ODE flow is genuinely `C∞`: `SmoothFlow.lean` already has
  `chartPhaseVFTime_uncurry_contDiffOn_univ_nat` (arbitrary-order regularity).
  Watch the "parametric smoothness" gap flagged in `Analysis/ODE`.
- **Possible shortcut (math group: please assess).** `bochner_radial_riccati`'s
  hypothesis says `∞` but the theorem only assumes `[IsManifold I 2 M]` and the
  Hessian argument morally needs only *finite* order (≈ C³). If we weaken the
  hypothesis to `ContMDiff I 𝓘 n` for a fixed finite `n`, L0 only needs `exp`
  lifted to that finite order (which SmoothFlow's arbitrary-`Nat` regularity gives
  directly) — strictly easier than `∞`.
- **References.** Lee *Intro to Riemannian Manifolds* (2e) **Ch 5** (geodesics &
  the exponential map, smoothness/smooth dependence). Petersen *Riemannian
  Geometry* (3e) **Ch 5** (Geodesics and Distance). Smooth dependence on initial
  conditions for ODEs (the C∞ flow) — Lee *Smooth Manifolds* (the ODE appendix).

#### B2. Eikonal identity `|∇r|² = 1`  (Gauss lemma)
- **`≤ 1` half — ✅ done.** `manifoldGradient_metricInner_self_le_one`
  (`Operators/Gradient.lean`). From `(d r(v))² ≤ |v|²_g` (1-Lipschitz of `dist`).
  - **Still needed for `≤1`: ❌** the geometric bound `(d(dist p ·)(v))² ≤ |v|²_g`
    from `dist` being 1-Lipschitz w.r.t. `riemannianEDist` (the inf-path-length
    metric) — the `riemannianEDist ↔ g`-norm infinitesimal bridge.
- **`≥ 1` half — ❌  ⚠ HIGHEST RISK (the "open question").** Needs the radial
  isometry `dist p (exp_p v) = |v|` ⇒ along a unit radial geodesic `dr(γ') = 1`,
  `|γ'| = 1`, Cauchy–Schwarz ⇒ `|∇r| ≥ 1`. This is **first-variation / Gauss-lemma
  / minimizing-geodesic** machinery. Self-building it without a variation cone is
  the riskiest item in Route A — **math group: prioritize finding the cleanest
  reference proof here.**
- **References.** **Gauss lemma**: Lee (2e) **Ch 6** (geodesics and distance, the
  Gauss lemma & radial isometry); Petersen (3e) **Ch 5**. Minimizing geodesics in
  the normal ball: Lee **Ch 6**.

#### B3. Bochner radial Riccati  `a' + a² + κ ≤ 0`  — ✅ done
- `bochner_radial_riccati` (`Comparison/BishopGromov/RadialRiccati.lean`), the
  scalar Riccati from the Bochner identity (bypassing Jacobi fields), + the
  eikonal-kernel lemma. Refined Cauchy–Schwarz `(tr S)² ≤ (n−1)|S|²`
  (`Comparison/Util/RefinedCauchySchwarz.lean`) — ✅.
- **References.** **Bochner formula** `Δ(½|∇r|²) = |Hess r|² + ⟨∇r,∇Δr⟩ +
  Ric(∇r,∇r)`: Petersen (3e) **Ch 7 (The Bochner Technique)**; Lee (2e) Ch 11
  (Riccati form). Laplacian/mean-curvature comparison: Petersen **Ch 9**.

#### B4. Riccati comparison  `a ≤ ā = ct_κ`  — ✅ done
- `riccati_le_model` (`RiccatiComparison.lean`), variable-coeff ODE comparison via
  the `s_κ²` integrating factor.
- **References.** Lee (2e) **Ch 11** (Jacobi fields, Hessians, and Riccati
  equations); Petersen (3e) **Ch 6 / Ch 9**.

#### B5. Construct `RadialLaplacianProfile`  ❌  (the leg-[B] discharge)
Fields to provide (LaplacianComparison.lean): `profile`, `eval`
(`profile (dist p x) = scalarLaplacian g (dist p ·) x`), `radius_mem`,
`differentiableAt`, `riccati_sub` (← **B3** + **B2**), `asymptotic`
(`m(s) − (n−1)/s → 0` as `s→0⁺`).
- `riccati_sub` ⇐ `bochner_radial_riccati` once `dist` is `C∞` (B1) and the
  eikonal holds (B2).
- `eval` / `differentiableAt` ⇐ `dist` smooth off the cut locus + the radial
  structure of `r`.
- `asymptotic` ⇐ base-point Euclidean asymptotics (`d exp|₀ = id`).
- **References.** Laplacian comparison theorem & the `Δr ~ (n−1)/r` asymptotic:
  Petersen (3e) **Ch 9**; Lee (2e) **Ch 11**.

### Leg [C] — polar volume formula  ⇒ `BishopGromovVolumeData`

> Leg [C] needs only `C¹` exp (does **not** depend on L0). It is the
> CH21-aligned (Jacobi-determinant) leg and is already well advanced.

#### C1. Exp-volume change of variables  — ✅ done
- `exists_volumeMeasure_expImage_eq_setLIntegral_jacobian` and the change-of-vars
  core (`Volume/ExpBridge.lean`); `volumeMeasure_eq_setLIntegral_chartSqrtGramDet`
  and the chart-pullback keystone (`Volume/ChartPullbackFormula.lean`);
  local-finiteness & `volumeFormAt` (`Volume/ChartPullback.lean`, `VolumeForm.lean`)
  — ✅ (the latter two closed 2026-06-15).

#### C2. Volume Jacobian, polar form `det d exp_p(tξ) = t^{n−1} J_ξ(t)`  🔶
- `det_dExpMap_jacobiField_decomp` (`Volume/Exponential.lean`), positivity
  `chartExp_volumeJacobian_pos` (`ExpBridge.lean`) — done/partial. Remaining: the
  full polar `t^{n−1}` extraction + the radial Jacobi-field area density `J_ξ(t)`.
- **References.** CH21 (`references/.../CH21.tex`, the `j(v,t)` density and
  `∂_t j = tr(S) j`); Petersen (3e) **Ch 9**; Lee (2e) **Ch 10–11** (Jacobi
  fields & comparison).

#### C3. Radial log-derivative bridge `∂_t log J = Δr`  ❌
- Connects the volume-Jacobian derivative to the Laplacian of `dist` (= mean
  curvature of geodesic spheres = `tr S`). This is what lets leg-[B]'s
  `Δr ≤ m_κ` feed `ratio_antitone`.
- **References.** CH21 (`∂_t j = tr(S) j`, lines ≈170–189); Petersen (3e) **Ch 9**;
  Lee (2e) **Ch 11**.

#### C4. Cut locus has measure zero + `vol B(p,R) = ∫₀ᴿ A(t) dt`  ❌
- `exp_p : B(0,r) ∩ C_p → B(p,r)∖cut(p)` is a diffeomorphism, `cut(p)` is
  measure-zero, so the polar volume formula holds. `A(t)` is the geodesic-sphere
  area `∫_{S^{n−1}} J(v,t) dvol`.
- **References.** CH21 (the "Fact" + polar volume, lines ≈248–264); Lee (2e)
  **Ch 10** (cut points); Petersen (3e) **Ch 5 / Ch 9**.

#### C5. Monotone average integral  — ✅ done
- `ratio_intervalIntegral_le` (`Comparison/BishopGromov/VolumeMonotone.lean`) +
  `ratio_spaceFormBallVolume_le` (`PolarVolumeReduction.lean`).
- **References.** CH21 (Lemma "monotone average integral", lines 6–42); Petersen
  (3e) **Ch 9**.

#### C6. Construct `BishopGromovVolumeData`  ❌  (the leg-[C] discharge)
Fields (VolumeComparison.lean): `area`, `vol_eq` (← **C4**), `area_integrable`,
`ratio_antitone` (← **C3** + leg-[B] `Δr ≤ m_κ`).

---

## 2. Engineering task list (this branch)

In dependency order. `[ ]` = to build, `[~]` = partial, `[x]` = done.

**Leg [B]**
- [ ] **B1 / L0** — lift `expMap` C¹→C∞ (or to a fixed finite order, pending B1's
      shortcut assessment). ~7 files in `Exponential/Smoothness/*` +
      `LocalDiffeomorphism.lean`, parameterized over order via SmoothFlow.
- [~] **B2** — eikonal `|∇r|²=1`: `≤1` algebra done; build (i) the 1-Lipschitz
      `riemannianEDist`↔`g`-norm bound (`≤1` closure), (ii) **`≥1` via Gauss
      lemma / radial isometry** ⚠.
- [x] **B3** Bochner radial Riccati · [x] **B4** Riccati comparison · [x] refined CS.
- [ ] **B5** — construct `RadialLaplacianProfile` ⇒ `laplacian_comparison`
      unconditional.

**Leg [C]**
- [x] **C1** exp-volume change of variables + volume-measure substrate.
- [~] **C2** polar `det d exp_p(tξ) = t^{n−1} J_ξ(t)`.
- [ ] **C3** `∂_t log J = Δr`.
- [ ] **C4** cut locus measure-zero + polar `vol B(p,R) = ∫₀ᴿ A`.
- [x] **C5** monotone average integral.
- [ ] **C6** — construct `BishopGromovVolumeData` ⇒ `bishopGromov_volume_comparison`
      unconditional.

**Finish**
- [ ] Drop the `(data)` arguments from the two headline theorems (their proof
      bodies are already written against the interfaces) → BG unconditional.

---

## 3. References & PDFs

### Primary (the project's own notes)
- `references/arXiv-2404.09792v2/CH21.tex` — the Bishop–Gromov chapter (ground
  truth). NB: CH21 follows the **Jacobi/shape-operator** route; use it directly
  for leg [C] (the `j(v,t)` density, `∂_t log j = tr S`, polar volume, cut locus)
  and the monotone-average lemma.

### John M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed. (GTM 176, 2018)
- Author's book page: <https://sites.math.washington.edu/~lee/Books/RM/>
- Springer full PDF: <https://link.springer.com/content/pdf/10.1007/978-3-319-91755-9.pdf>
- Front matter / TOC (author): <https://sites.math.washington.edu/~lee/Books/RM/front-matter.pdf>
- Relevant chapters: **Ch 5** exponential map / geodesics (B1 smoothness),
  **Ch 6** geodesics & distance — Gauss lemma, radial isometry (B2),
  **Ch 10** Jacobi fields, conjugate & cut points (C2, C4),
  **Ch 11** Comparison Theory — Jacobi/Hessian/Riccati, Ricci comparison,
  Laplacian comparison (B3–B5, C3).

### Peter Petersen, *Riemannian Geometry*, 3rd ed. (GTM 171, 2016)
- Author's full PDF: <https://www.math.ucla.edu/~petersen/RG.pdf>
- Relevant chapters: **Ch 5** Geodesics and Distance (B1, B2),
  **Ch 7** The Bochner Technique (B3 — the Bochner formula),
  **Ch 9** Ricci Curvature Comparison — Bishop–Gromov, relative volume
  comparison, Laplacian/mean-curvature comparison, segment inequality (B3–B5,
  C3–C6).

> **Math group:** please verify the exact section/page numbers above against the
> linked PDFs and pin them to each task (the chapter mapping is best-effort; the
> section granularity needs confirming). Flag any place where Lee/Petersen's
> hypotheses (completeness, smoothness order, cut-locus treatment) differ from
> what the OpenGALib lemma actually needs — especially **B1's finite-order
> shortcut** and **B2's `≥1` Gauss-lemma route**.

---

## 4. Owners & roles

**Math group** — verify the references above are accurate and sufficient, pin
exact sections, and resolve the two flagged risks (B1 finite-order shortcut, B2
`≥1` Gauss lemma):
- Zhifei Zhu — `@zhifeizhu92`
- Chunlei Liu (YiuYiu Happy) — `@YiuYiu-Happy`

**Engineering group** — build the remaining Lean engineering on this branch per
the task list in §2:
- Leheng Chen — `@LehengChen`

---

*Generated 2026-06-15. Route A = Bochner. Branch: `feat/bishop-gromov`.*
