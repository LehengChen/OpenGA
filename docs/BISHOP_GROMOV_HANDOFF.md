# Bishop–Gromov formalization — handoff

**Goal:** the COMPLETE Bishop–Gromov volume-comparison proof in OpenGALib, no
interface shortcuts. Headline target: `bishopGromov_volume_comparison` in
`OpenGALib/Comparison/BishopGromov/VolumeComparison.lean` (currently `sorry`).

**Resume branch:** `feat/exp-geodesic-migration` (contains everything below;
branched off `feat/bishop-gromov` which holds the analytic core). Working tree
is clean. Everything committed builds with **0 sorry, 0 warnings**.

**Math reference:** the user's own notes `references/arXiv-2404.09792v2/CH21.tex`
(the Bishop–Gromov chapter — actually read, grounded). Standard texts (do Carmo
Ch.10, Petersen Ch.9, Cheeger–Ebin) are recalled from training, not re-read.
Precise CH21 line map is in `docs/EXP_GEODESIC_MIGRATION.md`.

---

## DONE (all 0 sorry, committed)

### Analytic engines (the two ends of BG, pure analysis)
- **Riccati comparison → `Δr ≤ m_K`** (on `feat/bishop-gromov`):
  - `Comparison/Util/SnakeCalculus.lean` — snake function `s_K`, Jacobi ODE,
    model Riccati, asymptotics.
  - `Comparison/BishopGromov/RiccatiComparison.lean` — `riccati_le_model`
    (variable-coeff ODE comparison via the `s_K²` integrating factor).
  - `Comparison/BishopGromov/RadialRiccati.lean` — `bochner_radial_riccati`
    (the scalar Riccati sub-equation FROM the Bochner identity, bypassing the
    classical Jacobi-field/matrix-Riccati route), eikonal-kernel lemma.
  - `Comparison/Util/RefinedCauchySchwarz.lean` — `(trace S)² ≤ (n-1)‖S‖²` with a
    unit kernel vector (the `n→n-1` sharpening).
- **Volume-ratio monotonicity** (`feat/exp-geodesic-migration`):
  - `Comparison/BishopGromov/VolumeMonotone.lean` — `ratio_intervalIntegral_le`:
    `A/B` antitone + `B>0` ⟹ `(∫₀ᴿA)/(∫₀ᴿB)` antitone. CH21 "monotone average
    integral", weighted form, pivot on `q(r)` (no double integral).

### Geometry foundation (migration from `external/differential-geometry`, reference-only)
- **ODE smooth-dependence bedrock**: `OpenGALib/Analysis/ODE/Flow/` (8 files) —
  Picard–Lindelöf variational equation + C1/Ck flow regularity (ns `Analysis.ODE`).
- **Chart Christoffel**: `Riemannian/Connection/ChartChristoffel{,Smooth}.lean` —
  `chartChristoffel`, smoothness; rebased onto the EXISTING `TensorBundle/MusicalIso`
  Gram infra + `Module.finBasis ℝ E` (after a dedup catch — see lessons).
- **Geodesic layer**: `Riemannian/Geodesic/` (9 files) — `Equation`
  (`γ''=−Γ(γ',γ')`), `Existence`, `Uniqueness`, `Smoothness`, `MaximalInterval`,
  `SmoothFlow` (flow smoothness via the ODE bedrock), `Homogeneity`,
  `GeodesicEquationFromIntegralCurve`, `MaximalRescaling`.
- **Exponential map (local diffeomorphism at 0)**: `Riemannian/Exponential/`
  (18 files) — `Defs` (`expMap p v = γ_v(1)`), `Smoothness/MfderivZero`
  (`d expₚ|₀ = id`), `LocalDiffeomorphism`, supporting `ChartFlow/*` + `Smoothness/*`.
  **No heavy SecondVariation cone** (that is pulled only by the deferred
  `ExpVariationSmooth`).

---

## CRITICAL PATH TO THE HEADLINE (what remains)

```
expMap (✅ def + local diffeo at 0)
  ├─→ [B] Gauss lemma → smooth eikonal |∇r|²=1  ──→ laplacian_comparison: Δr ≤ m_K
  │        (uses bochner_radial_riccati ✅ + riccati_le_model ✅)
  └─→ [C] volume Jacobian J(t,ξ) + ∂_t log J = Δr + geodesic-polar volume formula
           vol B(p,R) = ∫₀ᴿ A(t) dt,  A(t)/A_K(t) antitone
                                   ↓
              ratio_intervalIntegral_le ✅  →  bishopGromov_volume_comparison
```

**Verified facts about the remaining work:**
- external has the exp map + geodesics + the *metric* Gauss lemma + ODE/chart
  smoothness, but **NOT** the smooth eikonal `|∇r|=1`, the volume Jacobian,
  `∂_t log J = Δr`, the polar volume formula, or BG itself (full-library grep).
  Those are **build-ourselves** (reuse OpenGALib's `Riemannian/Volume/` +
  migrated divergence theorem).
- Both [B] and [C]'s *full* versions need exp smoothness on the whole normal ball,
  i.e. `Exponential/ExpVariationSmooth` → which pulls a heavy cone:
  **~25k genuinely-new lines** (`Geometry/Comparison/Variation` second-variation +
  parallel-transport-along-curve + InjectivityRadius/HopfRinow + IntrinsicExp) +
  ~21 dedup-able foundation files to reconcile. This is the big remaining migration.

---

## RECOMMENDED NEXT STEPS (in order)

1. **Small reachable 0-sorry adapter (was mid-flight, not started):** in a new
   `Comparison/BishopGromov/PolarVolumeReduction.lean`, prove that
   `(∫₀ᴿ A)/(spaceFormBallVolume n K R)` is antitone given `A / (model area
   density)` antitone — by unfolding `spaceFormBallVolume n K R =
   n·ωₙ·∫₀ᴿ max(0,s_K)^(n-1) = ∫₀ᴿ B_K` (`intervalIntegral.integral_const_mul`)
   and applying `ratio_intervalIntegral_le`. Needs `snakeFunction_pos`
   (have, `SnakeCalculus`) for `B_K>0` on the window. This is the headline's
   analytic glue, reachable now, no geometry. (See `SpaceForm.spaceFormBallVolume`.)
2. **The big chunk — migrate `ExpVariationSmooth` + its `Comparison/Variation`
   cone** (~25k new lines, bottom-up: parallel-transport-along-curve →
   first/second variation → IntrinsicExp → ExpVariationSmooth). This unblocks
   both [B] and [C].
3. **[B] smooth eikonal** `|∇r|²=1` (from the migrated Gauss lemma) →
   discharge `laplacian_comparison`'s hypotheses, feeding `bochner_radial_riccati`.
4. **[C] volume Jacobian** + `∂_t log J = Δr` + polar volume → feed
   `ratio_intervalIntegral_le` → close `bishopGromov_volume_comparison`.

---

## CONVENTIONS & LESSONS (do not relearn the hard way)

- **DEDUP FIRST.** Before migrating ANY external file, `grep -rn 'def <symbol>'
  OpenGALib/` for the symbols it defines. OpenGALib already had the whole
  chart-Gram stack (`TensorBundle/MusicalIso`: `chartGramMatrix`,
  `chartInvGramMatrix`, smoothness; `SmoothOrthoFrame/ChartBasis`:
  `chartBasisVecFiber`, `Module.finBasis`-based) — a first pass duplicated it.
  Reuse ours, don't lift duplicates.
- **Reuse our foundation, migrate only new content** (user's explicit decision).
  `SmoothRiemannianMetric` ≡ our `RiemannianMetric` (same `ContMDiffRiemannianMetric`
  abbrev — just rename on lift).
- **Homing:** ODE → `OpenGALib/Analysis/ODE/` (ns `Analysis.ODE`); geodesics/exp →
  `OpenGALib/Riemannian/{Geodesic,Exponential}/` (ns `Riemannian.Geodesic` /
  `Riemannian.Exponential`).
- **Basis rebase:** external uses `chartModelBasis E`; OpenGALib's Gram infra uses
  `Module.finBasis ℝ E`. Rewrite `chartModelBasis E` → `Module.finBasis ℝ E` on
  lift (geometrically equivalent; any consistent chart basis works).
- **Lift mechanics:** the per-file sed rewrites are in `scripts/lift-diffgeo.sh`
  (Analysis) and the inline geodesic/exp seds in the transcript. They rewrite
  `import DifferentialGeometry.X` → `OpenGALib...`, drop the
  `namespace DifferentialGeometry`/`Geometry` wrappers, drop vestigial
  `open DifferentialGeometry.Integral.*`, rename the metric, rebase the basis.
  **BSD sed has no `\b`; zsh does NOT word-split unquoted vars** (use a bash
  array `for f in "${arr[@]}"`).
- **v4.29 → v4.30 drift seen:** `deriv_comp_add_const`/`deriv_comp_neg`/
  `hasDerivAt_neg` moved to `Mathlib.Analysis.Calculus.Deriv.{Add,Shift}` (add the
  imports); `Mathlib.MeasureTheory.Integral.FundThmCalculus` is gone;
  `div_le_div_iff` → `div_le_div_iff₀`; `integral_mono_on_of_le_Ioo` (NoAtoms)
  dodges the `r=0` endpoint where the model area vanishes.
- **Trim vestigial imports/lemmas:** e.g. `MaximalInterval` imported a ~53k
  `SecondVariation` cone but only used a couple of arc-length lemmas — trimmed
  them out. Check actual symbol usage before lifting a file's whole cone.
- **Linter cleanup per migrated file:** `**Math.**` tag on docstrings (the content
  is all math) via `perl -i -pe 's{/-- (?!\*\*(?:Math|Eng|Mixed)\.)([^\n])}
  {/-- **Math.** $1}g'`; `set_option linter.unusedSectionVars false` after the
  last import. mathTag fires only on `Riemannian.*`, not `Analysis.*`.
- **Never** give calendar-time estimates; commit messages on this repo omit the
  Claude co-author trailer; build per-file (LSP) during iteration, full
  `lake build` only before committing.
