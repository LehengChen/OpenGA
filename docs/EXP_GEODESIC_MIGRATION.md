# Exponential-map / geodesic layer migration — scope, cone, staged plan

**Status (2026-06-14):** scoping complete. **Stage 2 (ODE bedrock) DONE** —
`OpenGALib/Analysis/ODE/Flow/` (8 files, 0 sorry, 0 version drift): the
Picard–Lindelöf variational equation + C1/Ck flow regularity, self-contained on
Mathlib, rehomed to namespace `Analysis.ODE`. Next: geodesic layer.

**Decisions (confirmed with Moqian):**
- *Reuse our foundation, migrate only new content* — do not lift external's
  dedup-able Connection/Operator/Metric/Curvature/Tensor (76 files / 38k lines);
  rewire the new geometric code onto `OpenGALib.Riemannian.*` / `OpenGALib.Tensor.*`.
- *Homing*: ODE → `OpenGALib/Analysis/ODE/` (ns `Analysis.ODE`); geodesics/exp/
  Gauss → `OpenGALib/Riemannian/{Geodesic,Exponential}/` (ns `Riemannian.Geodesic`,
  `Riemannian.Exponential`).
- `SmoothRiemannianMetric` ≡ our `RiemannianMetric` (same `ContMDiffRiemannianMetric`
  abbrev) — trivial rename on lift.

**Geodesic layer note:** `Geometry/Geodesic/Equation` defines geodesics via
chart-local Christoffel symbols (`γ'' = -Γ(γ',γ')`) computed directly from the
metric in coordinates — a thin foundation slice (chart Gram + metric), not the
full 29-file external Connection cone.

**Progress (chart-Christoffel foundation, committed, 0 sorry):**
- `OpenGALib/Riemannian/Metric/ChartGram.lean` — `chartModelBasis`,
  `chartGramMatrix` (+Hermitian/posDef/det/smoothness), on our `RiemannianMetric`.
- `OpenGALib/Riemannian/Connection/ChartChristoffel.lean` — `partialDeriv`,
  `chartInvGramMatrix`, `chartGramOnE`, `chartChristoffel` (+lower-index symmetry).

**Chart-Christoffel smoothness sub-layer DONE** (committed, 0 sorry):
`OpenGALib/Riemannian/Connection/ChartChristoffelSmooth.lean` — adjugate →
inverse-Gram → Gram/InvGram-on-E → `chartChristoffel_contDiffOn_interior`, plus
the chart helpers (`extChartAt_source_eq_chartAt_source`,
`trivializationAt_baseSet_eq_chartAt_source`,
`extChartAt_target_subset_interior_of_boundaryless`).

**`Geodesic/Equation` DONE** (committed, 0 sorry):
`OpenGALib/Riemannian/Geodesic/Equation.lean` — `geodesicVectorField`,
`HasGeodesicEquationAt` (`γ''=-Γ(γ',γ')`), `IsGeodesic{,At,On}`, affine
reparametrization (shift / time-reversal), chart-fixed smoothness. v4.30 deriv
drift fixed via `import Mathlib.Analysis.Calculus.Deriv.{Add,Shift}`.

**⚠ Dedup lesson (2026-06-14):** the first geodesic-foundation pass *duplicated*
existing OpenGALib infrastructure. OpenGALib already had the full chart-Gram
stack — `TensorBundle/MusicalIso` (`chartGramMatrix`, `chartInvGramMatrix`,
Hermitian/posDef/det/adjugate/inverse **smoothness**) and `SmoothOrthoFrame/
ChartBasis` (`chartBasisVecFiber`, on `Module.finBasis ℝ E`). The migrated
`Metric/ChartGram.lean` and the adjugate/inverse smoothness in
`ChartChristoffelSmooth` were duplicates on a parallel `chartModelBasis` frame.
**Fixed**: deleted `ChartGram.lean`, rebased `ChartChristoffel{,Smooth}` and
`Geodesic/Equation` onto the existing `MusicalIso` Gram + `Module.finBasis`
frame. **Rule going forward: before lifting any external file, grep OpenGALib
for the symbols it defines; reuse, don't duplicate.**

**Deduped state (committed, 0 sorry):** genuinely-new content only —
`Connection/ChartChristoffel` (`chartGramOnE`, `chartChristoffel` +symm,
`partialDeriv`), `Connection/ChartChristoffelSmooth` (pulled-back smoothness +
`chartChristoffel_contDiffOn_interior` + chart helpers), `Geodesic/Equation`
(`IsGeodesic`, `HasGeodesicEquationAt`, …), all on existing OpenGALib foundation.

**Next:** rest of `Geometry/Geodesic` bottom-up — `Existence`, `Uniqueness`,
`MaximalInterval`, `SmoothFlow` (consumes the migrated `Analysis.ODE.Flow`),
then the `Geometry/Exponential` layer (`expMap`, smoothness, Gauss lemma) —
**grepping OpenGALib for each file's symbols first.**

---

**Goal:** supply the three geometric facts that gate `LaplacianComparison`
(`Comparison/BishopGromov/LaplacianComparison.lean`) and, downstream,
`bishopGromov_volume_comparison`:

1. eikonal `|∇r|²_g = 1` for `r = dist p ·` on the smooth locus (Gauss lemma);
2. radial-derivative identification `⟨∇r, ∇(Δr)⟩ = (d/dt) (Δr ∘ γ)` along unit
   geodesics;
3. base-point asymptotic `Δr ∼ (n-1)/r` as `r → 0⁺`.

The Bishop–Gromov **ODE / analytic core is already complete and 0-sorry**
(`riccati_le_model`, `bochner_radial_riccati`, `RefinedCauchySchwarz`); these
three facts are the only remaining inputs, and all three rest on the smooth
exponential map, which neither OpenGALib nor Mathlib `v4.30` currently has
(Mathlib `Geometry/Manifold/Riemannian/` has only `Basic` + `PathELength`).

## Source

`external/differential-geometry` (reference only; never committed) has a
complete exp-map / geodesic / Gauss-lemma development under
`DifferentialGeometry/Geometry/{Exponential,Geodesic}` and
`DifferentialGeometry/Analysis/ODE`. It is on Lean `v4.29` and uses
`SmoothRiemannianMetric I M`; OpenGALib is `v4.30` and uses `RiemannianMetric`.

## Dependency cone (measured)

Transitive closure of the four target modules — `Exponential.GaussLemma`,
`GaussLemmaPullback`, `LocalDiffeomorphism`, `MinimizingGeodesic`:

| | files | lines |
|---|---|---|
| **Total cone** | 159 | 92,898 |
| — foundation, dedup-able to OpenGALib (Connection, Curvature, Operator, Metric, Tensor/*) | 73 | 37,111 |
| — **genuinely new** (Analysis/ODE, Geodesic, Exponential, exp-specific Comparison) | 86 | 55,787 |

The new-content subdir breakdown (top): `Analysis/ODE` (≈30k lines — the
Picard–Lindelöf + smooth-dependence-on-initial-conditions ODE machinery Mathlib
lacks), `Geometry/Exponential` (27 files), `Geometry/Geodesic` (14 files),
`Geometry/Comparison` (exp-specific: NormalCoordinates, InjectivityRadius,
Variation/SecondVariation).

**The exponential map drags in a ~30k-line ODE-smoothness foundation** — this is
why the cone is far larger than the 45-file / 30k-line `Exponential+Geodesic`
directories alone.

## Convention / version gaps to fix on lift

- `SmoothRiemannianMetric I M` → `RiemannianMetric I M` (the divergence-theorem
  migration already established this rewrite).
- Lean `v4.29` → `v4.30` drift (the divergence migration hit
  `ContinuousMultilinearMap` instance changes, `borel` measure mismatches; fix
  per file).
- Namespace/path: `DifferentialGeometry.*` → `OpenGALib.*`; remap the
  dedup-able foundation imports onto existing `OpenGALib.Riemannian.*` /
  `OpenGALib.Tensor.*` modules rather than lifting duplicates.
- House style: single `**Math.**`/`**Eng.**` tag, `Provenance:` footers,
  namespace = directory.

## Staged bottom-up plan

The cone has 14 Mathlib-only leaves; lift order is forced bottom-up (nothing
builds until its cone is present). Proposed stages:

1. **Foundation remap audit** — for each of the 73 dedup-able files, decide
   remap-to-existing vs lift. Produces the import-rewrite map. *(no new proofs)*
2. **ODE bedrock** (`Analysis/ODE`, ≈30k lines) — Picard–Lindelöf, flow
   regularity, smooth dependence, variational ODE. The hardest, most technical
   slice; gates everything geometric.
3. **Geodesic layer** (`Geometry/Geodesic`) — geodesic equation, maximal
   interval, smooth flow, chart transition.
4. **Exponential layer** (`Geometry/Exponential`) — `expMap`, smoothness off
   zero, local diffeomorphism, exp-variation smoothness.
5. **Gauss lemma + minimizing geodesics** — the eikonal/radial facts.
6. **Extract the three `LaplacianComparison` inputs** and close
   `laplacian_comparison`, then `bishopGromov_volume_comparison`.

## Note on alternatives

Given the ~56k-line genuinely-new scale (Stage 2 alone is a ~30k-line ODE
foundation yielding no visible Bishop–Gromov progress until Stage 5), a hybrid
is worth weighing: define the three facts as a faithful **geometric interface**
(a `structure`/typeclass — smooth distance with eikonal + radial structure +
asymptotic), prove `laplacian_comparison` and `bishopGromov_volume_comparison`
to **0-sorry-modulo-interface** now (completing the headline contribution's
logical shape), and let the staged migration *discharge* that interface
bottom-up afterwards. The interface and the migration are not exclusive; the
interface unblocks the headline while the migration proceeds underneath.
