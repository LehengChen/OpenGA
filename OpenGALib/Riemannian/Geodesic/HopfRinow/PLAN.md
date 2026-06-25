# Hopf–Rinow — Level-2 build plan (branch `feat/hopf-rinow`)

Goal: prove Hopf–Rinow (CH2) unconditionally, as the upstream the Bishop–Gromov
volume side (CH21) cites. Faithful to **do Carmo, *Riemannian Geometry*, Ch. 7**
(geodesic-sphere + connectedness argument — NO Morse / second variation / spray).

`HopfRinow.lean` (the facade, one level up) holds the statement + corollaries with
the do-Carmo proof blueprint. This folder builds the upstream stack it needs.

## Dependency stack (bottom-up). Build in this order.

| # | Piece | File (this folder) | Depends on | Status |
|---|-------|--------------------|------------|--------|
| ① | `dist = ⨅ pathLength` (metric = Riemannian length) | `EVariationLePathELength.lean` + fix `Bridges/RiemannianToLength.lean` | Mathlib `pathELength`, `riemannianEDist_le_pathELength`, `pathELength_add/mono`, `IsRiemannianManifold.out` (all ✅) | **doing now** |
| ② | `d(exp_p)_v(w) = J(1)` (exp ↔ Jacobi field, general `v`) | `ExpJacobi.lean` | OpenGALib Jacobi infra (`JacobiFrame`, `JacobiDeterminant`); `mfderiv_expMap_at_zero` (only `v=0` exists) | missing core |
| ③ | `d exp_p` radial isometry (Gauss inner-product) | `GaussInnerProduct.lean` | ② + Jacobi `⟨J,γ̇⟩` (`JacobiFrame.hasDerivAt_metricInner_covDeriv_jacobi` 🟡) | not started |
| ④ | Gauss lemma `dist(exp_p v, p) = ‖v‖` | `GaussLemma.lean` | ① + ③ + minimization | not started |
| ⑤ | Hopf–Rinow (main ⟺ + corollaries) | `../HopfRinow.lean` (facade) | ④ + ① + geodesic extension (`MaximalInterval`) | statement + blueprint only |
| ⑥ | (consumer) BG volume side | `Comparison/BishopGromov/...` | ⑤ + cut-locus measure-0 + polar volume + Jacobi spine (spine ✅) | out of this folder |

## ① proof map (the one feasible-now bottom)

```
⨅_{γ:Path x y} pathLength γ ≤ edist x y
  = riemannianEDist            -- IsRiemannianManifold.out
  = ⨅_{γ:Path}(_:CMDiff 1 γ) ∫‖mfderiv γ‖
  le_iInf₂ ⟹ ∀ C¹ γ: ⨅ pathLength ≤ ∫‖mfderiv γ‖
  iInf_le γ ⟹           pathLength γ ≤ ∫‖mfderiv γ‖
  = KEY LEMMA  eVariationOn (γ:I→M) univ ≤ pathELength I γ 0 1
       proof: eVariationOn = ⨆_partitions Σ edist(γ tᵢ, γ tᵢ₊₁)
              ≤ ⨆ Σ pathELength I γ tᵢ tᵢ₊₁        (edist = riemannianEDist ≤ pathELength)
              = pathELength I γ 0 1                 (pathELength_add telescoping)
```
~80–100 LOC; the only intricate part is the unit-interval (`Path` subtype) ↔ `ℝ→M`
coercion bookkeeping and the eVariationOn sup API.

## Hard-won non-goals (do NOT build — off CH21's path, see ../../../../docs/BG_UPSTREAM_INTERFACE.md)

Morse index / index form, spray / geodesic-flow cocycle, Hopf–Rinow "weak-to-strong
minimizer regularity". do Carmo's proof uses none of these. The snapshot
`openga-bg-buildable-*` (45-file `HopfRinow/`) over-built exactly these + shipped
false statements; we do NOT inherit it.
