import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional

/-!
# Composition operations for continuous multilinear maps

Continuity and smoothness of pre-composition of continuous multilinear maps
with a diagonal continuous linear map (`p ↦ compContinuousLinearMapL (fun _ ↦ p)`).

## Main results

* `ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous`: continuity.
* `ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff`: `C^∞`,
  given finite-dimensional fibers.

The smoothness proof bypasses the `ContinuousLinearMap.addCommMonoid` vs.
`NormedAddCommGroup`-derived `AddCommMonoid` instance diamond on `F₁ →L[𝕜] F₁`
by reducing via `contDiff_clm_apply_iff` (which requires finite-dimensional
codomain) and then using `CPolynomialAt.contDiffAt` together with Mathlib's
`ContinuousMultilinearMap.cpolynomialAt_uncurry_compContinuousLinearMap`. The
intermediate `CPolynomialAt` lemma operates on `(p, β)`-bivariate functions
into `CMM`, where the only relevant instances are on `F₁` (no diamond) and
on the `CMM` itself (Banach space, no diamond).
-/

noncomputable section Comp

namespace ContinuousLinearMap

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace 𝕜 M]
  {M' : Type*} [NormedAddCommGroup M'] [NormedSpace 𝕜 M']
  {N : Type*} [NormedAddCommGroup N] [NormedSpace 𝕜 N]
  {ι : Type*} [Fintype ι]

/-- The map sending `p : M →L[𝕜] M'` to `compContinuousLinearMapL (fun _ ↦ p)`
(pre-composing all `ι` slots of a continuous multilinear map with the same `p`)
is continuous. -/
theorem compContinuousMultilinearMapL_diag_continuous :
    Continuous (fun p : M →L[𝕜] M' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ M') N →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ ↦ M) N)) := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ M →L[𝕜] M') _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      𝕜 (fun _ : ι ↦ M) (fun _ : ι ↦ M') N
  change Continuous (fun p : M →L[𝕜] M' ↦ φ (fun _ : ι ↦ p))
  exact φ.cont.comp (continuous_pi (fun _ ↦ continuous_id))

end ContinuousLinearMap

section Continuous

variable
  (𝕜 : Type*) [NontriviallyNormedField 𝕜]
  (ι : Type*) [Fintype ι]
  (F₁ F₂ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [ContinuousAdd F₁]

/-- Continuity of `p ↦ compContinuousLinearMapL (fun _ ↦ p)` in the
endo-domain case `F₁ →L[𝕜] F₁`. -/
theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_continuous :
    Continuous (fun p : F₁ →L[𝕜] F₁ ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂)) := by
  let φ : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁ →L[𝕜] F₁) _ :=
    ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      𝕜 (fun _ : ι ↦ F₁) (fun _ : ι ↦ F₁) F₂
  change Continuous (fun p : F₁ →L[𝕜] F₁ ↦ φ (fun _ : ι ↦ p))
  exact φ.cont.comp (continuous_pi (fun _ ↦ continuous_id))

end Continuous

section Smooth

variable {𝕜 ι F₁ F₂ : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [Fintype ι]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]

/-- `CMM 𝕜 E F → MM 𝕜 E F` as a `LinearMap`, used to transport
finite-dimensionality from the algebraic multilinear-map module to the
continuous one. -/
def ContinuousMultilinearMap.toMultilinearMapₗ :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ →ₗ[𝕜]
      MultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ where
  toFun := ContinuousMultilinearMap.toMultilinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance ContinuousMultilinearMap.instFiniteDimensional :
    FiniteDimensional 𝕜
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) := by
  refine FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapₗ (𝕜 := 𝕜) (ι := ι)
      (F₁ := F₁) (F₂ := F₂)) ?_
  exact ContinuousMultilinearMap.toMultilinearMap_injective

/-- The map `p ↦ compContinuousLinearMapL (fun _ ↦ p)` is `C^∞` when `F₁` and
`F₂` are finite-dimensional.

Proof strategy: reduce via `contDiff_clm_apply_iff` (codomain
`CMM 𝕜 (fun _ ↦ F₁) F₂` is finite-dimensional) to fixed-`β` smoothness, then
use `CPolynomialAt.contDiffAt` with the bivariate Mathlib lemma
`cpolynomialAt_uncurry_compContinuousLinearMap` composed with a
continuous-linear "diagonal-and-pad" map. -/
theorem ContinuousMultilinearMap.compContinuousLinearMapL_diag_contDiff :
    ContDiff 𝕜 ⊤ (fun p : F₁ →L[𝕜] F₁ ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) :
        ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂ →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ ↦ F₁) F₂)) := by
  rw [contDiff_clm_apply_iff]
  intro β
  rw [contDiff_iff_contDiffAt]
  intro p
  -- `p ↦ compContinuousLinearMapL (fun _ ↦ p) β = β.compContinuousLinearMap (fun _ ↦ p)`
  -- factors as `(q ↦ q.2.compContinuousLinearMap q.1) ∘ (p ↦ ((fun _ ↦ p), β))`
  -- where the first is cpolynomial (Mathlib) and the second is CLM + constant.
  let diag : (F₁ →L[𝕜] F₁) →L[𝕜] (Π _ : ι, F₁ →L[𝕜] F₁) :=
    ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.id 𝕜 _)
  let padBeta : (F₁ →L[𝕜] F₁) →
      (Π _ : ι, F₁ →L[𝕜] F₁) × ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂ :=
    fun p ↦ (diag p, β)
  have h_eq : (fun p : F₁ →L[𝕜] F₁ ↦
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : ι ↦ p) β) =
      (fun (q : (Π _ : ι, F₁ →L[𝕜] F₁) ×
          ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂) ↦
        q.2.compContinuousLinearMap q.1) ∘ padBeta := by
    funext q
    rfl
  rw [h_eq]
  apply CPolynomialAt.contDiffAt
  apply CPolynomialAt.comp
  · exact ContinuousMultilinearMap.cpolynomialAt_uncurry_compContinuousLinearMap
  · -- `padBeta = (diag · , const β)` as a CLM-valued affine map.
    have h_padBeta_eq : padBeta = fun p ↦
        (diag.prod (0 : (F₁ →L[𝕜] F₁) →L[𝕜]
          ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) p + (0, β) := by
      funext p
      simp [padBeta, diag]
    rw [h_padBeta_eq]
    -- A CLM plus a constant is cpolynomial.
    apply (ContinuousLinearMap.cpolynomialAt
      (diag.prod (0 : (F₁ →L[𝕜] F₁) →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ F₁) F₂)) p).add
    exact CPolynomialAt_const

end Smooth

end Comp
