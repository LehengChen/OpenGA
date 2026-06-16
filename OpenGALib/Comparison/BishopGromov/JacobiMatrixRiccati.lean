import OpenGALib.Comparison.BishopGromov.JacobiRiccatiOperator
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Jacobi matrix ODE ⟶ operator matrix Riccati

The Jacobi equation, written for the normal frame as a **matrix ODE**
`A'' + Rc A = 0` (CH21 L156–168), produces the shape operator `S = A' A⁻¹` whose
derivative satisfies the **operator matrix Riccati** `S' + S² + Rc = 0` (CH21 §
`thm: split Jacobi equation`). This file is that purely-operator-calculus step:
differentiating `S = A' · A⁻¹` once, using `A'' = -Rc A`.

It works in the normed ring `V →L[ℝ] V` (continuous linear endomorphisms of a
finite-dimensional real inner product space). The inverse `A⁻¹` is differentiated
via `hasFDerivAt_ringInverse`; the product rule for ring-valued maps assembles the
result. The output `HasDerivAt S (-(Rc t) - S t * S t) t` is **exactly** the
operator Riccati hypothesis `hric` consumed by `operatorRiccati_scalar_riccati`
(`JacobiRiccatiOperator.lean`).

*No geometry, no manifolds* — pure operator calculus.

## Main results

* `hasDerivAt_shapeOperator_of_jacobiMatrixODE` — from `A'' = -Rc A` at `t` and
  `A t` invertible, `S = A' A⁻¹` satisfies `HasDerivAt S (-(Rc t) - S t · S t) t`.
-/

open scoped InnerProductSpace

namespace OpenGA.Comparison.BishopGromov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Math.** **Jacobi matrix ODE ⟶ operator Riccati (one differentiation).** Let
`A, A', Rc : ℝ → (V →L[ℝ] V)` be operator paths with, at time `t`:
* `HasDerivAt A (A' t) t` — `A'` is the derivative of `A`;
* `HasDerivAt A' (-(Rc t) * A t) t` — the **Jacobi matrix ODE** `A'' = -Rc A`;
* `A t` invertible.

Then the shape operator `S s := A' s · A⁻¹ s` (with `A⁻¹ = Ring.inverse`) satisfies
the **operator matrix Riccati**
`HasDerivAt S (-(Rc t) - S t · S t) t`, where `S t = A' t · A⁻¹ t`.

The proof: `A⁻¹` is differentiated by `hasFDerivAt_ringInverse`
(`(A⁻¹)' = -A⁻¹ A' A⁻¹`); the ring product rule gives
`S' = A'' A⁻¹ + A' (A⁻¹)' = (-Rc A) A⁻¹ - A' A⁻¹ A' A⁻¹ = -Rc - S²`,
using `A A⁻¹ = 1`. This is exactly the `hric` input of
`operatorRiccati_scalar_riccati`. -/
theorem hasDerivAt_shapeOperator_of_jacobiMatrixODE
    (A A' Rc : ℝ → (V →L[ℝ] V)) (t : ℝ)
    (hAt : HasDerivAt A (A' t) t)
    (hA'' : HasDerivAt A' (-(Rc t) * A t) t)
    (hunit : IsUnit (A t)) :
    HasDerivAt (fun s => A' s * Ring.inverse (A s))
      (-(Rc t) - (A' t * Ring.inverse (A t)) * (A' t * Ring.inverse (A t))) t := by
  obtain ⟨u, hu⟩ := hunit
  -- `Ring.inverse (A t) = ↑u⁻¹`.
  have hAinv : Ring.inverse (A t) = (↑u⁻¹ : V →L[ℝ] V) := by rw [← hu, Ring.inverse_unit]
  -- Derivative of `Ring.inverse ∘ A` at `t`, via `hasFDerivAt_ringInverse`.
  have hinv_fderiv : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V) (↑u⁻¹) (↑u⁻¹)) (A t) := by
    rw [← hu]; exact hasFDerivAt_ringInverse u
  have hInv : HasDerivAt (fun s => Ring.inverse (A s))
      (-((↑u⁻¹ : V →L[ℝ] V) * A' t * ↑u⁻¹)) t := by
    have h := hinv_fderiv.comp_hasDerivAt t hAt
    simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply] using h
  -- Product rule: `S = A' · (Ring.inverse ∘ A)`.
  have hmul := hA''.mul hInv
  -- Cancellation `↑u * ↑u⁻¹ = 1`.
  have hcancel : (↑u : V →L[ℝ] V) * ↑u⁻¹ = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- Match the derivative values.
  convert hmul using 1
  rw [hAinv, ← hu]
  -- Goal: `-(Rc t) - (A' t * ↑u⁻¹) * (A' t * ↑u⁻¹)`
  --     = (-(Rc t) * ↑u) * ↑u⁻¹ + A' t * -(↑u⁻¹ * A' t * ↑u⁻¹)
  have hfst : (-(Rc t) * (↑u : V →L[ℝ] V)) * ↑u⁻¹ = -(Rc t) := by
    rw [mul_assoc, hcancel, mul_one]
  have hprod : (A' t * (↑u⁻¹ : V →L[ℝ] V)) * (A' t * ↑u⁻¹)
      = A' t * (↑u⁻¹ * A' t * ↑u⁻¹) := by
    simp only [mul_assoc]
  rw [hfst, sub_eq_add_neg, hprod, mul_neg]

/-- **Math.** **Jacobi matrix ODE ⟶ scalar Riccati (the leg-① spine).** Chaining
`hasDerivAt_shapeOperator_of_jacobiMatrixODE` into `operatorRiccati_scalar_riccati`:
from the normal-frame Jacobi matrix ODE `A'' = -R̃ A` at `t`, with `A t` invertible
and the shape operator `S = A' A⁻¹` symmetric with the radial unit vector `u` in
its kernel and the Ricci-trace bound `tr R̃ ≥ (n-1)κ`, the scalar mean
`a t := tr (S t)/(n-1)` satisfies the scalar Riccati `a'(t) + a(t)² + κ ≤ 0`.

This is the operator-calculus spine of the Bishop–Gromov Jacobi route: it consumes
only the matrix ODE (which the parallel-frame reduction of the Jacobi equation
supplies) and the algebraic shape-operator facts, and outputs exactly the scalar
Riccati that `riccati_le_model` compares against the model. -/
theorem scalarRiccati_of_jacobiMatrixODE
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (A A' Rc : ℝ → (V →L[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hAt : HasDerivAt A (A' t) t)
    (hA'' : HasDerivAt A' (-(Rc t) * A t) t)
    (hunit : IsUnit (A t))
    (hSsym : ((A' t * Ring.inverse (A t) : V →L[ℝ] V) : V →ₗ[ℝ] V).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (A' t * Ring.inverse (A t)) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (Rc t : V →ₗ[ℝ] V))
    (a : ℝ → ℝ)
    (ha : ∀ s, a s = LinearMap.trace ℝ V
      ((A' s * Ring.inverse (A s) : V →L[ℝ] V) : V →ₗ[ℝ] V) / ((n : ℝ) - 1)) :
    deriv a t + a t ^ 2 + κ ≤ 0 :=
  operatorRiccati_scalar_riccati hn b
    (fun s => A' s * Ring.inverse (A s)) Rc κ t hSsym u hu hSu hR
    (hasDerivAt_shapeOperator_of_jacobiMatrixODE A A' Rc t hAt hA'' hunit) a ha

/-- **Math.** **Jacobi matrix ODE ⟶ mean-curvature Riccati** (the `m = trace S`
form of the spine). Same hypotheses as `scalarRiccati_of_jacobiMatrixODE`, but the
conclusion is delivered in the mean-curvature form `m'(t) + m(t)²/(n-1) +
(n-1)κ ≤ 0` with `m t = trace (S t)` — the exact pointwise sub-equation `hsub`
consumed by the Riccati comparison engine `riccati_le_model`. -/
theorem meanCurvatureRiccati_of_jacobiMatrixODE
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (A A' Rc : ℝ → (V →L[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hAt : HasDerivAt A (A' t) t)
    (hA'' : HasDerivAt A' (-(Rc t) * A t) t)
    (hunit : IsUnit (A t))
    (hSsym : ((A' t * Ring.inverse (A t) : V →L[ℝ] V) : V →ₗ[ℝ] V).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (A' t * Ring.inverse (A t)) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (Rc t : V →ₗ[ℝ] V))
    (m : ℝ → ℝ)
    (hm : ∀ s, m s = LinearMap.trace ℝ V
      ((A' s * Ring.inverse (A s) : V →L[ℝ] V) : V →ₗ[ℝ] V)) :
    deriv m t + m t ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * κ ≤ 0 :=
  operatorRiccati_mean_riccati hn b
    (fun s => A' s * Ring.inverse (A s)) Rc κ t hSsym u hu hSu hR
    (hasDerivAt_shapeOperator_of_jacobiMatrixODE A A' Rc t hAt hA'' hunit) m hm

end OpenGA.Comparison.BishopGromov
