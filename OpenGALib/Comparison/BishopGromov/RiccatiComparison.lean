import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Comparison.Util.SnakeCalculus

/-!
# Riccati comparison

Layer 3a-ODE of the Bishop–Gromov chain, and OpenGALib's own contribution (no
upstream counterpart). The mean curvature `m(r)` of the geodesic spheres around a
point satisfies the Riccati differential inequality
`m'(r) + m(r)^2 / (n-1) + Ric(∂_r, ∂_r) ≤ 0`, and under `Ric ≥ (n-1) K` this is
dominated by the model equality solution
`m_K(r) = (n-1) · s_K'(r) / s_K(r)` (`s_K = snakeFunction K`). Comparison of the
two then forces `m ≤ m_K`, which is exactly the Laplacian comparison
`Δ_g r ≤ m_K` (`LaplacianComparison`).

This file isolates the purely real-analytic core: the model mean-curvature
function, its Riccati identity, and the sub-solution comparison. The geometric
identification `m = Δ_g r` and the curvature input live in `LaplacianComparison`.

Ground truth: Petersen Ch.9 Lemma 27.1; do Carmo Ch.10 §1.
-/

open scoped Real
open OpenGA.Comparison.BishopGromov

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** The model mean-curvature function of a space form of curvature `K` in
dimension `n`: `m_K(r) = (n-1) · s_K'(r) / s_K(r)`, where `s_K = snakeFunction K`
is the Jacobi function. It is the equality solution of the Riccati equation that
bounds the mean curvature of geodesic spheres. -/
noncomputable def modelMeanCurvature (n : ℕ) (K r : ℝ) : ℝ :=
  ((n : ℝ) - 1) * deriv (snakeFunction K) r / snakeFunction K r

/-- **Math.** Riccati identity for the model: the model mean curvature solves
`m_K'(r) + m_K(r)^2 / (n-1) + (n-1) K = 0` on the admissible radius window, the
equality case of the Riccati inequality satisfied by a manifold mean curvature
with `Ric ≥ (n-1) K`. -/
theorem modelMeanCurvature_riccati (n : ℕ) (hn : 2 ≤ n) (K : ℝ) {r : ℝ}
    (hr : r ∈ spaceFormAdmissibleRadii K) :
    deriv (modelMeanCurvature n K) r
        + modelMeanCurvature n K r ^ 2 / ((n : ℝ) - 1)
        + ((n : ℝ) - 1) * K = 0 := by
  have hs_ne : snakeFunction K r ≠ 0 := (snakeFunction_pos hr).ne'
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- `modelMeanCurvature` written via the proven derivative `snakeDeriv`
  have hmodel : modelMeanCurvature n K
      = fun x => ((n : ℝ) - 1) * (snakeDeriv K x / snakeFunction K x) := by
    funext x
    unfold modelMeanCurvature
    rw [(hasDerivAt_snakeFunction K x).deriv]; ring
  -- quotient rule, using the Jacobi ODE `s'' = -K·s` baked into `hasDerivAt_snakeDeriv`
  have hm : HasDerivAt (modelMeanCurvature n K)
      (((n : ℝ) - 1) * (((-K * snakeFunction K r) * snakeFunction K r
          - snakeDeriv K r * snakeDeriv K r) / snakeFunction K r ^ 2)) r := by
    rw [hmodel]
    exact ((hasDerivAt_snakeDeriv K r).div (hasDerivAt_snakeFunction K r) hs_ne).const_mul _
  rw [hm.deriv, show modelMeanCurvature n K r
      = ((n : ℝ) - 1) * (snakeDeriv K r / snakeFunction K r) by rw [hmodel]]
  field_simp
  ring

/-- **Math.** Riccati comparison. If a differentiable real function `m` on the
admissible window satisfies the Riccati sub-equation
`m'(r) + m(r)^2/(n-1) + (n-1) K ≤ 0` and is asymptotic to the model singularity
`(n-1)/r` as `r → 0⁺`, then it is dominated by the model mean curvature:
`m(r) ≤ m_K(r)`. This is the ODE engine behind the Laplacian comparison.

PRE-PAPER. Proof plan (concrete `s_K²` integrating factor, avoiding an abstract
`exp ∫` — Mathlib's Gronwall is constant-coefficient only): with `a := m/(n-1)`,
`ā := m_K/(n-1) = s_K'/s_K`, set `w := a - ā` and `z := w · s_K²`. From the
sub-equation, `w' ≤ -(a + ā) w`, hence
`z' = s_K²(w' + 2 ā w) ≤ s_K²(-w²) ≤ 0`, so `z` is antitone; the asymptotic gives
`z(0⁺) = 0` (both `w → 0` and `s_K² → 0`); therefore `z ≤ 0`, and `s_K² > 0`
(`snakeFunction_pos`) gives `w ≤ 0`, i.e. `m ≤ m_K`. Needs: differentiability of
`m` (hypothesis below), the product/quotient `HasDerivAt` for `z`, the singular
limit, and `antitoneOn_of_deriv_nonpos`. -/
theorem riccati_le_model (n : ℕ) (hn : 2 ≤ n) (K : ℝ) (m : ℝ → ℝ)
    (hdiff : ∀ r ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ m r)
    (hsub : ∀ r ∈ spaceFormAdmissibleRadii K,
      deriv m r + m r ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * K ≤ 0)
    (hasymp : Filter.Tendsto (fun r => m r - ((n : ℝ) - 1) / r) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0))
    {r : ℝ} (hr : r ∈ spaceFormAdmissibleRadii K) :
    m r ≤ modelMeanCurvature n K r := by
  sorry

end OpenGA.Comparison.BishopGromov
