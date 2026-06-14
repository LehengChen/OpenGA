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

/-- **Math.** The model mean curvature is differentiable on the admissible window,
with derivative given by the quotient rule applied to `(n-1) s_K'/s_K` (using the
Jacobi ODE `s_K'' = -K s_K`). -/
theorem hasDerivAt_modelMeanCurvature (n : ℕ) (K : ℝ) {r : ℝ}
    (hr : r ∈ spaceFormAdmissibleRadii K) :
    HasDerivAt (modelMeanCurvature n K)
      (((n : ℝ) - 1) * (((-K * snakeFunction K r) * snakeFunction K r
          - snakeDeriv K r * snakeDeriv K r) / snakeFunction K r ^ 2)) r := by
  have hs_ne : snakeFunction K r ≠ 0 := (snakeFunction_pos hr).ne'
  have hmodel : modelMeanCurvature n K
      = fun x => ((n : ℝ) - 1) * (snakeDeriv K x / snakeFunction K x) := by
    funext x
    unfold modelMeanCurvature
    rw [(hasDerivAt_snakeFunction K x).deriv]; ring
  rw [hmodel]
  exact ((hasDerivAt_snakeDeriv K r).div (hasDerivAt_snakeFunction K r) hs_ne).const_mul _

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
  have hval : modelMeanCurvature n K r
      = ((n : ℝ) - 1) * (snakeDeriv K r / snakeFunction K r) := by
    unfold modelMeanCurvature
    rw [(hasDerivAt_snakeFunction K r).deriv]; ring
  rw [(hasDerivAt_modelMeanCurvature n K hr).deriv, hval]
  field_simp
  ring

/-- **Math.** Core of the Riccati comparison: the `s_K²`-weighted gap
`z = (m - m_K) · s_K²` is non-increasing. Its derivative equals
`-(m - m_K)² · s_K² / (n-1) ≤ 0`, computed from the product rule, the model
Riccati identity, and the Riccati sub-equation for `m`. -/
theorem hasDerivAt_riccatiGap_nonpos (n : ℕ) (hn : 2 ≤ n) (K : ℝ) (m : ℝ → ℝ)
    {x : ℝ} (hx : x ∈ spaceFormAdmissibleRadii K)
    (hmx : DifferentiableAt ℝ m x)
    (hsubx : deriv m x + m x ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * K ≤ 0) :
    deriv (fun y => (m y - modelMeanCurvature n K y) * snakeFunction K y ^ 2) x ≤ 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hs_ne : snakeFunction K x ≠ 0 := (snakeFunction_pos hx).ne'
  -- s' = m_K · s / (n-1)
  have hsd : snakeDeriv K x = modelMeanCurvature n K x * snakeFunction K x / ((n : ℝ) - 1) := by
    unfold modelMeanCurvature
    rw [(hasDerivAt_snakeFunction K x).deriv]; field_simp
  -- HasDerivAt of the gap z = (m - m_K)·s², in terms of the derivatives
  have hmm : HasDerivAt m (deriv m x) x := hmx.hasDerivAt
  have hmKK : HasDerivAt (modelMeanCurvature n K) (deriv (modelMeanCurvature n K) x) x :=
    (hasDerivAt_modelMeanCurvature n K hx).differentiableAt.hasDerivAt
  have hs2 : HasDerivAt (fun y => snakeFunction K y ^ 2)
      (2 * snakeFunction K x ^ 1 * snakeDeriv K x) x :=
    (hasDerivAt_snakeFunction K x).pow 2
  have hz : HasDerivAt (fun y => (m y - modelMeanCurvature n K y) * snakeFunction K y ^ 2)
      ((deriv m x - deriv (modelMeanCurvature n K) x) * snakeFunction K x ^ 2
        + (m x - modelMeanCurvature n K x) * (2 * snakeFunction K x ^ 1 * snakeDeriv K x)) x :=
    (hmm.sub hmKK).mul hs2
  rw [hz.deriv, hsd]
  -- model Riccati identity gives the derivative of m_K (equality)
  have hric := modelMeanCurvature_riccati n hn K hx
  have hs2nonneg : (0 : ℝ) ≤ snakeFunction K x ^ 2 := sq_nonneg _
  -- clear `/(n-1)` and bound `deriv m` via the sub-equation; the gap derivative is
  -- `-(m - m_K)^2 · s^2 / (n-1) ≤ 0`.
  have hsubx' : deriv m x * ((n : ℝ) - 1) + m x ^ 2 + ((n : ℝ) - 1) ^ 2 * K ≤ 0 := by
    have := mul_le_mul_of_nonneg_right hsubx hn1.le
    field_simp at this; nlinarith [this]
  have hric' : deriv (modelMeanCurvature n K) x * ((n : ℝ) - 1)
      + modelMeanCurvature n K x ^ 2 + ((n : ℝ) - 1) ^ 2 * K = 0 := by
    have := congrArg (· * ((n : ℝ) - 1)) hric
    field_simp at this; nlinarith [this]
  -- write the gap derivative as a single fraction over `(n-1)`
  have key : (deriv m x - deriv (modelMeanCurvature n K) x) * snakeFunction K x ^ 2
        + (m x - modelMeanCurvature n K x)
            * (2 * snakeFunction K x ^ 1
                * (modelMeanCurvature n K x * snakeFunction K x / ((n : ℝ) - 1)))
      = ((deriv m x - deriv (modelMeanCurvature n K) x) * snakeFunction K x ^ 2 * ((n : ℝ) - 1)
          + (m x - modelMeanCurvature n K x) * 2 * snakeFunction K x ^ 2
              * modelMeanCurvature n K x) / ((n : ℝ) - 1) := by
    field_simp
  rw [key, div_nonpos_iff]
  right
  refine ⟨?_, hn1.le⟩
  have hbound : deriv m x * ((n : ℝ) - 1) - deriv (modelMeanCurvature n K) x * ((n : ℝ) - 1)
      ≤ modelMeanCurvature n K x ^ 2 - m x ^ 2 := by linarith [hsubx', hric']
  nlinarith [mul_le_mul_of_nonneg_right hbound hs2nonneg,
    sq_nonneg (m x - modelMeanCurvature n K x), hs2nonneg,
    mul_nonneg hs2nonneg (sq_nonneg (m x - modelMeanCurvature n K x))]

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
  classical
  set z : ℝ → ℝ := fun y => (m y - modelMeanCurvature n K y) * snakeFunction K y ^ 2 with hz_def
  -- `z` is differentiable on the window (for continuity, and `deriv z ≤ 0`)
  have hzdiff : ∀ x ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ z x := by
    intro x hx
    exact ((hdiff x hx).sub (hasDerivAt_modelMeanCurvature n K hx).differentiableAt).mul
      ((hasDerivAt_snakeFunction K x).pow 2).differentiableAt
  -- `z` is non-increasing on the window
  have hint : interior (spaceFormAdmissibleRadii K) = spaceFormAdmissibleRadii K :=
    (isOpen_spaceFormAdmissibleRadii K).interior_eq
  have hanti : AntitoneOn z (spaceFormAdmissibleRadii K) := by
    refine antitoneOn_of_deriv_nonpos (convex_spaceFormAdmissibleRadii K)
      (fun x hx => (hzdiff x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hzdiff x (hint ▸ hx)).differentiableWithinAt) ?_
    intro x hx
    rw [hint] at hx
    exact hasDerivAt_riccatiGap_nonpos n hn K m hx (hdiff x hx) (hsub x hx)
  -- singular boundary: `z → 0` as `r → 0⁺`
  have hs0 : Filter.Tendsto (snakeFunction K) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using ((continuous_snakeFunction K).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hsd1 : Filter.Tendsto (snakeDeriv K) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using ((continuous_snakeDeriv K).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hs2lim : Filter.Tendsto (fun y => snakeFunction K y ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hs0.pow 2
  -- `m_K · s² = (n-1)·s'·s` near 0, hence → 0
  have hmKlim : Filter.Tendsto (fun y => modelMeanCurvature n K y * snakeFunction K y ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have heq : (fun y => modelMeanCurvature n K y * snakeFunction K y ^ 2)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun y => ((n : ℝ) - 1) * snakeDeriv K y * snakeFunction K y) := by
      filter_upwards [eventually_mem_spaceFormAdmissibleRadii hr] with s hs
      have hsne : snakeFunction K s ≠ 0 := (snakeFunction_pos hs.1).ne'
      unfold modelMeanCurvature
      rw [(hasDerivAt_snakeFunction K s).deriv]; field_simp
    refine Filter.Tendsto.congr' heq.symm ?_
    simpa using ((tendsto_const_nhds.mul hsd1).mul hs0)
  -- `m · s² → 0` via the asymptotic `m - (n-1)/r → 0` and `s/r → 1`
  have hmlim : Filter.Tendsto (fun y => m y * snakeFunction K y ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have ht1 : Filter.Tendsto (fun y => (m y - ((n : ℝ) - 1) / y) * snakeFunction K y ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using hasymp.mul hs2lim
    have ht2 : Filter.Tendsto (fun y => ((n : ℝ) - 1) * (snakeFunction K y * (snakeFunction K y / y)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using tendsto_const_nhds.mul (hs0.mul (tendsto_snakeFunction_div_one K))
    have heq : (fun y => m y * snakeFunction K y ^ 2)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun y => (m y - ((n : ℝ) - 1) / y) * snakeFunction K y ^ 2
          + ((n : ℝ) - 1) * (snakeFunction K y * (snakeFunction K y / y))) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hyne : y ≠ 0 := ne_of_gt hy
      field_simp; ring
    have hadd : Filter.Tendsto
        (fun y => (m y - ((n : ℝ) - 1) / y) * snakeFunction K y ^ 2
          + ((n : ℝ) - 1) * (snakeFunction K y * (snakeFunction K y / y)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by simpa using ht1.add ht2
    exact hadd.congr' heq.symm
  have hlim : Filter.Tendsto z (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := hmlim.sub hmKlim
    simpa [hz_def, sub_mul] using this
  -- antitone + boundary limit ⟹ `z r ≤ 0`
  have hzr : z r ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_mem_spaceFormAdmissibleRadii hr] with s hs
    exact hanti hs.1 hr hs.2
  -- conclude `m r ≤ m_K r` from `(m r - m_K r)·s² ≤ 0` and `s² > 0`
  have hs2pos : 0 < snakeFunction K r ^ 2 := pow_pos (snakeFunction_pos hr) 2
  simp only [hz_def] at hzr
  nlinarith [hzr, hs2pos, mul_pos hs2pos hs2pos]

end OpenGA.Comparison.BishopGromov
