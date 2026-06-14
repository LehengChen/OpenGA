import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import OpenGALib.Comparison.Util.SpaceForm

/-!
# Calculus of the snake function

Derivative facts for `snakeFunction K` underpinning the model Riccati identity
(`RiccatiComparison`). The snake function is the solution of the Jacobi /
space-form ODE `s'' = -K · s` with `s(0) = 0`, `s'(0) = 1`; this file records its
first derivative and that Jacobi ODE, the two facts the cotangent Riccati
`(s'/s)' + (s'/s)^2 + K = 0` reduces to.

Reference: comparison-geometry notes (CH21, Jacobi/Riccati equations);
Petersen Ch.9; do Carmo Ch.10 §1.
-/

open Real
open scoped Real

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** First derivative of the snake function: `s_K'(r)` is
`cos(√K·r)` (K>0), `1` (K=0), `cosh(√(-K)·r)` (K<0). -/
noncomputable def snakeDeriv (K r : ℝ) : ℝ :=
  if 0 < K then Real.cos (Real.sqrt K * r)
  else if K < 0 then Real.cosh (Real.sqrt (-K) * r)
  else 1

/-- **Math.** `snakeDeriv` is the derivative of `snakeFunction`. -/
theorem hasDerivAt_snakeFunction (K r : ℝ) :
    HasDerivAt (snakeFunction K) (snakeDeriv K r) r := by
  unfold snakeFunction snakeDeriv
  split_ifs with hK hK'
  · -- K > 0 : s = sin(√K r)/√K, s' = cos(√K r)·√K / √K = cos(√K r)
    have hsqrt : Real.sqrt K ≠ 0 := by positivity
    have h : HasDerivAt (fun r => Real.sin (Real.sqrt K * r))
        (Real.cos (Real.sqrt K * r) * Real.sqrt K) r := by
      simpa using (Real.hasDerivAt_sin (Real.sqrt K * r)).comp r
        ((hasDerivAt_id r).const_mul (Real.sqrt K))
    have := h.div_const (Real.sqrt K)
    rwa [mul_div_assoc, div_self hsqrt, mul_one] at this
  · -- K < 0 : s = sinh(√(-K) r)/√(-K), s' = cosh(√(-K) r)
    have hKpos : 0 < -K := by linarith
    have hsqrt : Real.sqrt (-K) ≠ 0 := by positivity
    have h : HasDerivAt (fun r => Real.sinh (Real.sqrt (-K) * r))
        (Real.cosh (Real.sqrt (-K) * r) * Real.sqrt (-K)) r := by
      simpa using (Real.hasDerivAt_sinh (Real.sqrt (-K) * r)).comp r
        ((hasDerivAt_id r).const_mul (Real.sqrt (-K)))
    have := h.div_const (Real.sqrt (-K))
    rwa [mul_div_assoc, div_self hsqrt, mul_one] at this
  · -- K = 0 : s = r, s' = 1
    simpa using hasDerivAt_id r

/-- **Math.** Jacobi / space-form ODE: `s_K'' = -K · s_K`. The snake function is
the solution of the model Jacobi equation with `s(0) = 0`, `s'(0) = 1`. -/
theorem hasDerivAt_snakeDeriv (K r : ℝ) :
    HasDerivAt (snakeDeriv K) (-K * snakeFunction K r) r := by
  unfold snakeDeriv snakeFunction
  split_ifs with hK hK'
  · -- K > 0 : (cos(√K r))' = -√K sin(√K r) = -K · sin(√K r)/√K
    have hsqrt : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK.le
    have hs : Real.sqrt K ≠ 0 := by positivity
    have h : HasDerivAt (fun r => Real.cos (Real.sqrt K * r))
        (-Real.sin (Real.sqrt K * r) * Real.sqrt K) r := by
      simpa using (Real.hasDerivAt_cos (Real.sqrt K * r)).comp r
        ((hasDerivAt_id r).const_mul (Real.sqrt K))
    have heq : -K * (Real.sin (Real.sqrt K * r) / Real.sqrt K)
        = -Real.sin (Real.sqrt K * r) * Real.sqrt K := by
      nth_rewrite 1 [← hsqrt]; field_simp
    rw [heq]; exact h
  · -- K < 0 : (cosh(√(-K) r))' = √(-K) sinh(√(-K) r) = -K · sinh(√(-K) r)/√(-K)
    have hKpos : 0 < -K := by linarith
    have hsqrt : Real.sqrt (-K) * Real.sqrt (-K) = -K := Real.mul_self_sqrt hKpos.le
    have hs : Real.sqrt (-K) ≠ 0 := by positivity
    have h : HasDerivAt (fun r => Real.cosh (Real.sqrt (-K) * r))
        (Real.sinh (Real.sqrt (-K) * r) * Real.sqrt (-K)) r := by
      simpa using (Real.hasDerivAt_cosh (Real.sqrt (-K) * r)).comp r
        ((hasDerivAt_id r).const_mul (Real.sqrt (-K)))
    have heq : -K * (Real.sinh (Real.sqrt (-K) * r) / Real.sqrt (-K))
        = Real.sinh (Real.sqrt (-K) * r) * Real.sqrt (-K) := by
      have : -K = Real.sqrt (-K) * Real.sqrt (-K) := hsqrt.symm
      nth_rewrite 1 [this]; field_simp
    rw [heq]; exact h
  · -- K = 0 : (1)' = 0 = -0 · r
    have hK0 : K = 0 := le_antisymm (not_lt.mp hK) (not_lt.mp hK')
    rw [hK0]; simp only [neg_zero, zero_mul]; exact hasDerivAt_const r (1 : ℝ)

/-- **Math.** `s_K(0) = 0`. -/
@[simp] theorem snakeFunction_zero (K : ℝ) : snakeFunction K 0 = 0 := by
  unfold snakeFunction; split_ifs <;> simp

/-- **Math.** `s_K'(0) = 1`. -/
@[simp] theorem snakeDeriv_zero (K : ℝ) : snakeDeriv K 0 = 1 := by
  unfold snakeDeriv; split_ifs <;> simp

/-- **Math.** The snake function is continuous. -/
theorem continuous_snakeFunction (K : ℝ) : Continuous (snakeFunction K) := by
  unfold snakeFunction
  split_ifs
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const _
  · exact (Real.continuous_sinh.comp (continuous_const.mul continuous_id)).div_const _
  · exact continuous_id

/-- **Math.** The snake derivative is continuous. -/
theorem continuous_snakeDeriv (K : ℝ) : Continuous (snakeDeriv K) := by
  unfold snakeDeriv
  split_ifs
  · exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
  · exact Real.continuous_cosh.comp (continuous_const.mul continuous_id)
  · exact continuous_const

/-- **Math.** Sinc-type asymptotic: `s_K(r)/r → 1` as `r → 0⁺`, since `s_K(0)=0`
and `s_K'(0)=1`. -/
theorem tendsto_snakeFunction_div_one (K : ℝ) :
    Filter.Tendsto (fun r => snakeFunction K r / r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h := hasDerivAt_snakeFunction K 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  rw [snakeDeriv_zero] at h
  have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {0}ᶜ :=
    nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)
  refine (h.mono_left hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [slope_def_field, snakeFunction_zero]

/-- **Math.** The snake function is strictly positive on the admissible radius
window `𝒟_K` (where it governs the model ball volume). -/
theorem snakeFunction_pos {K r : ℝ} (hr : r ∈ spaceFormAdmissibleRadii K) :
    0 < snakeFunction K r := by
  unfold spaceFormAdmissibleRadii at hr
  unfold snakeFunction
  split_ifs with hK hK'
  · -- K > 0 : sin(√K r)/√K with √K r ∈ (0, π)
    rw [if_pos hK] at hr
    obtain ⟨hr0, hrπ⟩ := hr
    have hsqrtK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
    have h1 : 0 < Real.sqrt K * r := mul_pos hsqrtK hr0
    have h2 : Real.sqrt K * r < Real.pi := by
      rw [lt_div_iff₀ hsqrtK] at hrπ; linarith [hrπ]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi h1 h2) hsqrtK
  · -- K < 0 : sinh(√(-K) r)/√(-K), r > 0
    rw [if_neg hK] at hr
    have hr0 : 0 < r := hr
    have hKpos : 0 < -K := by linarith
    have hsqrt : 0 < Real.sqrt (-K) := Real.sqrt_pos.mpr hKpos
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hsqrt hr0)) hsqrt
  · -- K = 0 : r, r > 0
    rw [if_neg hK] at hr
    exact hr

/-- **Math.** The admissible radius window is convex. -/
theorem convex_spaceFormAdmissibleRadii (K : ℝ) :
    Convex ℝ (spaceFormAdmissibleRadii K) := by
  unfold spaceFormAdmissibleRadii; split_ifs
  · exact convex_Ioo _ _
  · exact convex_Ioi _

/-- **Math.** The admissible radius window is open. -/
theorem isOpen_spaceFormAdmissibleRadii (K : ℝ) :
    IsOpen (spaceFormAdmissibleRadii K) := by
  unfold spaceFormAdmissibleRadii; split_ifs
  · exact isOpen_Ioo
  · exact isOpen_Ioi

/-- **Math.** Small admissible radii: for every `r` in the window, all small
positive `s` are admissible and `≤ r`. -/
theorem eventually_mem_spaceFormAdmissibleRadii {K r : ℝ}
    (hr : r ∈ spaceFormAdmissibleRadii K) :
    ∀ᶠ s in nhdsWithin (0 : ℝ) (Set.Ioi 0), s ∈ spaceFormAdmissibleRadii K ∧ s ≤ r := by
  have hr0 : (0 : ℝ) < r := by
    unfold spaceFormAdmissibleRadii at hr; split_ifs at hr with hK
    · exact hr.1
    · exact hr
  have hw : spaceFormAdmissibleRadii K ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
    unfold spaceFormAdmissibleRadii; split_ifs with hK
    · have hc : (0 : ℝ) < Real.pi / Real.sqrt K := by positivity
      have : Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt K) = Set.Ioi 0 ∩ Set.Iio (Real.pi / Real.sqrt K) := by
        ext x; simp [Set.mem_Ioo, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio]
      rw [this]
      exact Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hc))
    · exact self_mem_nhdsWithin
  have hlt : Set.Iio r ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds hr0)
  filter_upwards [hw, hlt] with s hsw hslt
  exact ⟨hsw, le_of_lt hslt⟩

end OpenGA.Comparison.BishopGromov
