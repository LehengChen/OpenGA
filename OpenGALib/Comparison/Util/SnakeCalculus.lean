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

end OpenGA.Comparison.BishopGromov
