import OpenGALib.Algebraic.BilinearForm.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum.Ineq

/-!
# Concrete instance: rational vectors

A fully `#eval`-able `BilinearForm` on `Fin n → ℚ`. `#eval inner`
produces a `Rat`; concrete equalities like
`inner ![1,2,3] ![4,5,6] = 32` are closed by kernel-checked
`simp`/`norm_num` proofs. The same operations on the abstract
`Form ℚ V` API give the same numerical results, demonstrating
algebraic-core ↔ concrete-instance consistency.

Specialising to `𝕜 = ℝ` + smoothness reproduces the Riemannian module's
`metricInner` (with the usual `noncomputable` cascade).

**Ground truth**: $\langle v, w \rangle = \sum_i v_i w_i$ on
$\mathbb{Q}^n$.
-/

namespace RatVector

open BilinearForm

/-- The standard symmetric bilinear form on $\mathrm{Fin}\,n \to \mathbb{Q}$:
$B(v, w) = \sum_i v_i w_i$. As a `LinearMap.BilinForm`-style
`V →ₗ[ℚ] V →ₗ[ℚ] ℚ`. -/
def stdForm (n : ℕ) : Form ℚ (Fin n → ℚ) where
  toFun v :=
    { toFun := fun w => ∑ i, v i * w i
      map_add' := fun w₁ w₂ => by
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun c w => by
        simp [Finset.mul_sum, mul_left_comm] }
  map_add' v₁ v₂ := by
    ext w
    simp [Finset.sum_add_distrib, add_mul]
  map_smul' c v := by
    ext w
    simp [Finset.mul_sum, mul_assoc]

/-- Standard inner product specialised to ℚ: `inner v w = ∑ i, v i * w i`. -/
@[simp]
theorem stdForm_apply (n : ℕ) (v w : Fin n → ℚ) :
    stdForm n v w = ∑ i, v i * w i :=
  rfl

/-- `inner` via the standard form on $\mathbb{Q}^n$ also reduces to the
sum: `inner (stdForm n) v w = ∑ i, v i * w i`. -/
theorem inner_stdForm (n : ℕ) (v w : Fin n → ℚ) :
    inner (stdForm n) v w = ∑ i, v i * w i :=
  rfl

end RatVector

/-! ## `#eval` demonstrations — math runs

Below `#eval` commands genuinely execute at elaboration time and
produce rational numbers. Sample output (lhs is what `#eval` prints):

```
inner (stdForm 3) ![1, 2, 3] ![4, 5, 6]   =  32
inner (stdForm 2) ![3, 4] ![3, 4]         =  25
inner (stdForm 3) ![1, 0, 0] ![0, 1, 0]   =  0
inner (stdForm 3) ![1, 0, 0] ![1, 0, 0]   =  1
```
-/

open BilinearForm RatVector

#eval inner (stdForm 3) ![1, 2, 3] ![4, 5, 6]    -- 32

#eval inner (stdForm 2) ![3, 4] ![3, 4]          -- 25

#eval inner (stdForm 3) ![1, 0, 0] ![0, 1, 0]    -- 0

#eval inner (stdForm 3) ![1, 0, 0] ![1, 0, 0]    -- 1

/-! ## Kernel-checked equalities — proof by computation

The same equations that `#eval` produces are closed as theorems by
unfolding `inner` to the concrete sum (`stdForm_apply`,
`Fin.sum_univ_two`/`Fin.sum_univ_three`) and discharging the rational
arithmetic with `norm_num`. Each proof is checked by the kernel — no
native code or compiler trust. -/

example : inner (stdForm 3) ![1, 2, 3] ![4, 5, 6] = 32 := by
  simp [stdForm_apply, Fin.sum_univ_three]; norm_num

example : inner (stdForm 2) ![3, 4] ![3, 4] = 25 := by
  simp [stdForm_apply, Fin.sum_univ_two]; norm_num

example : inner (stdForm 3) ![1, 0, 0] ![0, 1, 0] = 0 := by
  simp [stdForm_apply, Fin.sum_univ_three]

example : inner (stdForm 3) ![1, 0, 0] ![1, 0, 0] = 1 := by
  simp [stdForm_apply, Fin.sum_univ_three]

/-- Cauchy–Schwarz on a concrete pair, kernel-checked. -/
example :
    let v : Fin 3 → ℚ := ![1, 2, 3]
    let w : Fin 3 → ℚ := ![4, 5, 6]
    (inner (stdForm 3) v w) ^ 2
      ≤ inner (stdForm 3) v v * inner (stdForm 3) w w := by
  norm_num [inner_def, stdForm_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
