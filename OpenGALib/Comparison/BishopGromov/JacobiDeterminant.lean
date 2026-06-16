import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Jacobi's / Liouville's determinant derivative formula

The Bishop–Gromov Jacobi route differentiates the determinant of the Jacobi matrix
`A(t)` (whose columns are the Jacobi fields in the parallel frame) — CH21 L148–151:

> "Remember that for `A(t)` we have `d/dt det A(t) = Σᵢ det(a₁|…|aᵢ'|…|aₙ)`"

— and combines it with `D_t J = S J` to get `∂_t det A = (tr S) · det A` (CH21
L186–188). Mathlib has the determinant as a Leibniz sum but **not** its
time-derivative; this file supplies it.

The clean special case is at the identity (`Liouville at `1``): for a matrix path
`B` with `B t = 1`, `d/dt det B = tr B'`. In the Leibniz expansion
`det = Σ_σ ε σ ∏ᵢ Bᵢ,σᵢ`, the product rule lands a derivative on one factor and
freezes the rest at `B t = 1`; a frozen factor `(1)_{σ j, j}` vanishes unless
`σ` fixes `j`, so only the identity permutation survives, leaving `Σₖ B'ₖₖ = tr B'`.
The general invertible case reduces to this via `det (A s) = det (A t)·det(A t⁻¹ A s)`.

Hypotheses are stated **entrywise** (`HasDerivAt (fun s => B s a b) (B' a b) t`),
which is exactly what the parallel-frame component reduction produces and which
sidesteps any choice of matrix norm.

## Main results

* `hasDerivAt_det_one` — `B t = 1` ⟹ `d/dt det (B s) = trace B'`.
* `hasDerivAt_det` — `A t` invertible ⟹
  `d/dt det (A s) = det (A t) · trace ((A t)⁻¹ * A')`.
-/

open Matrix Equiv Equiv.Perm Finset

namespace OpenGA.Comparison.BishopGromov

variable {m : ℕ}

/-- **Math.** **Liouville's formula at the identity.** For a path of matrices `B`
with `B t = 1` and entrywise derivative `B'` at `t`, the determinant has derivative
`d/dt det (B s) = trace B'`.

Leibniz expansion `det B = Σ_σ ε σ ∏ᵢ B (σ i) i`; the product rule differentiates
one factor and freezes the others at `B t = 1`. A frozen factor `(1)_{σ j, j}` is
`0` unless `σ` fixes `j`; a non-identity permutation moves `≥ 2` points
(`two_le_card_support_of_ne_one`), so for every `k` some frozen factor `j ≠ k`
vanishes — only `σ = 1` survives, contributing `Σₖ B'ₖₖ = trace B'`. -/
theorem hasDerivAt_det_one {B : ℝ → Matrix (Fin m) (Fin m) ℝ}
    {B' : Matrix (Fin m) (Fin m) ℝ} {t : ℝ}
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t) (hBt : B t = 1) :
    HasDerivAt (fun s => (B s).det) B'.trace t := by
  classical
  -- Rewrite `det` as the Leibniz sum.
  have hfun : (fun s => (B s).det)
      = fun s => ∑ σ : Perm (Fin m), ((sign σ : ℤ) : ℝ) * ∏ i, B s (σ i) i := by
    funext s; exact Matrix.det_apply' (B s)
  rw [hfun]
  -- Derivative of each Leibniz summand via the finite product rule.
  have hsummand : ∀ σ : Perm (Fin m),
      HasDerivAt (fun s => ((sign σ : ℤ) : ℝ) * ∏ i, B s (σ i) i)
        (((sign σ : ℤ) : ℝ)
          * ∑ k, (∏ j ∈ univ.erase k, B t (σ j) j) * B' (σ k) k) t := by
    intro σ
    have hp : HasDerivAt (fun s => ∏ i, B s (σ i) i)
        (∑ k, (∏ j ∈ univ.erase k, B t (σ j) j) • B' (σ k) k) t :=
      HasDerivAt.fun_finset_prod (fun i _ => hB (σ i) i)
    have := hp.const_mul (((sign σ : ℤ) : ℝ))
    simpa only [smul_eq_mul] using this
  have hsum := HasDerivAt.fun_sum (u := (univ : Finset (Perm (Fin m))))
    (fun σ _ => hsummand σ)
  -- Identify the derivative value with `trace B'`.
  have hval : (∑ σ : Perm (Fin m), ((sign σ : ℤ) : ℝ)
        * ∑ k, (∏ j ∈ univ.erase k, B t (σ j) j) * B' (σ k) k) = B'.trace := by
    rw [hBt]
    rw [Finset.sum_eq_single (1 : Perm (Fin m))]
    · -- the identity term equals `trace B'`
      have hone : ∀ k : Fin m,
          (∏ j ∈ univ.erase k,
            (1 : Matrix (Fin m) (Fin m) ℝ) ((1 : Perm (Fin m)) j) j) = 1 :=
        fun k => Finset.prod_eq_one fun j _ => by rw [Perm.one_apply, Matrix.one_apply_eq]
      simp only [Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Perm.one_apply, hone]
      simp [Matrix.trace, Matrix.diag]
    · -- non-identity permutations contribute `0`
      intro σ _ hσ
      have hcard : 1 < #σ.support := one_lt_card_support_of_ne_one hσ
      have hinner : (∑ k, (∏ j ∈ univ.erase k,
          (1 : Matrix (Fin m) (Fin m) ℝ) (σ j) j) * B' (σ k) k) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        obtain ⟨p, hp_supp, hpk⟩ := Finset.exists_mem_ne hcard k
        have hσp : σ p ≠ p := (Perm.mem_support).mp hp_supp
        have hzero : (1 : Matrix (Fin m) (Fin m) ℝ) (σ p) p = 0 :=
          Matrix.one_apply_ne hσp
        have hpr : (∏ j ∈ univ.erase k, (1 : Matrix (Fin m) (Fin m) ℝ) (σ j) j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hpk, Finset.mem_univ p⟩) hzero
        rw [hpr, zero_mul]
      rw [hinner, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← hval]
  exact hsum

/-- **Math.** **Jacobi's / Liouville's formula.** For a path of matrices `A` with
entrywise derivative `A'` at `t` and `A t` invertible, the determinant has
derivative `d/dt det (A s) = det (A t) · trace ((A t)⁻¹ * A')`.

Reduce to the identity: `A s = A t * ((A t)⁻¹ * A s)`, so
`det (A s) = det (A t) · det (B s)` with `B s = (A t)⁻¹ * A s`, `B t = 1`. The
entrywise derivative of `B` is `(A t)⁻¹ * A'` (constant left factor), and
`hasDerivAt_det_one` gives `d/dt det (B s) = trace ((A t)⁻¹ * A')`. -/
theorem hasDerivAt_det {A : ℝ → Matrix (Fin m) (Fin m) ℝ}
    {A' : Matrix (Fin m) (Fin m) ℝ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hinv : IsUnit (A t).det) :
    HasDerivAt (fun s => (A s).det)
      ((A t).det * ((A t)⁻¹ * A').trace) t := by
  classical
  set Ainv := (A t)⁻¹ with hAinv
  -- The reduced path `B s = (A t)⁻¹ * A s`, with `B t = 1`.
  set B : ℝ → Matrix (Fin m) (Fin m) ℝ := fun s => Ainv * A s with hBdef
  have hBt : B t = 1 := by rw [hBdef]; exact Matrix.nonsing_inv_mul (A t) hinv
  -- Entrywise derivative of `B`: `(Ainv * A')` entrywise.
  have hBentry : ∀ a b, HasDerivAt (fun s => B s a b) ((Ainv * A') a b) t := by
    intro a b
    have hentry : (fun s => B s a b)
        = fun s => ∑ c, Ainv a c * A s c b := by
      funext s; simp [hBdef, Matrix.mul_apply]
    rw [hentry]
    have hval : (Ainv * A') a b = ∑ c, Ainv a c * A' c b := by
      rw [Matrix.mul_apply]
    rw [hval]
    exact HasDerivAt.fun_sum
      (fun c _ => (hA c b).const_mul (Ainv a c))
  -- Liouville at the identity for `B`.
  have hdetB : HasDerivAt (fun s => (B s).det) (Ainv * A').trace t :=
    hasDerivAt_det_one hBentry hBt
  -- `det (A s) = det (A t) * det (B s)` since `A s = A t * B s`.
  have hAfact : (fun s => (A s).det) = fun s => (A t).det * (B s).det := by
    funext s
    rw [hBdef, ← Matrix.det_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv (A t) hinv,
      Matrix.one_mul]
  rw [hAfact, hAinv]
  exact hdetB.const_mul (A t).det

end OpenGA.Comparison.BishopGromov
