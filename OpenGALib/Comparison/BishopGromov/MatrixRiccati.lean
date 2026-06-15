import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import OpenGALib.Comparison.Util.RefinedCauchySchwarz

/-!
# Matrix Riccati ⟶ scalar Riccati (trace reduction)

Abstract linear-algebra + scalar-ODE brick of a Jacobi-field Bishop–Gromov
proof. *No geometry, no manifolds.*

A path of symmetric operators `S t` on a finite-dimensional real inner product
space `V` (of dimension `n`), carrying a fixed unit vector `u` in the kernel of
every `S t` (the radial direction), and satisfying the **matrix Riccati**
inequality through its trace,

  `(trace S)' + trace (S ∘ S) + trace R = 0`,  `trace (R t) ≥ (n-1) κ`,

has its scalar mean `a t := trace (S t) / (n-1)` satisfying the **scalar
Riccati** inequality

  `a'(t) + a(t)² + κ ≤ 0`.

## Math

Trace the matrix Riccati: `(trace S)' + trace(S²) + trace R = 0`. For symmetric
`S`, `trace(S²) = ‖S‖²_HS = ∑ᵢⱼ ⟪S bᵢ, bⱼ⟫²` (Hilbert–Schmidt;
`trace_sq_eq_frobenius` below). The refined Cauchy–Schwarz with the unit kernel
vector `u` (`OpenGA.Comparison.Util.refined_cauchy_schwarz`) gives
`(trace S)² ≤ (n-1)·‖S‖²_HS`, i.e. `trace(S²) ≥ (trace S)²/(n-1)`. With
`trace R ≥ (n-1)κ`:

  `(trace S)' = -trace(S²) - trace R ≤ -(trace S)²/(n-1) - (n-1)κ`.

With `a = trace S/(n-1)` (so `trace S = (n-1)a`): `a' ≤ -a² - κ`, the claim.

## Encoding choice

The covariant-derivative hypothesis is taken in **traced scalar form**: rather
than threading an operator-valued `HasDerivAt` through the (finite-dimensional)
`V →L[ℝ] V` normed structure and pushing the continuous-linear `trace` through
it, we take as hypothesis a scalar `HasDerivAt` for the trace function
`h t = trace (S t)` whose derivative equals the traced Riccati right-hand side
`-(trace (S t ∘ S t)) - trace (R t)`. This is the honest fallback flagged in the
design notes: it keeps the operators `S, R : ℝ → (V →ₗ[ℝ] V)` first-class and
phrases the matrix Riccati *exactly* (via `LinearMap.trace`), while avoiding the
operator-valued-derivative plumbing. The Hilbert–Schmidt bridge
`trace (S ∘ S) = ∑ᵢⱼ ⟪S bᵢ, bⱼ⟫²` is proved here (`trace_sq_eq_frobenius`), so
the hypothesis is stated against the genuine operator trace.

The output is delivered in BOTH the `a`-form (`a' + a² + κ ≤ 0`) and the
mean-curvature `m = trace S`-form that `riccati_le_model`
(`Comparison/BishopGromov/RiccatiComparison.lean`) consumes:
`m'(r) + m(r)²/(n-1) + (n-1)κ ≤ 0`. The two differ exactly by the positive
factor `(n-1)`.
-/

open scoped InnerProductSpace BigOperators

namespace OpenGA.Comparison.BishopGromov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

open OpenGA.Comparison.Util

omit [FiniteDimensional ℝ V] in
/-- **Hilbert–Schmidt bridge.** For a symmetric operator `S` and an orthonormal
basis `b`, `trace (S ∘ S) = ∑ᵢ ∑ⱼ ⟪S bᵢ, bⱼ⟫²`, the squared Hilbert–Schmidt /
Frobenius norm. (Insert the resolution of identity `∑ⱼ ⟪·, bⱼ⟫ bⱼ` and use
symmetry `⟪bᵢ, S(S bᵢ)⟫ = ⟪S bᵢ, S bᵢ⟫`.) -/
theorem trace_sq_eq_frobenius {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)
    (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric) :
    LinearMap.trace ℝ V (S ∘ₗ S) = ∑ i, ∑ j, (inner ℝ (S (b i)) (b j)) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner (S ∘ₗ S) b]
  -- termwise: ⟪bᵢ, (S∘S) bᵢ⟫ = ∑ⱼ ⟪S bᵢ, bⱼ⟫²
  apply Finset.sum_congr rfl
  intro i _
  -- ⟪bᵢ, S (S bᵢ)⟫ = ⟪S bᵢ, S bᵢ⟫ = ‖S bᵢ‖² = ∑ⱼ ⟪S bᵢ, bⱼ⟫²  (Parseval)
  have hsym : (inner ℝ (b i) ((S ∘ₗ S) (b i)) : ℝ) = inner ℝ (S (b i)) (S (b i)) := by
    simp only [LinearMap.comp_apply]
    rw [hS (b i) (S (b i))]
  rw [hsym, real_inner_self_eq_norm_sq]
  -- Parseval over the orthonormal basis `b`
  have hpar := b.sum_sq_norm_inner_left (S (b i))
  rw [← hpar]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs]

/-- **Trace ⟶ scalar Riccati (mean-curvature `m = trace S` form).**

Let `S, R : ℝ → (V →ₗ[ℝ] V)` be operator paths on an `n`-dimensional real inner
product space, with `S t` symmetric and a fixed unit vector `u` in `ker (S t)`
for all `t`. Suppose the trace function `h t = trace (S t)` is differentiable at
`t` with the traced matrix-Riccati derivative
`h'(t) = -trace (S t ∘ S t) - trace (R t)`, and that `trace (R t) ≥ (n-1) κ`.

Then the mean curvature `m = trace S` satisfies the scalar Riccati sub-equation
`m'(t) + m(t)²/(n-1) + (n-1) κ ≤ 0`.

This is exactly the input shape consumed by `riccati_le_model`. -/
theorem matrixRiccati_trace_riccati
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (S R : ℝ → (V →ₗ[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hSsym : (S t).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (S t) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (R t))
    (h : ℝ → ℝ) (hh : ∀ s, h s = LinearMap.trace ℝ V (S s))
    (hderiv : HasDerivAt h
      (-(LinearMap.trace ℝ V (S t ∘ₗ S t)) - LinearMap.trace ℝ V (R t)) t) :
    deriv h t + h t ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * κ ≤ 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- trace S in basis components: trace S = ∑ ⟪S bᵢ, bᵢ⟫
  have htrace : LinearMap.trace ℝ V (S t) = ∑ i, (inner ℝ ((S t) (b i)) (b i) : ℝ) := by
    rw [LinearMap.trace_eq_sum_inner (S t) b]
    apply Finset.sum_congr rfl
    intro i _
    exact (real_inner_comm (b i) ((S t) (b i))).symm
  -- trace (S∘S) = HS double-sum
  have hHS : LinearMap.trace ℝ V (S t ∘ₗ S t)
      = ∑ i, ∑ j, (inner ℝ ((S t) (b i)) (b j)) ^ 2 :=
    trace_sq_eq_frobenius b (S t) hSsym
  -- refined Cauchy–Schwarz: (trace S)² ≤ (n-1)·HS
  have hrcs := refined_cauchy_schwarz b (S t) hSsym u hu hSu
  rw [← htrace, ← hHS] at hrcs
  -- hence trace(S∘S) ≥ (trace S)²/(n-1)
  have hHSlb : (LinearMap.trace ℝ V (S t)) ^ 2 / ((n : ℝ) - 1)
      ≤ LinearMap.trace ℝ V (S t ∘ₗ S t) := by
    rw [div_le_iff₀ hn1, mul_comm]
    exact hrcs
  -- value of deriv h t
  have hd : deriv h t = -(LinearMap.trace ℝ V (S t ∘ₗ S t)) - LinearMap.trace ℝ V (R t) :=
    hderiv.deriv
  -- assemble
  rw [hd, hh t]
  -- goal: (-tr(S∘S) - tr R) + (tr S)²/(n-1) + (n-1)κ ≤ 0
  have hRlb : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (R t) := hR
  -- from hHSlb: (tr S)²/(n-1) - tr(S∘S) ≤ 0; from hRlb: (n-1)κ - tr R ≤ 0
  linarith [hHSlb, hRlb]

/-- **Trace ⟶ scalar Riccati (normalized mean `a = trace S/(n-1)` form).**

Same hypotheses as `matrixRiccati_trace_riccati`, restated for the normalized
scalar mean `a t := trace (S t) / (n-1)`: it satisfies `a'(t) + a(t)² + κ ≤ 0`.
Equivalent to the `m`-form by the positive factor `(n-1)`. -/
theorem matrixRiccati_trace_scalar_riccati
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (S R : ℝ → (V →ₗ[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hSsym : (S t).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (S t) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (R t))
    (h : ℝ → ℝ) (hh : ∀ s, h s = LinearMap.trace ℝ V (S s))
    (hderiv : HasDerivAt h
      (-(LinearMap.trace ℝ V (S t ∘ₗ S t)) - LinearMap.trace ℝ V (R t)) t)
    (a : ℝ → ℝ) (ha : ∀ s, a s = h s / ((n : ℝ) - 1)) :
    deriv a t + a t ^ 2 + κ ≤ 0 := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the m-form
  have hm := matrixRiccati_trace_riccati hn b S R κ t hSsym u hu hSu hR h hh hderiv
  -- a = h / (n-1), so deriv a t = deriv h t / (n-1)
  have hafun : a = fun s => h s / ((n : ℝ) - 1) := funext ha
  have hda : deriv a t = deriv h t / ((n : ℝ) - 1) := by
    rw [hafun, deriv_div_const]
  rw [hda, ha t]
  -- The target equals the m-form `hm` divided by the positive factor `(n-1)`.
  -- Show `target = hm-expression / (n-1)` and conclude by `div_nonpos`.
  have hn1' : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hn1
  have heq : deriv h t / ((n : ℝ) - 1) + (h t / ((n : ℝ) - 1)) ^ 2 + κ
      = (deriv h t + h t ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * κ) / ((n : ℝ) - 1) := by
    field_simp
  rw [heq]
  exact div_nonpos_of_nonpos_of_nonneg hm hn1.le

end OpenGA.Comparison.BishopGromov
