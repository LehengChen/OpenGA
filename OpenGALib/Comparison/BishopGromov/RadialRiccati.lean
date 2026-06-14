import OpenGALib.Riemannian.Operators.Bochner
import OpenGALib.Comparison.BishopGromov.RiccatiComparison
import OpenGALib.Comparison.Util.RefinedCauchySchwarz

/-!
# Radial Riccati sub-equation from the Bochner formula

The analytic heart of the Laplacian comparison theorem, isolated from the
geometry of geodesics. For a function `f` whose gradient is a *unit* field
(`|∇f|² ≡ 1`, the eikonal equation satisfied by a distance function on its
smooth locus) on a manifold with `Ric ≥ (n-1) K g`, the Laplacian `Δ_g f`
satisfies the scalar Riccati sub-equation

  `∇f(Δf) + (Δf)² / (n-1) + (n-1) K ≤ 0`.

This is the Bochner–Weitzenböck identity
`½ Δ|∇f|² = |Hess f|² + ⟨∇f, ∇(Δf)⟩ + Ric(∇f, ∇f)`
specialised to `|∇f|² ≡ 1` (so the left side vanishes), combined with two
sharpenings of the curvature/Hessian terms:

* `Ric(∇f, ∇f) ≥ (n-1) K |∇f|² = (n-1) K`  — the Ricci lower bound;
* `|Hess f|² ≥ (Δf)² / (n-1)`  — Cauchy–Schwarz, sharpened from the naive
  `/n` to `/(n-1)` because the eikonal equation forces `∇f` into the kernel of
  `Hess f`, so the Hessian is effectively supported on the `(n-1)`-dimensional
  orthogonal complement.

Feeding `m := Δ_g f` (the radial Laplacian) into `riccati_le_model` then yields
`Δ_g f ≤ m_K`, the Laplacian comparison, once the geometric inputs (eikonal
equation, radial-derivative identification, base-point asymptotic) are supplied
by the exponential-map layer.

Reference: comparison-geometry notes (CH21, trace of the shape operator);
Petersen Ch.9 Lemma 27.2; do Carmo Ch.10 §1.
-/

open scoped ContDiff Manifold Bundle Riemannian InnerProductSpace Topology
open Bundle Riemannian Riemannian.Operators

namespace OpenGA.Comparison.BishopGromov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [IsLocallyConstantChartedSpace H M]
  [hm : HasMetric I M]

/-- **Math.** Eikonal equation kills the radial Hessian direction: if the
gradient-norm `|∇f|²_g` is critical at `x` (`d(|∇f|²) x = 0`, automatic where
`|∇f|² ≡ 1`), then `∇f` lies in the kernel of `Hess f`:
`Hess f (x) (v, ∇f) = 0` for every `v`. -/
theorem hessianBilin_grad_apply_eq_zero
    (g : RiemannianMetric I M) (f : M → ℝ) (x : M) (v : TangentSpace I x)
    (h_grad : TangentSmoothAt (manifoldGradient (I := I) g f) x)
    (hcrit : mfderiv I 𝓘(ℝ, ℝ)
      (fun y => g.metricInner y (manifoldGradient (I := I) g f y)
                                (manifoldGradient (I := I) g f y)) x = 0) :
    hessianBilin (I := I) g f x v (manifoldGradient (I := I) g f x) = 0 := by
  have h := mfderiv_gradientNormSq_apply g f x v h_grad
  rw [hcrit, ContinuousLinearMap.zero_apply] at h
  show g.metricInner x (covDerivAt g (manifoldGradient (I := I) g f) x v)
        (manifoldGradient (I := I) g f x) = 0
  have h' : (0 : ℝ) = 2 * g.metricInner x
      (covDerivAt g (manifoldGradient (I := I) g f) x v)
      (manifoldGradient (I := I) g f x) := h
  linear_combination (-1 / 2 : ℝ) * h'

/-- **Math.** `(n-1)`-sharpened Cauchy–Schwarz for the Hessian on the eikonal
locus: with `Hess f` symmetric at `x`, the gradient `g`-unit, and `∇f` in the
kernel of `Hess f`, the trace controls the Frobenius norm with the sharp
`(n-1)` constant: `(Δf)² ≤ (n-1) · |Hess f|²_F`. The kernel direction `∇f`
removes one dimension from the naive `n`-Cauchy–Schwarz. -/
theorem trace_sq_le_dim_sub_one_mul_frobeniusSq
    (g : RiemannianMetric I M) (hg : g = hm.metric) (f : M → ℝ) (x : M)
    (hsym : ∀ v w : TangentSpace I x,
      hessianBilin (I := I) g f x v w = hessianBilin (I := I) g f x w v)
    (hunit : g.metricInner x (manifoldGradient (I := I) g f x)
              (manifoldGradient (I := I) g f x) = 1)
    (hker : ∀ v : TangentSpace I x,
      hessianBilin (I := I) g f x v (manifoldGradient (I := I) g f x) = 0) :
    (Operators.trace (I := I) (M := M) (hessianBilin (I := I) g f) x) ^ 2
      ≤ ((Module.finrank ℝ E : ℝ) - 1)
          * Operators.frobeniusSq (I := I) (M := M) (hessianBilin (I := I) g f) x := by
  subst hg
  set S : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
    (covDerivAt hm.metric (manifoldGradient (I := I) hm.metric f) x).toLinearMap with hS_def
  -- Bridge: `hessianBilin = ⟪S ·, ·⟫` (metric inner is the fibre inner for `hm.metric`).
  have hHB : ∀ v w : TangentSpace I x,
      hessianBilin (I := I) hm.metric f x v w = inner ℝ (S v) w := fun v w => rfl
  -- `S` is symmetric.
  have hSsym : S.IsSymmetric := by
    intro v w
    rw [show inner ℝ (S v) w = hessianBilin (I := I) hm.metric f x v w from (hHB v w).symm,
        hsym v w, hHB w v, real_inner_comm]
  -- `u = ∇f x` is a unit kernel vector.
  set u : TangentSpace I x := manifoldGradient (I := I) hm.metric f x with hu_def
  have hu : ‖u‖ = 1 := by
    have h1 : inner ℝ u u = (1 : ℝ) := hunit
    have : ‖u‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h1
    nlinarith [norm_nonneg u, this]
  have hSu : S u = 0 := by
    have hzero : ∀ w : TangentSpace I x, inner ℝ (S u) w = (0 : ℝ) := by
      intro w
      rw [hSsym u w, real_inner_comm,
          show inner ℝ (S w) u = hessianBilin (I := I) hm.metric f x w u from (hHB w u).symm]
      exact hker w
    have := hzero (S u)
    rwa [inner_self_eq_zero] at this
  -- Apply the refined Cauchy–Schwarz with the standard orthonormal frame.
  have hcs := OpenGA.Comparison.Util.refined_cauchy_schwarz
    (stdOrthonormalBasis ℝ (TangentSpace I x)) S hSsym u hu hSu
  -- Bridge both sides back to `trace` / `frobeniusSq` of the Hessian.
  have htr : Operators.trace (I := I) (M := M) (hessianBilin (I := I) hm.metric f) x
      = ∑ i, inner ℝ (S ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) i) := by
    rw [Operators.trace_def]
    exact Finset.sum_congr rfl (fun i _ => hHB _ _)
  have hfr : Operators.frobeniusSq (I := I) (M := M) (hessianBilin (I := I) hm.metric f) x
      = ∑ i, ∑ j, (inner ℝ (S ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
              ((stdOrthonormalBasis ℝ (TangentSpace I x)) j)) ^ 2 := by
    rw [Operators.frobeniusSq_def]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hHB]))
  rw [htr, hfr]
  exact hcs

end OpenGA.Comparison.BishopGromov
