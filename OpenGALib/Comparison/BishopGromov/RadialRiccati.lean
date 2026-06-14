import OpenGALib.Riemannian.Operators.Bochner
import OpenGALib.Comparison.BishopGromov.RiccatiComparison

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

end OpenGA.Comparison.BishopGromov
