import OpenGALib.Riemannian.Connection.ParallelTransport
import OpenGALib.Riemannian.Curvature.JacobiField

/-!
# Parallel frame: the covariant derivative is the component derivative

The Bishop–Gromov Jacobi route (CH21) writes Jacobi fields in a **parallel
orthonormal frame** `v₁(t), …, vₙ(t)` along the geodesic (CH21 L121) so that the
covariant derivative `D_t` becomes the ordinary componentwise time-derivative — the
device that turns the Jacobi equation into the matrix ODE `A'' + R̃ A = 0` and lets
`∂_t det A = Σᵢ det(… Jᵢ' …)` (CH21 L150–154).

This file records the analytic atom behind that device: for a field `E` that is
**parallel** at `t₀` (`D_t E = 0`), the time-derivative of the inner product
`⟨W, E⟩_g` is the inner product of the covariant derivative with `E`:
`d/dt ⟨W, E⟩_g = ⟨D_t W, E⟩_g`. It is the metric-compatibility identity
`covDerivAlongCurve_metricInner` (item ①) with the `D_t E` term killed by
parallelism. Stated in `HasDerivAt` form so it can be **iterated** (apply once to
`W = J` and once to `W = D_t J`) to read off the second covariant derivative of a
Jacobi field as the second component derivative.

The parallel orthonormal frame whose existence underlies this route is the
deliverable of issue #86 (parallel-transport existence); here `E` parallel is taken
as a hypothesis, faithful to CH21's use of the frame.

## Main results

* `hasDerivAt_metricInner_parallel_right` — `d/dt ⟨W, E⟩_g = ⟨D_t W, E⟩_g` (in
  `HasDerivAt` form) when `E` is parallel at `t₀`.
-/

open Bundle
open scoped Manifold ContDiff Topology
open Riemannian.Tensor

namespace OpenGA.Comparison.BishopGromov

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Covariant derivative = component derivative against a parallel field.**
For along-curve fields `W` and `E` with `E` parallel at `t₀` (`D_t E (t₀) = 0`), the
inner product `t ↦ ⟨W t, E t⟩_g` has derivative `⟨D_t W (t₀), E t₀⟩_g` at `t₀`.

This is the metric-compatibility identity `covDerivAlongCurve_metricInner`
`d/dt⟨W,E⟩ = ⟨D_tW,E⟩ + ⟨W,D_tE⟩` with the second term annihilated by `D_t E = 0`.
The conclusion is packaged as `HasDerivAt` (using the supplied differentiability of
the scalar inner product) so it can be iterated to extract second covariant
derivatives — the engine of the parallel-frame reduction of the Jacobi equation. -/
theorem hasDerivAt_metricInner_parallel_right
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (W Efield : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hE : covDerivAlongCurve (I := I) g γ Efield t₀ = 0)
    (hWc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) t₀)
    (hEc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (Efield t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ContinuousAt γ t₀)
    (hdiff : DifferentiableAt ℝ (fun t => g.metricInner (γ t) (W t) (Efield t)) t₀) :
    HasDerivAt (fun t => g.metricInner (γ t) (W t) (Efield t))
      (g.metricInner (γ t₀) (covDerivAlongCurve (I := I) g γ W t₀) (Efield t₀)) t₀ := by
  have hval := covDerivAlongCurve_metricInner g γ W Efield t₀ hWc hEc hγc hγcont
  rw [hE, g.metricInner_zero_right, add_zero] at hval
  exact hval ▸ hdiff.hasDerivAt

section JacobiRow

variable [CompleteSpace E] [T2Space M] [IsLocallyConstantChartedSpace H M] [HasMetric I M]

/-- **Math.** **Second component derivative of a Jacobi field against a parallel
field = minus the curvature term.** For a Jacobi field `J` along `γ` and a field `E`
parallel at `t₀`, the first-component derivative `t ↦ ⟨D_t J, E⟩_g` has, at `t₀`,
derivative `-⟨R(J, γ') γ', E⟩_g`. Equivalently the parallel-frame component
`c(t) = ⟨J, E⟩` satisfies `c''(t₀) = -⟨R(J,γ')γ', E⟩` — exactly the row of the
Jacobi matrix ODE `A'' + R̃ A = 0` (CH21 L156–168) read against the frame.

Apply the parallel-frame atom `hasDerivAt_metricInner_parallel_right` to
`W = D_t J`: its derivative is `⟨D_t (D_t J), E⟩ = ⟨D_t² J, E⟩`; the Jacobi equation
`D_t² J = -R(J,γ')γ'` (`hJac`) turns this into `-⟨R(J,γ')γ', E⟩`. -/
theorem hasDerivAt_metricInner_covDeriv_jacobi
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (J Efield : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hJac : Riemannian.IsJacobiFieldAlong (I := I) g γ J)
    (hE : covDerivAlongCurve (I := I) g γ Efield t₀ = 0)
    (hDJc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlongCurve (I := I) g γ J t)) t₀)
    (hEc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (Efield t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ContinuousAt γ t₀)
    (hdiff : DifferentiableAt ℝ (fun t =>
      g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J t) (Efield t)) t₀) :
    HasDerivAt (fun t => g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J t) (Efield t))
      (-(g.metricInner (γ t₀) (Riemannian.jacobiCurvatureTerm (I := I) g γ J t₀) (Efield t₀))) t₀ := by
  have hatom := hasDerivAt_metricInner_parallel_right g γ
    (fun s => covDerivAlongCurve (I := I) g γ J s) Efield t₀ hE hDJc hEc hγc hγcont hdiff
  -- The covariant derivative of `D_t J` is `D_t² J = -R(J,γ')γ'` by the Jacobi equation.
  have h2 : covDerivAlongCurve (I := I) g γ (fun s => covDerivAlongCurve (I := I) g γ J s) t₀
      = -(Riemannian.jacobiCurvatureTerm (I := I) g γ J t₀) := by
    have hj := hJac t₀
    rw [Riemannian.covDerivAlongCurve2_def] at hj
    exact eq_neg_of_add_eq_zero_left hj
  rw [h2, g.metricInner_neg_left] at hatom
  exact hatom

end JacobiRow

end OpenGA.Comparison.BishopGromov
