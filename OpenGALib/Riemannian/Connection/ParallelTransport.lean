import OpenGALib.Riemannian.Connection.GeodesicCovDeriv

/-!
# Parallel transport along a curve

A vector field `V` along a curve `γ : ℝ → M` into a smooth Riemannian manifold is
**parallel** when its covariant derivative along the curve vanishes everywhere,
`D_t V = 0`. This file defines that notion and proves the cornerstone fact that
**parallel transport is an isometry**: if `V` and `W` are both parallel along `γ`,
the inner product `t ↦ ⟨V t, W t⟩_g` is constant in `t`.

## The proof

Metric-compatibility of `D_t` (`covDerivAlongCurve_metricInner`, the `V ≠ W`
headline) gives
`d/dt ⟨V,W⟩ = ⟨D_tV, W⟩ + ⟨V, D_tW⟩`.
When `V` and `W` are parallel both covariant derivatives vanish, so the derivative
is `0` at every time. A `Differentiable ℝ` real function with everywhere-vanishing
derivative is constant (`is_const_of_deriv_eq_zero`), hence `⟨V,W⟩` equals its value
at `0`.

This is the `V ≠ W` generalisation of the constant-speed corollary
`covDerivAlongCurve_curveVelocity_metricInner_deriv_eq_zero` in `GeodesicCovDeriv.lean`,
extended from "derivative vanishes at one point" to "constant on all of `ℝ`".

## Main definitions / results

* `IsParallelAlong` — `V` is parallel along `γ` iff `D_t V ≡ 0`.
* `IsParallelAlong.metricInner_const` — parallel transport is an isometry: for
  parallel `V`, `W` the Gram product `⟨V,W⟩_g` is constant in `t`.
* `IsParallelAlong.norm_sq_const` — a parallel field has constant squared length;
  combined with `metricInner_const` this is the "parallel transport preserves
  orthonormality" fact.
-/

open scoped Manifold ContDiff Topology
open Riemannian.Tensor

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A vector field `V` along a curve `γ` is **parallel** when its covariant
derivative along the curve vanishes at every time: `D_t V t = 0` for all `t`. -/
def IsParallelAlong (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace I (γ t)) : Prop :=
  ∀ t, covDerivAlongCurve (I := I) g γ V t = 0

/-- **Math.** **Parallel transport is an isometry.** If `V` and `W` are both parallel
along `γ`, then the metric inner product `t ↦ ⟨V t, W t⟩_g` is constant: it equals its
value at `0` for every `t`.

Metric-compatibility of `D_t` (`covDerivAlongCurve_metricInner`) gives
`d/dt ⟨V,W⟩ = ⟨D_tV, W⟩ + ⟨V, D_tW⟩`; both covariant derivatives vanish by `hV`, `hW`,
so the derivative is `0` everywhere, and a differentiable real function with vanishing
derivative is constant.

The chart-coordinate differentiability hypotheses mirror `covDerivAlongCurve_metricInner`,
now quantified over every base time `t₀`; the global `Differentiable ℝ` of the scalar
`⟨V,W⟩` powers the line-constancy step. -/
theorem IsParallelAlong.metricInner_const [ModelWithCorners.Boundaryless I]
    {g : RiemannianMetric I M} {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace I (γ t)}
    (hV : IsParallelAlong g γ V) (hW : IsParallelAlong g γ W)
    (hVc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀)
    (hWc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) t₀)
    (hγc : ∀ t₀, DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ∀ t₀, ContinuousAt γ t₀)
    (hInner : Differentiable ℝ (fun t => g.metricInner (γ t) (V t) (W t))) :
    ∀ t, g.metricInner (γ t) (V t) (W t)
      = g.metricInner (γ 0) (V 0) (W 0) := by
  -- The derivative of the inner product vanishes at every time.
  have hderiv : ∀ t₀, deriv (fun t => g.metricInner (γ t) (V t) (W t)) t₀ = 0 := by
    intro t₀
    rw [covDerivAlongCurve_metricInner g γ V W t₀
        (hVc t₀) (hWc t₀) (hγc t₀) (hγcont t₀),
      hV t₀, hW t₀, g.metricInner_zero_left, g.metricInner_zero_right, add_zero]
  -- A differentiable real function with vanishing derivative is constant.
  intro t
  exact is_const_of_deriv_eq_zero hInner hderiv t 0

/-- **Math.** **A parallel field has constant squared length.** Specialising
`IsParallelAlong.metricInner_const` to `W = V`, a field `V` parallel along `γ` has
constant squared norm `⟨V,V⟩_g`. Together with the general bilinear statement this is
the fact that **parallel transport preserves orthonormality**: angles and lengths of
parallel frames are constant along the curve. -/
theorem IsParallelAlong.norm_sq_const [ModelWithCorners.Boundaryless I]
    {g : RiemannianMetric I M} {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace I (γ t)}
    (hV : IsParallelAlong g γ V)
    (hVc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀)
    (hγc : ∀ t₀, DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ∀ t₀, ContinuousAt γ t₀)
    (hInner : Differentiable ℝ (fun t => g.metricInner (γ t) (V t) (V t))) :
    ∀ t, g.metricInner (γ t) (V t) (V t)
      = g.metricInner (γ 0) (V 0) (V 0) :=
  hV.metricInner_const hV hVc hVc hγc hγcont hInner

end Riemannian
