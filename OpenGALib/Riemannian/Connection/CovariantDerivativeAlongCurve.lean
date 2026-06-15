import OpenGALib.Riemannian.Geodesic.Equation

/-!
# Covariant derivative along a curve

For a curve `γ : ℝ → M` into a Riemannian manifold and a vector field
`V : (t : ℝ) → T_{γ t} M` *along* `γ`, the **covariant derivative along the
curve** `D_t V (t₀) ∈ T_{γ t₀} M` is the intrinsic rate of change of `V` as it is
transported along `γ`. In the chart centred at `γ t₀` it is the chart-coordinate
time-derivative of `V` corrected by the Christoffel contraction of the chart
velocity with `V`:
`(D_t V)(t₀) = φ⁻¹_* ( d/dt[V in coords] + Γ(γ̇, V) )`,
where `φ = extChartAt I (γ t₀)` and `Γ` is `chartChristoffelContraction`.

This is foundational infrastructure for the whole "along-a-curve" calculus —
parallel transport (`D_t V = 0`), Jacobi fields, the first/second variation of
energy, the constant-speed property of geodesics (`D_t γ̇ = 0`), and the radial
structure of the distance function. It is **not** specific to any one application:
`covDeriv`/`covDerivAt` (`Connection/LeviCivita`) differentiate a vector field *on
`M`* in a tangent direction; this differentiates a field defined *only along a
curve*, which is exactly what those cannot express.

## Main definitions

* `covDerivAlongCurve g γ V t₀` — the covariant derivative `D_t V (t₀)`.
-/

open Bundle
open scoped Manifold ContDiff
open Riemannian.Tensor

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **covariant derivative of `V` along the curve `γ`** at `t₀`,
`D_t V (t₀) ∈ T_{γ t₀} M`.

In the chart at `γ t₀`, write `V` in chart-fibre coordinates via the tangent-bundle
trivialization and the chart velocity `γ̇` as `deriv (extChartAt ∘ γ)`; then
`D_t V` is `d/dt` of those coordinates plus the Christoffel contraction
`Γ(γ̇, V)`, pulled back to the fibre `T_{γ t₀} M`. Meaningful where `γ` stays in
the chart source of `γ t₀` near `t₀`. -/
noncomputable def covDerivAlongCurve (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ) : TangentSpace I (γ t₀) :=
  (trivializationAt E (TangentSpace I) (γ t₀)).symmL ℝ (γ t₀)
    (deriv (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (V t)) t₀
      + Geodesic.chartChristoffelContraction (I := I) g (γ t₀)
          (deriv (fun t => extChartAt I (γ t₀) (γ t)) t₀)
          ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀))
          (extChartAt I (γ t₀) (γ t₀)))

/-- **Math.** The covariant derivative along `γ` of the **zero field** is zero:
`D_t 0 = 0`. The chart coordinates of the zero field vanish (so their time
derivative does), and the Christoffel contraction with the zero vector vanishes,
so the pulled-back result is `0`. -/
theorem covDerivAlongCurve_zero (g : RiemannianMetric I M) (γ : ℝ → M) (t₀ : ℝ) :
    covDerivAlongCurve (I := I) g γ (fun t => (0 : TangentSpace I (γ t))) t₀ = 0 := by
  rw [covDerivAlongCurve]
  have hderiv : deriv (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
      (γ t) (0 : TangentSpace I (γ t))) t₀ = 0 := by
    simp only [map_zero, deriv_const']
  rw [hderiv, map_zero,
    Geodesic.chartChristoffelContraction_symm,
    Geodesic.chartChristoffelContraction_zero_left, add_zero, map_zero]

/-- **Math.** **Additivity** of the covariant derivative along a curve:
`D_t (V + W) = D_t V + D_t W`, where the chart coordinates of `V` and `W` along
`γ` are differentiable at `t₀`. Pointwise additivity of the chart coordinates and
of the Christoffel contraction (second slot), plus `deriv` of a sum, plus
linearity of the inverse trivialization. -/
theorem covDerivAlongCurve_add (g : RiemannianMetric I M) (γ : ℝ → M)
    (V W : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hV : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀)
    (hW : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) t₀) :
    covDerivAlongCurve (I := I) g γ (fun t => V t + W t) t₀ =
      covDerivAlongCurve (I := I) g γ V t₀ + covDerivAlongCurve (I := I) g γ W t₀ := by
  rw [covDerivAlongCurve, covDerivAlongCurve, covDerivAlongCurve]
  have hcoord : (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
      (γ t) ((fun t => V t + W t) t))
      = (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t))
        + (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) := by
    funext t; rw [Pi.add_apply]; exact map_add _ _ _
  have harg : (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
      ((fun t => V t + W t) t₀)
      = (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀)
        + (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (W t₀) :=
    map_add _ _ _
  rw [hcoord, (hV.hasDerivAt.add hW.hasDerivAt).deriv, harg,
    Geodesic.chartChristoffelContraction_add_right,
    add_add_add_comm, map_add]

/-- **Math.** **Homogeneity** of the covariant derivative along a curve:
`D_t (a • V) = a • D_t V`, where the chart coordinates of `V` along `γ` are
differentiable at `t₀`. Pointwise homogeneity of the chart coordinates and of the
Christoffel contraction (second slot), plus `deriv` of a scalar multiple, plus
linearity of the inverse trivialization. -/
theorem covDerivAlongCurve_smul (g : RiemannianMetric I M) (γ : ℝ → M) (a : ℝ)
    (V : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hV : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀) :
    covDerivAlongCurve (I := I) g γ (fun t => a • V t) t₀ =
      a • covDerivAlongCurve (I := I) g γ V t₀ := by
  rw [covDerivAlongCurve, covDerivAlongCurve]
  have hcoord : (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
      (γ t) ((fun t => a • V t) t))
      = a • (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
          (γ t) (V t)) := by
    funext t; rw [Pi.smul_apply]; exact map_smul _ _ _
  have harg : (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
      ((fun t => a • V t) t₀)
      = a • (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀) :=
    map_smul _ _ _
  rw [hcoord, (hV.hasDerivAt.const_smul a).deriv, harg,
    Geodesic.chartChristoffelContraction_smul_right, ← smul_add, map_smul]

/-- **Math.** **Leibniz rule** for the covariant derivative along a curve:
`D_t (f • V) = f' • V + f • D_t V` for a scalar function `f : ℝ → ℝ`, where `f`
and the chart coordinates of `V` are differentiable at `t₀`. The product rule for
`deriv` on the chart coordinates produces the `f' • V` term; the chart coordinate
of `V` at the basepoint `γ t₀` is recovered by the trivialization being an inverse
pair there (`symmL_continuousLinearMapAt`). -/
theorem covDerivAlongCurve_smul_scalar (g : RiemannianMetric I M) (γ : ℝ → M) (f : ℝ → ℝ)
    (V : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hf : DifferentiableAt ℝ f t₀)
    (hV : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀) :
    covDerivAlongCurve (I := I) g γ (fun t => f t • V t) t₀
      = deriv f t₀ • V t₀ + f t₀ • covDerivAlongCurve (I := I) g γ V t₀ := by
  have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
    mem_chart_source H (γ t₀)
  rw [covDerivAlongCurve, covDerivAlongCurve]
  have hcoord : (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
      (γ t) ((fun t => f t • V t) t))
      = f • (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
          (γ t) (V t)) := by
    funext t; exact map_smul _ _ _
  have harg : (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀)
      ((fun t => f t • V t) t₀)
      = f t₀ • (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀) :=
    map_smul _ _ _
  rw [hcoord, (hf.hasDerivAt.smul hV.hasDerivAt).deriv, harg,
    Geodesic.chartChristoffelContraction_smul_right]
  set D := deriv (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
    (γ t) (V t)) t₀ with hD
  set G := Geodesic.chartChristoffelContraction (I := I) g (γ t₀)
    (deriv (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀))
    (extChartAt I (γ t₀) (γ t₀)) with hG
  have hre : (f t₀ • D + deriv f t₀ •
        (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀))
        + f t₀ • G
      = deriv f t₀ •
          (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀)
        + f t₀ • (D + G) := by rw [smul_add]; abel
  rw [hre, map_add, map_smul, map_smul,
    (trivializationAt E (TangentSpace I) (γ t₀)).symmL_continuousLinearMapAt hbase]

/-- **Math.** **Metric inner product in chart coordinates (bilinear form).** The
inner product of two linear combinations of chart-basis vectors is the Gram-matrix
bilinear form of the coefficient vectors:
`⟨Σᵢ aᵢ eᵢ, Σⱼ bⱼ eⱼ⟩_g = Σᵢ Σⱼ aᵢ bⱼ G_{ij}`. The bilinear companion of
`chartGramMatrix_dotProduct_mulVec` (which is the `a = b` quadratic case); the
inner-product-in-coordinates bridge feeding the metric-compatibility of `D_t`. -/
theorem metricInner_chartBasis_combination (g : RiemannianMetric I M) (α : M) (x : M)
    (a b : Fin (Module.finrank ℝ E) → ℝ) :
    g.metricInner x (∑ i, a i • chartBasisVecFiber (I := I) α i x)
        (∑ j, b j • chartBasisVecFiber (I := I) α j x)
      = ∑ i, ∑ j, a i * b j * chartGramMatrix (I := I) g α x i j := by
  show g.inner x (∑ i, a i • chartBasisVecFiber (I := I) α i x)
      (∑ j, b j • chartBasisVecFiber (I := I) α j x)
    = ∑ i, ∑ j, a i * b j * chartGramMatrix (I := I) g α x i j
  rw [show g.inner x (∑ i, a i • chartBasisVecFiber (I := I) α i x)
        = ∑ i, a i • g.inner x (chartBasisVecFiber (I := I) α i x) from by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => by rw [map_smul]]
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, chartGramMatrix_apply]
  ring

end Riemannian
