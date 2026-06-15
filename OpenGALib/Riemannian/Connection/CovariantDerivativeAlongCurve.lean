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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Chart-coordinate expansion of a tangent vector.** On the
trivialization base set, any `v : T_b M` is the chart-basis combination of its
trivialization coordinates: `v = Σᵢ (φ v)ᵢ eᵢ(b)`, where the coefficients
`(φ v)ᵢ` are the `Module.finBasis ℝ E` components of the fibre coordinate
`(trivializationAt …).continuousLinearMapAt ℝ b v` and `eᵢ(b)` is
`chartBasisVecFiber α i b`. This is the inverse-trivialization side of the
inner-product-in-coordinates bridge: composed with `metricInner_chartBasis_combination`
(the bilinear Gram form) it expresses `⟨v,w⟩_g` as the Gram bilinear form of the
coordinate vectors — the input to the metric-compatibility of `D_t`. -/
theorem eq_sum_repr_smul_chartBasisVecFiber (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v : TangentSpace I b) :
    v = ∑ i, (Module.finBasis ℝ E).repr
        ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ b v) i
        • chartBasisVecFiber (I := I) α i b := by
  classical
  set T := trivializationAt E (TangentSpace I) α with hT
  have hbasis : ∀ i, chartBasisVecFiber (I := I) α i b
      = T.symmL ℝ b ((Module.finBasis ℝ E) i) := by
    intro i
    unfold chartBasisVecFiber
    rw [Bundle.Trivialization.symmL_apply]
  calc v = T.symmL ℝ b (T.continuousLinearMapAt ℝ b v) :=
        (T.symmL_continuousLinearMapAt hb v).symm
    _ = T.symmL ℝ b (∑ i, (Module.finBasis ℝ E).repr (T.continuousLinearMapAt ℝ b v) i
          • (Module.finBasis ℝ E) i) := by rw [(Module.finBasis ℝ E).sum_repr]
    _ = ∑ i, (Module.finBasis ℝ E).repr (T.continuousLinearMapAt ℝ b v) i
          • chartBasisVecFiber (I := I) α i b := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hbasis]

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

/-- **Math.** **Inner product of two tangent vectors in chart coordinates.** On
the trivialization base set, `⟨v,w⟩_g` is the Gram bilinear form of the
trivialization-coordinate vectors of `v` and `w`:
`⟨v,w⟩_g = Σᵢ Σⱼ (φ v)ᵢ (φ w)ⱼ G_{ij}`. This closes the
inner-product-in-coordinates bridge — `eq_sum_repr_smul_chartBasisVecFiber`
(expand each vector in the chart basis) composed with
`metricInner_chartBasis_combination` (the bilinear Gram form). The basepoint `α`
of the frame is decoupled from the evaluation point `x`, which is exactly the
setup for `D_t` metric-compatibility: the chart is centred at `γ t₀` while the
metric is read at the moving point `γ t`. -/
theorem metricInner_eq_chartGram_bilinear (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (v w : TangentSpace I x) :
    g.metricInner x v w
      = ∑ i, ∑ j,
          (Module.finBasis ℝ E).repr
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) i
            * (Module.finBasis ℝ E).repr
              ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x w) j
            * chartGramMatrix (I := I) g α x i j := by
  conv_lhs => rw [eq_sum_repr_smul_chartBasisVecFiber (I := I) α hx v,
    eq_sum_repr_smul_chartBasisVecFiber (I := I) α hx w]
  exact metricInner_chartBasis_combination (I := I) g α x
    (fun i => (Module.finBasis ℝ E).repr
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) i)
    (fun j => (Module.finBasis ℝ E).repr
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x w) j)

/-- **Math.** **Component of the Christoffel contraction.** The `m`-th chart
coordinate of `Γ(a,b)(y)` reads off the basis-component formula in
`chartChristoffelContraction`: `(Γ(a,b)(y))ᵐ = Σᵢ Σⱼ Γᵐ_{ij}(y) aⁱ bʲ`. The
inverse of the `• eₘ` packaging, isolating the scalar component that pairs with
the Gram matrix in the metric-compatibility cancellation. -/
theorem chartCoord_chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (a b : E) (y : E) (m : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) m (Geodesic.chartChristoffelContraction (I := I) g α a b y)
      = ∑ i, ∑ j, chartChristoffel (I := I) g α i j m y
          * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b := by
  classical
  rw [Geodesic.chartChristoffelContraction_def, Geodesic.chartCoord_def, map_sum,
    Finsupp.finset_sum_apply]
  simp_rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ m
    (fun k => ∑ i, ∑ j, chartChristoffel (I := I) g α i j k y
      * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b)]
  simp

/-- **Math.** **Metric-compatibility cancellation (the algebraic heart of `D_t`
compatibility).** Contracting the directional derivative of the Gram matrix along
`u` against the coordinate vectors `v, w` equals the two Christoffel-correction
terms produced by the covariant derivatives of `v` and `w`:
`Σᵢⱼ vⁱ wʲ (Σₖ uᵏ ∂ₖG_{ij}) = Σᵢⱼ (Γ(u,v)ⁱ wʲ + vⁱ Γ(u,w)ʲ) G_{ij}`.
Pure pointwise algebra: substitute the component metric-compatibility
`∂ₖG_{ij} = Σₘ (G_{mj}Γᵐ_{ki} + G_{im}Γᵐ_{kj})` (`partialDeriv_chartGramOnE_eq`) on
the left and the component formula `chartCoord_chartChristoffelContraction` on the
right; the four-index sums coincide after reindexing. This is the identity that
makes `d/dt⟨V,W⟩ = ⟨D_tV,W⟩ + ⟨V,D_tW⟩` once the chain rule supplies the velocity
`u = γ̇`. -/
theorem chartGram_dirDeriv_eq_christoffel_correction (g : RiemannianMetric I M) (α : M)
    (u v w : E) (y : E)
    (hy : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∑ i, ∑ j, Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w *
        (∑ k, Geodesic.chartCoord (E := E) k u
          * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
      = ∑ i, ∑ j,
          (Geodesic.chartCoord (E := E) i (Geodesic.chartChristoffelContraction (I := I) g α u v y)
              * Geodesic.chartCoord (E := E) j w
            + Geodesic.chartCoord (E := E) i v
              * Geodesic.chartCoord (E := E) j
                  (Geodesic.chartChristoffelContraction (I := I) g α u w y))
          * chartGramOnE (I := I) g α i j y := by
  classical
  -- Expand the component Christoffel contractions on the right.
  simp_rw [chartCoord_chartChristoffelContraction]
  -- Expand the directional Gram derivative on the left.
  simp_rw [partialDeriv_chartGramOnE_eq (I := I) g α _ _ _ y hy]
  -- A reusable reindexing lemma for a 4-nested sum: permuting the four dummy
  -- indices according to an equivalence `e` of the product type leaves the total
  -- sum unchanged.  This is what lets us swap dummies *across* summations, which a
  -- termwise `Finset.sum_congr` is not allowed to do.
  have reindex : ∀ (F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E)
        → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
      (e : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
          ≃ (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
            × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))),
      (∑ i, ∑ j, ∑ k, ∑ m, F i j k m)
        = ∑ i, ∑ j, ∑ k, ∑ m,
            F (e (i, j, k, m)).1 (e (i, j, k, m)).2.1
              (e (i, j, k, m)).2.2.1 (e (i, j, k, m)).2.2.2 := by
    intro F e
    rw [show (∑ i, ∑ j, ∑ k, ∑ m, F i j k m)
          = ∑ p : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              F p.1 p.2.1 p.2.2.1 p.2.2.2 by simp only [Fintype.sum_prod_type],
       show (∑ i, ∑ j, ∑ k, ∑ m,
            F (e (i, j, k, m)).1 (e (i, j, k, m)).2.1
              (e (i, j, k, m)).2.2.1 (e (i, j, k, m)).2.2.2)
          = ∑ p : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
              × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              F (e p).1 (e p).2.1 (e p).2.2.1 (e p).2.2.2 by
        simp only [Fintype.sum_prod_type]]
    exact (Equiv.sum_comp e (fun p => F p.1 p.2.1 p.2.2.1 p.2.2.2)).symm
  -- The swap `i ↔ m` of the first and last dummy.
  let e14 : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      ≃ (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    { toFun := fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1)
      invFun := fun p => (p.2.2.2, p.2.1, p.2.2.1, p.1)
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  -- The swap `j ↔ m` of the second and last dummy.
  let e24 : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))
      ≃ (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)
        × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) :=
    { toFun := fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1)
      invFun := fun p => (p.1, p.2.2.2, p.2.2.1, p.2.1)
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  have he14 : ∀ p, e14 p = (p.2.2.2, p.2.1, p.2.2.1, p.1) := fun _ => rfl
  have he24 : ∀ p, e24 p = (p.1, p.2.2.2, p.2.2.1, p.2.1) := fun _ => rfl
  -- Split the LHS into its two halves at the full-sum level (pure distribution of
  -- `+`, `*` and `∑`, valid termwise in every index).
  have hL :
      (∑ i, ∑ j, Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j w *
          ∑ k, Geodesic.chartCoord (E := E) k u *
            ∑ m, (chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
                + chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y))
        = (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) i v
              * Geodesic.chartCoord (E := E) j w * Geodesic.chartCoord (E := E) k u
              * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y)
          + (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) i v
              * Geodesic.chartCoord (E := E) j w * Geodesic.chartCoord (E := E) k u
              * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  -- Split the RHS into its two halves at the full-sum level.
  have hR :
      (∑ i, ∑ j,
          ((∑ k, ∑ m, chartChristoffel (I := I) g α k m i y * Geodesic.chartCoord (E := E) k u
                  * Geodesic.chartCoord (E := E) m v)
                * Geodesic.chartCoord (E := E) j w
            + Geodesic.chartCoord (E := E) i v
              * ∑ k, ∑ m, chartChristoffel (I := I) g α k m j y
                  * Geodesic.chartCoord (E := E) k u * Geodesic.chartCoord (E := E) m w)
            * chartGramOnE (I := I) g α i j y)
        = (∑ i, ∑ j, ∑ k, ∑ m, chartChristoffel (I := I) g α k m i y
              * Geodesic.chartCoord (E := E) k u * Geodesic.chartCoord (E := E) m v
              * Geodesic.chartCoord (E := E) j w * chartGramOnE (I := I) g α i j y)
          + (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) i v
              * chartChristoffel (I := I) g α k m j y * Geodesic.chartCoord (E := E) k u
              * Geodesic.chartCoord (E := E) m w * chartGramOnE (I := I) g α i j y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [add_mul, Finset.sum_mul, Finset.mul_sum]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
    · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
  rw [hL, hR]
  -- Match the two halves separately, each via the appropriate full-sum reindex.
  congr 1
  · -- First halves coincide after the `i ↔ m` swap.
    rw [reindex (fun i j k m => Geodesic.chartCoord (E := E) i v
        * Geodesic.chartCoord (E := E) j w * Geodesic.chartCoord (E := E) k u
        * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y) e14]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    rw [he14]
    ring
  · -- Second halves coincide after the `j ↔ m` swap.
    rw [reindex (fun i j k m => Geodesic.chartCoord (E := E) i v
        * Geodesic.chartCoord (E := E) j w * Geodesic.chartCoord (E := E) k u
        * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y) e24]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
    rw [he24]
    ring

/-! ### Metric-compatibility of the covariant derivative along a curve

The analysis glue assembling `d/dt⟨V,W⟩ = ⟨D_tV,W⟩ + ⟨V,D_tW⟩` from the algebraic
heart `chartGram_dirDeriv_eq_christoffel_correction`. -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Componentwise derivative of a differentiable `E`-valued curve. If
`F : ℝ → E` has derivative `F'` at `t₀`, then its `i`-th chart component
`Geodesic.chartCoord i ∘ F` has derivative `Geodesic.chartCoord i F'` at `t₀`
(the `i`-th coordinate is a continuous linear functional). -/
private theorem hasDerivAt_chartCoord_of_hasDerivAt
    {F : ℝ → E} {F' : E} {t₀ : ℝ} (hF : HasDerivAt F F' t₀)
    (i : Fin (Module.finrank ℝ E)) :
    HasDerivAt (fun t => Geodesic.chartCoord (E := E) i (F t))
      (Geodesic.chartCoord (E := E) i F') t₀ := by
  have hCLM := ((Module.finBasis ℝ E).coord i).toContinuousLinearMap.hasFDerivAt
    (x := F t₀)
  have := hCLM.comp_hasDerivAt t₀ hF
  simpa only [Function.comp_def, Geodesic.chartCoord, ContinuousLinearMap.coe_coe,
    LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply] using this

/-- **Math.** The Fréchet derivative of `u : E → ℝ` at `y`, applied to a vector
`a : E`, is the `chartCoord`-weighted sum of its chart partial derivatives:
`fderiv u y a = Σ_k aᵏ · ∂_k u y`. Expand `a` in the chart basis and use linearity
of `fderiv u y`. -/
private theorem fderiv_eq_sum_chartCoord_partialDeriv
    (u : E → ℝ) (y : E) (a : E) :
    fderiv ℝ u y a
      = ∑ k, Geodesic.chartCoord (E := E) k a * partialDeriv (E := E) k u y := by
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr a, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, partialDeriv, Geodesic.chartCoord_def]

/-- **Math.** Chain rule for the chart Gram factor along a curve. Let `α : M`,
`c : ℝ → E` differentiable at `t₀` with `c t₀ ∈ (extChartAt I α).target`. Then the
Gram entry pulled along `c`, `t ↦ chartGramOnE g α i j (c t)`, has derivative
`Σ_k (deriv c t₀)ᵏ · ∂_k (chartGramOnE g α i j) (c t₀)` at `t₀`. The chart Gram
entry is `C^∞` on the target (`chartGramOnE_contDiffOn`), hence differentiable at
`c t₀`; the chain rule then converts to the `chartCoord`-weighted partial
derivative sum. -/
private theorem hasDerivAt_chartGramOnE_comp [ModelWithCorners.Boundaryless I]
    (g : RiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {c : ℝ → E} {t₀ : ℝ} (hc : DifferentiableAt ℝ c t₀)
    (hmem : c t₀ ∈ (extChartAt I α).target) :
    HasDerivAt (fun t => chartGramOnE (I := I) g α i j (c t))
      (∑ k, Geodesic.chartCoord (E := E) k (deriv c t₀)
        * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)) t₀ := by
  have htgt : (extChartAt I α).target ∈ nhds (c t₀) :=
    (isOpen_extChartAt_target (I := I) α).mem_nhds hmem
  have hGdiff : DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (c t₀) :=
    ((chartGramOnE_contDiffOn (I := I) g α i j).differentiableOn (by simp)
      _ hmem).differentiableAt htgt
  have hcomp := hGdiff.hasFDerivAt.comp_hasDerivAt t₀ hc.hasDerivAt
  rw [← fderiv_eq_sum_chartCoord_partialDeriv (chartGramOnE (I := I) g α i j) (c t₀)
    (deriv c t₀)]
  exact hcomp

/-- **Math.** Derivative of a single Gram-weighted coordinate product along a
curve. For chart-coordinate functions `Vc Wc : ℝ → E` (the trivialization
coordinates of the two fields) differentiable at `t₀`, and a chart-coordinate
curve `c : ℝ → E` with `c t₀` in the chart target, the `(i,j)` term
`t ↦ vⁱ(t) · wʲ(t) · G_{ij}(c t)` of the bilinear Gram form has, at `t₀`, the
product-rule derivative `(vⁱ)' wʲ G + vⁱ (wʲ)' G + vⁱ wʲ (Σ_k uᵏ ∂_k G)`, with
`u = deriv c t₀`. The three factors are differentiable via
`hasDerivAt_chartCoord_of_hasDerivAt` (twice) and `hasDerivAt_chartGramOnE_comp`. -/
private theorem hasDerivAt_chartGram_term [ModelWithCorners.Boundaryless I]
    (g : RiemannianMetric I M) (α : M) (i j : Fin (Module.finrank ℝ E))
    {Vc Wc c : ℝ → E} {t₀ : ℝ}
    (hVc : DifferentiableAt ℝ Vc t₀) (hWc : DifferentiableAt ℝ Wc t₀)
    (hc : DifferentiableAt ℝ c t₀) (hmem : c t₀ ∈ (extChartAt I α).target) :
    HasDerivAt
      (fun t => Geodesic.chartCoord (E := E) i (Vc t)
        * Geodesic.chartCoord (E := E) j (Wc t)
        * chartGramOnE (I := I) g α i j (c t))
      (Geodesic.chartCoord (E := E) i (deriv Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (deriv Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * (∑ k, Geodesic.chartCoord (E := E) k (deriv c t₀)
                * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)))
      t₀ := by
  have hv := hasDerivAt_chartCoord_of_hasDerivAt (E := E) hVc.hasDerivAt i
  have hw := hasDerivAt_chartCoord_of_hasDerivAt (E := E) hWc.hasDerivAt j
  have hG := hasDerivAt_chartGramOnE_comp (I := I) g α i j hc hmem
  have hprod := ((hv.mul hw).mul hG)
  convert hprod using 1
  simp only [Geodesic.chartCoord_def, Pi.mul_apply]
  ring

/-- **Math.** **Metric-compatibility of the covariant derivative along a curve.**
The Riemannian metric is parallel for `D_t`: the time derivative of the inner
product of two fields `V W` along `γ` is the sum of the inner products with the
covariant derivatives,
`d/dt⟨V,W⟩_g = ⟨D_tV,W⟩_g + ⟨V,D_tW⟩_g`.
The chart-coordinate curves of `V`, `W` and `γ` are assumed differentiable at
`t₀`, and `γ` is continuous at `t₀` (so it stays in the trivialization base set on
a neighborhood, letting the inner product be read as the bilinear Gram form).
The proof differentiates the bilinear Gram form termwise (product rule via
`hasDerivAt_chartGram_term`), expands `D_tV`, `D_tW` through the
trivialization/Christoffel formula of `covDerivAlongCurve`, and cancels the
Gram-derivative term against the two Christoffel corrections with the algebraic
heart `chartGram_dirDeriv_eq_christoffel_correction`. -/
theorem covDerivAlongCurve_metricInner [ModelWithCorners.Boundaryless I]
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (V W : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hVc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (V t)) t₀)
    (hWc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ContinuousAt γ t₀) :
    deriv (fun t => g.metricInner (γ t) (V t) (W t)) t₀
      = g.metricInner (γ t₀) (covDerivAlongCurve (I := I) g γ V t₀) (W t₀)
        + g.metricInner (γ t₀) (V t₀) (covDerivAlongCurve (I := I) g γ W t₀) := by
  classical
  set α := γ t₀ with hα
  set T := trivializationAt E (TangentSpace I) α with hT
  -- chart-coordinate functions of the two fields and of the curve
  set Vc : ℝ → E := fun t => T.continuousLinearMapAt ℝ (γ t) (V t) with hVcdef
  set Wc : ℝ → E := fun t => T.continuousLinearMapAt ℝ (γ t) (W t) with hWcdef
  set c : ℝ → E := fun t => extChartAt I α (γ t) with hcdef
  set u : E := deriv c t₀ with hu
  have hbase : α ∈ T.baseSet := mem_chart_source H α
  -- `c t₀ = extChartAt I α α` is in the chart target
  have hct₀ : c t₀ = extChartAt I α α := rfl
  have hmem : c t₀ ∈ (extChartAt I α).target := by
    rw [hct₀]; exact mem_extChartAt_target α
  -- `(extChartAt I α).symm (c t₀) = α`
  have hsymm : (extChartAt I α).symm (c t₀) = α := by
    rw [hct₀]; exact (extChartAt I α).left_inv (mem_extChartAt_source α)
  -- Bridge: chartGramOnE pulled to `c t₀` is the Gram matrix at `α`.
  have hGram0 : ∀ i j, chartGramOnE (I := I) g α i j (c t₀)
      = chartGramMatrix (I := I) g α α i j := by
    intro i j; rw [chartGramOnE_def, hsymm]
  -- STEP 1: on a neighborhood of `t₀`, the inner product is the bilinear Gram form.
  have hnhds : ∀ᶠ t in nhds t₀, γ t ∈ T.baseSet := by
    have hopen : IsOpen T.baseSet := T.open_baseSet
    exact hγcont (hopen.mem_nhds hbase)
  have hEq : (fun t => g.metricInner (γ t) (V t) (W t))
      =ᶠ[nhds t₀] (fun t => ∑ i, ∑ j,
        Geodesic.chartCoord (E := E) i (Vc t) * Geodesic.chartCoord (E := E) j (Wc t)
          * chartGramOnE (I := I) g α i j (c t)) := by
    filter_upwards [hnhds] with t ht
    have htsrc : γ t ∈ (extChartAt I α).source := by
      rw [extChartAt_source]; exact ht
    rw [metricInner_eq_chartGram_bilinear (I := I) g α ht (V t) (W t)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [chartGramOnE_def, (extChartAt I α).left_inv htsrc]
    rw [hVcdef, hWcdef]; simp only [Geodesic.chartCoord_def, hT]
  -- STEP 2: differentiate the bilinear Gram form termwise (product rule per term).
  have hterm : ∀ i j, HasDerivAt
      (fun t => Geodesic.chartCoord (E := E) i (Vc t)
        * Geodesic.chartCoord (E := E) j (Wc t)
        * chartGramOnE (I := I) g α i j (c t))
      (Geodesic.chartCoord (E := E) i (deriv Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (deriv Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * (∑ k, Geodesic.chartCoord (E := E) k u
                * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)))
      t₀ := fun i j =>
    hasDerivAt_chartGram_term (I := I) g α i j hVc hWc hγc hmem
  -- The whole inner sum (over j) has the sum of the per-term derivatives.
  have hsumj : ∀ i, HasDerivAt
      (fun t => ∑ j, Geodesic.chartCoord (E := E) i (Vc t)
        * Geodesic.chartCoord (E := E) j (Wc t)
        * chartGramOnE (I := I) g α i j (c t))
      (∑ j, (Geodesic.chartCoord (E := E) i (deriv Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (deriv Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * (∑ k, Geodesic.chartCoord (E := E) k u
                * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀))))
      t₀ := fun i => HasDerivAt.fun_sum fun j _ => hterm i j
  have hsum : HasDerivAt
      (fun t => ∑ i, ∑ j, Geodesic.chartCoord (E := E) i (Vc t)
        * Geodesic.chartCoord (E := E) j (Wc t)
        * chartGramOnE (I := I) g α i j (c t))
      (∑ i, ∑ j, (Geodesic.chartCoord (E := E) i (deriv Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (deriv Wc t₀)
            * chartGramOnE (I := I) g α i j (c t₀)
          + Geodesic.chartCoord (E := E) i (Vc t₀)
            * Geodesic.chartCoord (E := E) j (Wc t₀)
            * (∑ k, Geodesic.chartCoord (E := E) k u
                * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀))))
      t₀ := HasDerivAt.fun_sum fun i _ => hsumj i
  rw [hEq.deriv_eq, hsum.deriv]
  -- Abbreviations for the chart coordinates at `t₀`.
  set vc : Fin (Module.finrank ℝ E) → ℝ := fun i => Geodesic.chartCoord (E := E) i (Vc t₀) with hvc
  set wc : Fin (Module.finrank ℝ E) → ℝ := fun j => Geodesic.chartCoord (E := E) j (Wc t₀) with hwc
  set vc' : Fin (Module.finrank ℝ E) → ℝ := fun i => Geodesic.chartCoord (E := E) i (deriv Vc t₀)
    with hvc'
  set wc' : Fin (Module.finrank ℝ E) → ℝ := fun j => Geodesic.chartCoord (E := E) j (deriv Wc t₀)
    with hwc'
  set G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => chartGramOnE (I := I) g α i j (c t₀) with hG
  -- STEP 3: expand the right-hand inner products in chart coordinates.
  -- `⟨D_tV, W⟩ = Σᵢⱼ (vⁱ' + Γ(u,v)ⁱ) wʲ Gᵢⱼ`.
  -- `T.continuousLinearMapAt α (D_t V t₀) = deriv Vc t₀ + Γ(u, Vc t₀)(c t₀)`.
  have hcoordVecDV : T.continuousLinearMapAt ℝ α (covDerivAlongCurve (I := I) g γ V t₀)
      = deriv Vc t₀ + Geodesic.chartChristoffelContraction (I := I) g α u (Vc t₀) (c t₀) := by
    show T.continuousLinearMapAt ℝ α (T.symmL ℝ α _) = _
    rw [T.continuousLinearMapAt_symmL hbase]
  have hcoordVecDW : T.continuousLinearMapAt ℝ α (covDerivAlongCurve (I := I) g γ W t₀)
      = deriv Wc t₀ + Geodesic.chartChristoffelContraction (I := I) g α u (Wc t₀) (c t₀) := by
    show T.continuousLinearMapAt ℝ α (T.symmL ℝ α _) = _
    rw [T.continuousLinearMapAt_symmL hbase]
  -- coordinate of `D_tV` / `D_tW` at `t₀`
  have hcoordDV : ∀ i, Geodesic.chartCoord (E := E) i
      (T.continuousLinearMapAt ℝ α (covDerivAlongCurve (I := I) g γ V t₀))
      = vc' i + Geodesic.chartCoord (E := E) i
          (Geodesic.chartChristoffelContraction (I := I) g α u (Vc t₀) (c t₀)) := by
    intro i; rw [hcoordVecDV, Geodesic.chartCoord_add, hvc']
  have hcoordDW : ∀ j, Geodesic.chartCoord (E := E) j
      (T.continuousLinearMapAt ℝ α (covDerivAlongCurve (I := I) g γ W t₀))
      = wc' j + Geodesic.chartCoord (E := E) j
          (Geodesic.chartChristoffelContraction (I := I) g α u (Wc t₀) (c t₀)) := by
    intro j; rw [hcoordVecDW, Geodesic.chartCoord_add, hwc']
  -- Rewrite both RHS inner products as bilinear Gram forms.
  rw [metricInner_eq_chartGram_bilinear (I := I) g α hbase
        (covDerivAlongCurve (I := I) g γ V t₀) (W t₀),
      metricInner_eq_chartGram_bilinear (I := I) g α hbase
        (V t₀) (covDerivAlongCurve (I := I) g γ W t₀)]
  -- Fold `trivializationAt … α` back to `T`, replace `repr` by `chartCoord`,
  -- bridge `chartGramMatrix` to `G`, and expand the covariant-derivative coords.
  simp only [← hT, ← Geodesic.chartCoord_def]
  have hGbridge : ∀ i j, chartGramMatrix (I := I) g α α i j = G i j := by
    intro i j; rw [hG]; exact (hGram0 i j).symm
  -- coordinate of `W t₀` / `V t₀` at base equals `wc j` / `vc i`
  have hWcoord : ∀ j, Geodesic.chartCoord (E := E) j (T.continuousLinearMapAt ℝ α (W t₀)) = wc j :=
    fun j => rfl
  have hVcoord : ∀ i, Geodesic.chartCoord (E := E) i (T.continuousLinearMapAt ℝ α (V t₀)) = vc i :=
    fun i => rfl
  simp only [hcoordDV, hcoordDW, hWcoord, hVcoord, hGbridge]
  -- STEP 4: algebraic cancellation.
  -- LHS = Σᵢⱼ [vⁱ' wʲ + vⁱ wʲ'] Gᵢⱼ + Σᵢⱼ vⁱ wʲ (Σₖ uᵏ ∂ₖG_ij).
  -- RHS = Σᵢⱼ (vⁱ' + Γ(u,v)ⁱ) wʲ Gᵢⱼ + Σᵢⱼ vⁱ (wʲ' + Γ(u,w)ʲ) Gᵢⱼ.
  -- Difference reduces to the heart identity.
  have hheart := chartGram_dirDeriv_eq_christoffel_correction (I := I) g α u (Vc t₀) (Wc t₀) (c t₀)
    (by rw [hsymm]; exact hbase)
  -- Reassemble: rewrite both sides as a single double sum over `(i,j)`, then match
  -- termwise — using the heart identity for the Gram-derivative block.
  set Γv : Fin (Module.finrank ℝ E) → ℝ := fun i => Geodesic.chartCoord (E := E) i
    (Geodesic.chartChristoffelContraction (I := I) g α u (Vc t₀) (c t₀)) with hΓv
  set Γw : Fin (Module.finrank ℝ E) → ℝ := fun j => Geodesic.chartCoord (E := E) j
    (Geodesic.chartChristoffelContraction (I := I) g α u (Wc t₀) (c t₀)) with hΓw
  -- LHS as a single double sum, with the heart already substituted.
  have hLHS : (∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j
        + vc i * wc j * (∑ k, Geodesic.chartCoord (E := E) k u
            * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀))))
      = ∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j
          + (Γv i * wc j + vc i * Γw j) * G i j) := by
    have hsplit : (∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j
          + vc i * wc j * (∑ k, Geodesic.chartCoord (E := E) k u
              * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀))))
        = (∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j))
          + ∑ i, ∑ j, vc i * wc j * (∑ k, Geodesic.chartCoord (E := E) k u
              * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
    have hmerge : (∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j))
          + ∑ i, ∑ j, ((Γv i * wc j + vc i * Γw j) * G i j)
        = ∑ i, ∑ j, (vc' i * wc j * G i j + vc i * wc' j * G i j
            + (Γv i * wc j + vc i * Γw j) * G i j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
    -- The Gram-derivative block equals the Christoffel-correction block by the heart.
    have hheart' : (∑ i, ∑ j, vc i * wc j * (∑ k, Geodesic.chartCoord (E := E) k u
            * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)))
        = ∑ i, ∑ j, ((Γv i * wc j + vc i * Γw j) * G i j) := by
      rw [show (∑ i, ∑ j, vc i * wc j * (∑ k, Geodesic.chartCoord (E := E) k u
            * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (c t₀)))
          = ∑ i, ∑ j, (Γv i * wc j + vc i * Γw j) * chartGramOnE (I := I) g α i j (c t₀)
            from hheart]
    rw [hsplit, hheart', hmerge]
  rw [hLHS]
  -- RHS: combine the two double sums into one, then match termwise.
  rw [show (∑ i, ∑ j, (vc' i + Γv i) * wc j * G i j)
          + ∑ i, ∑ j, vc i * (wc' j + Γw j) * G i j
        = ∑ i, ∑ j, ((vc' i + Γv i) * wc j * G i j + vc i * (wc' j + Γw j) * G i j) from by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Riemannian
