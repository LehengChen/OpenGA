import OpenGALib.Riemannian.Connection.GeodesicCovDeriv
import OpenGALib.Riemannian.Curvature.RiemannCurvature

/-!
# Jacobi fields along a curve

For a curve `γ : ℝ → M` into a smooth Riemannian manifold and an along-curve
section `J : (t) → T_{γ t} M`, the **Jacobi equation** is the second-order linear
ODE
`D_t² J + R(J, γ') γ' = 0`,
where `D_t` is the covariant derivative along `γ` (`covDerivAlongCurve`) and `R` is
the Riemann curvature tensor (`riemannCurvature`). A solution is a **Jacobi field**;
it is the variation field of a one-parameter family of geodesics, and it governs the
infinitesimal spreading of geodesics — the analytic engine of the Bishop–Gromov
volume comparison.

This file is the first brick of a Jacobi-field-based Bishop–Gromov proof. It sets up
the equation and proves the elementary but essential **Gauss orthogonality** fact:
along a geodesic, a Jacobi field that starts tangentially orthogonal to the velocity
stays orthogonal, `⟨J, γ'⟩_g ≡ 0`.

## Main definitions

* `covDerivAlongCurve2 g γ J` — the second covariant derivative `D_t² J` along `γ`.
* `jacobiCurvatureTerm g γ J t` — the curvature term `R(J, γ') γ'` at time `t`,
  built from `riemannCurvature` on the constant sections of the tangent vectors.
* `IsJacobiFieldAlong g γ J` — the Jacobi-equation predicate `D_t² J + R(J,γ')γ' = 0`.

## Main results

* `riemannCurvature_inner_self_zero_const` — the pointwise self-orthogonality
  `⟨R(u,v)v, v⟩_g = 0` for tangent vectors `u v`, via the smooth-field headline on
  constant fields.
* `IsJacobiFieldAlong.metricInner_curveVelocity_eq_zero` — **Gauss orthogonality**:
  for a geodesic `γ` and a Jacobi field `J` with `J 0 = 0` and `⟨(D_t J) 0, γ'(0)⟩ = 0`,
  one has `⟨J t, γ'(t)⟩_g = 0` for all `t`.
-/

open Bundle
open scoped Manifold ContDiff Topology
open Riemannian.Tensor

namespace Riemannian

section JacobiDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [IsLocallyConstantChartedSpace H M] [HasMetric I M]

/-- **Math.** The **second covariant derivative** of `J` along `γ`,
`D_t² J (t) = D_t (D_t J) (t) ∈ T_{γ t} M`. The inner `D_t J` is itself an
along-curve section, to which `covDerivAlongCurve` is applied a second time. -/
noncomputable def covDerivAlongCurve2 (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  covDerivAlongCurve (I := I) g γ
    (fun s => covDerivAlongCurve (I := I) g γ J s) t

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [ModelWithCorners.Boundaryless I] [T2Space M] [IsLocallyConstantChartedSpace H M]
  [HasMetric I M] in
@[simp] lemma covDerivAlongCurve2_def (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) :
    covDerivAlongCurve2 (I := I) g γ J t
      = covDerivAlongCurve (I := I) g γ
          (fun s => covDerivAlongCurve (I := I) g γ J s) t := rfl

/-- **Math.** The **Jacobi curvature term** `R(J, γ') γ'` at time `t`, an element of
`T_{γ t} M`. The Riemann tensor `riemannCurvature` consumes bare vector-field
sections `(y) → T_y M`; since `T_y M` is reducibly `E`, each tangent vector at
`γ t` is fed in as the constant section `fun _ => ·`. -/
noncomputable def jacobiCurvatureTerm (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) : TangentSpace I (γ t) :=
  riemannCurvature g (fun _ => J t) (fun _ => curveVelocity (I := I) γ t)
    (fun _ => curveVelocity (I := I) γ t) (γ t)

@[simp] lemma jacobiCurvatureTerm_def (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) (t : ℝ) :
    jacobiCurvatureTerm (I := I) g γ J t
      = riemannCurvature g (fun _ => J t) (fun _ => curveVelocity (I := I) γ t)
          (fun _ => curveVelocity (I := I) γ t) (γ t) := rfl

/-- **Math.** The **Jacobi-equation predicate**. `J` is a Jacobi field along `γ`
iff it satisfies the second-order linear ODE
`D_t² J + R(J, γ') γ' = 0` at every time. -/
def IsJacobiFieldAlong (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) : Prop :=
  ∀ t, covDerivAlongCurve2 (I := I) g γ J t + jacobiCurvatureTerm (I := I) g γ J t = 0

@[simp] lemma isJacobiFieldAlong_iff (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t)) :
    IsJacobiFieldAlong (I := I) g γ J
      ↔ ∀ t, covDerivAlongCurve2 (I := I) g γ J t
          + jacobiCurvatureTerm (I := I) g γ J t = 0 := Iff.rfl

end JacobiDef

/-! ## Gauss orthogonality `⟨J, γ'⟩ ≡ 0` -/

section GaussOrthogonality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 2 M] [T2Space M] [IsLocallyConstantChartedSpace H M] [HasMetric I M]

/-- **Math.** **Pointwise self-orthogonality of the curvature term.** For tangent
vectors `u v : T_x M`, `⟨R(u, v) v, v⟩_g = 0`. This is the do Carmo §4 Prop. 2.5(iii)
self-orthogonality `⟨R(X,Y)Z, Z⟩ = 0` specialised to the constant smooth vector
fields `cF[u], cF[v], cF[v]`; the boundary hypothesis of the headline is discharged
under `Boundaryless I`. -/
theorem riemannCurvature_inner_self_zero_const
    (g : RiemannianMetric I M) (x : M) (u v : TangentSpace I x) :
    g.metricInner x
        (riemannCurvature g (fun _ => u) (fun _ => v) (fun _ => v) x) v = 0 := by
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  have h := riemannCurvature_inner_self_zero g
    (SmoothVectorField.const (I := I) (M := M) u)
    (SmoothVectorField.const (I := I) (M := M) v)
    (SmoothVectorField.const (I := I) (M := M) v) x h_interior
  simpa only [SmoothVectorField.const_apply] using h

/-- **Math.** **Gauss orthogonality of a Jacobi field.** Along a geodesic `γ`, a
Jacobi field `J` whose initial value vanishes (`J 0 = 0`) and whose initial
covariant derivative is orthogonal to the velocity (`⟨(D_t J) 0, γ'(0)⟩_g = 0`)
stays pointwise orthogonal to the velocity: `⟨J t, γ'(t)⟩_g = 0` for all `t`.

Let `f t := ⟨J t, γ'(t)⟩_g`. Metric-compatibility of `D_t` and `D_t γ' = 0`
(geodesic) give `f' = ⟨D_t J, γ'⟩` and `f'' = ⟨D_t² J, γ'⟩`. The Jacobi equation
turns `D_t² J` into `-R(J,γ')γ'`, whose inner product with `γ'` is `0` by
`riemannCurvature_inner_self_zero_const`; so `f'' ≡ 0`. Line-constancy then
propagates the two initial conditions: `f'` is constant `= ⟨(D_t J) 0, γ'(0)⟩ = 0`,
hence `f` is constant `= ⟨J 0, γ'(0)⟩ = ⟨0, γ'(0)⟩ = 0`. -/
theorem IsJacobiFieldAlong.metricInner_curveVelocity_eq_zero
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (J : (t : ℝ) → TangentSpace I (γ t))
    (hJac : IsJacobiFieldAlong (I := I) g γ J)
    (hgeo : Geodesic.IsGeodesic (I := I) g γ)
    (hγdiff : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    -- chart-coordinate differentiability of `J`, `D_t J`, and `γ` at every base time
    (hJc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (J t)) t₀)
    (hDJc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlongCurve (I := I) g γ J t)) t₀)
    (hVc : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (curveVelocity (I := I) γ t)) t₀)
    (hγc : ∀ t₀, DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    -- global differentiability of the two scalar functions `f` and `f'`
    (hf : Differentiable ℝ
      (fun t => g.metricInner (γ t) (J t) (curveVelocity (I := I) γ t)))
    (hf' : Differentiable ℝ
      (fun t => g.metricInner (γ t)
        (covDerivAlongCurve (I := I) g γ J t) (curveVelocity (I := I) γ t)))
    (hJ0 : J 0 = 0)
    (hDJ0 : g.metricInner (γ 0)
      (covDerivAlongCurve (I := I) g γ J 0) (curveVelocity (I := I) γ 0) = 0)
    (t : ℝ) :
    g.metricInner (γ t) (J t) (curveVelocity (I := I) γ t) = 0 := by
  classical
  set V : (s : ℝ) → TangentSpace I (γ s) := curveVelocity (I := I) γ with hV
  set f : ℝ → ℝ := fun s => g.metricInner (γ s) (J s) (V s) with hfdef
  set h : ℝ → ℝ := fun s => g.metricInner (γ s) (covDerivAlongCurve (I := I) g γ J s) (V s)
    with hhdef
  -- `D_t γ' = 0` everywhere (geodesic).
  have hDV : ∀ s, covDerivAlongCurve (I := I) g γ V s = 0 := fun s =>
    IsGeodesic.covDerivAlongCurve_curveVelocity_eq_zero hgeo hγdiff s
  -- continuity of `γ` at every time
  have hγcont : ∀ s, ContinuousAt γ s := fun s => (hγdiff s).continuousAt
  -- STEP 1: `deriv f s = ⟨(D_t J) s, γ'(s)⟩ = h s`.
  have hderiv_f : ∀ s, deriv f s = h s := by
    intro s
    have := covDerivAlongCurve_metricInner g γ J V s
      (hJc s) (hVc s) (hγc s) (hγcont s)
    rw [hfdef, this, hDV s, g.metricInner_zero_right, add_zero]
  -- STEP 2: `deriv h s = ⟨(D_t² J) s, γ'(s)⟩`.
  have hderiv_h : ∀ s, deriv h s
      = g.metricInner (γ s) (covDerivAlongCurve2 (I := I) g γ J s) (V s) := by
    intro s
    have := covDerivAlongCurve_metricInner g γ (covDerivAlongCurve (I := I) g γ J) V s
      (hDJc s) (hVc s) (hγc s) (hγcont s)
    rw [hhdef, this, hDV s, g.metricInner_zero_right, add_zero, covDerivAlongCurve2_def]
  -- STEP 3: `⟨(D_t² J) s, γ'(s)⟩ = 0`, hence `deriv h ≡ 0`.
  have hderiv_h_zero : ∀ s, deriv h s = 0 := by
    intro s
    rw [hderiv_h s]
    -- Jacobi: `D_t² J s = - R(J,γ')γ' s`.
    have hjac := hJac s
    have hD2 : covDerivAlongCurve2 (I := I) g γ J s
        = - jacobiCurvatureTerm (I := I) g γ J s := by
      rw [eq_neg_iff_add_eq_zero]; exact hjac
    rw [hD2, g.metricInner_neg_left, hV, jacobiCurvatureTerm_def,
      riemannCurvature_inner_self_zero_const g (γ s) (J s) (curveVelocity (I := I) γ s),
      neg_zero]
  -- STEP 4a: `h` is constant `= h 0 = 0`.
  have hh_const : ∀ s, h s = h 0 := fun s =>
    is_const_of_deriv_eq_zero hf' hderiv_h_zero s 0
  have hh0 : h 0 = 0 := hDJ0
  have hh_zero : ∀ s, h s = 0 := fun s => (hh_const s).trans hh0
  -- STEP 4b: `deriv f ≡ 0`, so `f` is constant `= f 0 = 0`.
  have hderiv_f_zero : ∀ s, deriv f s = 0 := fun s => (hderiv_f s).trans (hh_zero s)
  have hf_const : ∀ s, f s = f 0 := fun s =>
    is_const_of_deriv_eq_zero hf hderiv_f_zero s 0
  have hf0 : f 0 = 0 := by
    rw [hfdef]; simp only; rw [hJ0, g.metricInner_zero_left]
  exact (hf_const t).trans hf0

end GaussOrthogonality

end Riemannian
