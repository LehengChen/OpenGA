import OpenGALib.Riemannian.Connection.CovariantDerivativeAlongCurve

/-!
# The geodesic velocity field and `D_t γ' = 0`

For a curve `γ : ℝ → M` into a smooth Riemannian manifold, the **velocity field**
`curveVelocity γ` is the honest along-curve section `t ↦ γ̇(t) ∈ T_{γ t} M`, defined
as the manifold derivative `mfderiv 𝓘(ℝ,ℝ) I γ t` applied to the unit tangent
`(1 : ℝ)`.

The headline result is the classical characterisation of geodesics by their
covariant acceleration: a geodesic has vanishing covariant derivative of its own
velocity,
`D_t γ' = 0`.
Concretely, `covDerivAlongCurve g γ (curveVelocity γ) t₀ = 0` whenever the
moving-foot geodesic equation `HasGeodesicEquationAt g γ t₀` holds; globally,
`IsGeodesic g γ → ∀ t₀, covDerivAlongCurve g γ (curveVelocity γ) t₀ = 0`.

## The bridge

The chart that `covDerivAlongCurve` uses at `t₀` is the canonical chart at `γ t₀`,
which is *exactly* the chart that `HasGeodesicEquationAt` reads the geodesic
equation in at base time `t₀`. The crux is the **velocity-coordinate bridge**: in a
neighbourhood of `t₀`, the trivialization coordinate of the velocity field equals
the chart-velocity of the curve,
`T.continuousLinearMapAt (γ t) (curveVelocity γ t) = deriv (extChartAt I (γ t₀) ∘ γ) t`,
which follows from `TangentBundle.continuousLinearMapAt_trivializationAt`
(the trivialization coordinate is `mfderiv (extChartAt …)`), the chain rule
`mfderiv_comp`, and `mfderiv ↔ deriv` for `ℝ`-curves into the model vector space.
The geodesic identity `a + Γ(v,v) = 0` then collapses `covDerivAlongCurve` to `0`.

## Main definitions / results

* `curveVelocity γ` — the velocity field `γ̇` as an along-curve section.
* `covDerivAlongCurve_curveVelocity_eq_zero` — `D_t γ' = 0` at a single time from
  `HasGeodesicEquationAt`.
* `IsGeodesic.covDerivAlongCurve_curveVelocity_eq_zero` — the global form.
-/

open Bundle
open scoped Manifold ContDiff Topology
open Riemannian.Tensor

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **velocity field** of a curve `γ : ℝ → M` as an honest along-curve
section: `curveVelocity γ t = γ̇(t) ∈ T_{γ t} M`, the manifold derivative of `γ` at
`t` applied to the unit tangent `(1 : ℝ) = TangentSpace 𝓘(ℝ,ℝ) t`. -/
noncomputable def curveVelocity (γ : ℝ → M) : (t : ℝ) → TangentSpace I (γ t) :=
  fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
@[simp] lemma curveVelocity_def (γ : ℝ → M) (t : ℝ) :
    curveVelocity (I := I) γ t = mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) := rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** `mfderiv ↔ deriv` for an `ℝ`-curve into a model vector space: for
`c : ℝ → E`, `mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) c t 1 = deriv c t`. The manifold derivative
between model vector spaces is the Fréchet derivative (`mfderiv_eq_fderiv`), and a
continuous linear map `ℝ →L E` evaluated at `1` is `deriv`. -/
private lemma mfderiv_one_eq_deriv (c : ℝ → E) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t (1 : ℝ) = deriv c t := by
  rw [mfderiv_eq_fderiv]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Velocity-coordinate bridge (B).** Where `γ t` lies in the canonical
chart source at `α := γ t₀`, the trivialization coordinate of the velocity field is
the chart-velocity of the curve:
`T.continuousLinearMapAt (γ t) (curveVelocity γ t) = deriv (chartLocalCurve γ t₀) t`,
where `chartLocalCurve γ t₀ = extChartAt I α ∘ γ`. Combine
`TangentBundle.continuousLinearMapAt_trivializationAt` (the coordinate is
`mfderiv (extChartAt I α)`) with the chain rule `mfderiv_comp` and `mfderiv ↔ deriv`. -/
private lemma continuousLinearMapAt_curveVelocity_eq_deriv
    {γ : ℝ → M} {t₀ : ℝ} {t : ℝ}
    (ht : γ t ∈ (chartAt H (γ t₀)).source) (hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (curveVelocity (I := I) γ t)
      = deriv (Geodesic.chartLocalCurve (I := I) γ t₀) t := by
  have hext : γ t ∈ (extChartAt I (γ t₀)).source := by
    rw [extChartAt_source]; exact ht
  -- The trivialization coordinate is the manifold derivative of `extChartAt I α`.
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (𝕜 := ℝ) (I := I) ht]
  -- Chain rule: `mfderiv (extChartAt I α ∘ γ) t = mfderiv (extChartAt I α) (γ t) ∘ mfderiv γ t`.
  have hExtDiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t) :=
    mdifferentiableAt_extChartAt (I := I) ht
  have hcomp :
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (extChartAt I (γ t₀) ∘ γ) t
        = (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t)).comp
            (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hExtDiff hγt
  have happ : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (extChartAt I (γ t₀) ∘ γ) t (1 : ℝ)
      = (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t))
          ((mfderiv 𝓘(ℝ, ℝ) I γ t) (1 : ℝ)) := by
    rw [hcomp]; rfl
  show (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ t₀)) (γ t)) (curveVelocity (I := I) γ t)
      = deriv (Geodesic.chartLocalCurve (I := I) γ t₀) t
  rw [curveVelocity_def, ← happ]
  rw [show (extChartAt I (γ t₀) ∘ γ) = Geodesic.chartLocalCurve (I := I) γ t₀ from rfl]
  exact mfderiv_one_eq_deriv (Geodesic.chartLocalCurve (I := I) γ t₀) t

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **`D_t γ' = 0` for geodesics (single time).** If `γ` satisfies the
moving-foot geodesic equation at `t₀` and is `MDifferentiable` on a neighbourhood of
`t₀` (so its velocity field has well-defined chart coordinates near `t₀`), then the
covariant derivative of its velocity along itself vanishes:
`covDerivAlongCurve g γ (curveVelocity γ) t₀ = 0`.

The trivialization coordinate of the velocity field equals the chart-velocity of
the curve on a neighbourhood of `t₀` (bridge `(B)`); differentiating, the chart
coordinate's time-derivative is the geodesic acceleration `a`, the coordinate value
at `t₀` is the velocity `v`, and the chart-velocity slot of `covDerivAlongCurve` is
also `v`. The geodesic identity `a + Γ(v,v) = 0` then sends the whole bracket to `0`
through the linear inverse trivialization. -/
theorem covDerivAlongCurve_curveVelocity_eq_zero
    (g : RiemannianMetric I M) (γ : ℝ → M) (t₀ : ℝ)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t₀)
    (hγdiff : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    covDerivAlongCurve (I := I) g γ (curveVelocity (I := I) γ) t₀ = 0 := by
  classical
  obtain ⟨v, a, hv, _hev, ha, hgeoeq⟩ := hgeo
  set α := γ t₀ with hα
  set T := trivializationAt E (TangentSpace I) α with hT
  set u : ℝ → E := Geodesic.chartLocalCurve (I := I) γ t₀ with hu
  -- `γ` is continuous at `t₀` from `MDifferentiableAt`.
  have hγdiff₀ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t₀ := hγdiff.self_of_nhds
  have hγcont : ContinuousAt γ t₀ := hγdiff₀.continuousAt
  -- `γ t ∈ (chartAt H α).source` on a neighbourhood of `t₀`.
  have hbase : α ∈ (chartAt H α).source := mem_chart_source H α
  have hsrcnhds : ∀ᶠ t in 𝓝 t₀, γ t ∈ (chartAt H α).source :=
    hγcont ((chartAt H α).open_source.mem_nhds hbase)
  -- Bridge (B): on a neighbourhood, the coordinate function is `deriv u`.
  have hcoordEq : (fun t => T.continuousLinearMapAt ℝ (γ t)
      (curveVelocity (I := I) γ t)) =ᶠ[𝓝 t₀] (fun t => deriv u t) := by
    filter_upwards [hsrcnhds, hγdiff] with t ht hdt
    exact continuousLinearMapAt_curveVelocity_eq_deriv (I := I) ht hdt
  -- Value at `t₀`: the coordinate equals `v`.
  have hcoord₀ : T.continuousLinearMapAt ℝ (γ t₀) (curveVelocity (I := I) γ t₀) = v := by
    have hbridge := continuousLinearMapAt_curveVelocity_eq_deriv (I := I) hbase hγdiff₀
    rw [hbridge, ← hu, hv.deriv]
  -- Derivative of the coordinate function at `t₀` is the geodesic acceleration `a`.
  have hcoordDeriv : deriv (fun t => T.continuousLinearMapAt ℝ (γ t)
      (curveVelocity (I := I) γ t)) t₀ = a := by
    rw [hcoordEq.deriv_eq]
    exact ha.deriv
  -- Chart-velocity slot of `covDerivAlongCurve` is also `v`.
  have hchartVel : deriv (fun t => extChartAt I α (γ t)) t₀ = v := by
    show deriv u t₀ = v
    exact hv.deriv
  -- Assemble.
  rw [covDerivAlongCurve, hcoordDeriv, hcoord₀, hchartVel]
  -- `extChartAt I α (γ t₀) = u t₀`, and `a + Γ(v,v)(u t₀) = 0`.
  have hbasept : extChartAt I α (γ t₀) = extChartAt I (γ t₀) (γ t₀) := rfl
  rw [hbasept, hgeoeq, map_zero]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **`D_t γ' = 0` for a geodesic (global).** A geodesic has vanishing
covariant acceleration at every time: `covDerivAlongCurve g γ (curveVelocity γ) t₀ = 0`
for all `t₀`. The differentiability of `γ` near each time is supplied by the caller,
as a global geodesic need not be `MDifferentiable` purely from the chart-local
second-order equation; in practice it is, and the hypothesis is then trivially met. -/
theorem IsGeodesic.covDerivAlongCurve_curveVelocity_eq_zero
    {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : Geodesic.IsGeodesic (I := I) g γ)
    (hγdiff : ∀ t, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) (t₀ : ℝ) :
    covDerivAlongCurve (I := I) g γ (curveVelocity (I := I) γ) t₀ = 0 :=
  Riemannian.covDerivAlongCurve_curveVelocity_eq_zero g γ t₀ (hγ t₀)
    (Filter.Eventually.of_forall hγdiff)

/-- **Math.** **Constant speed of a geodesic.** A geodesic has constant speed: the
derivative of its squared speed vanishes, `d/dt ⟨γ', γ'⟩_g = 0`. This is the
immediate composition of the metric-compatibility of `D_t`
(`covDerivAlongCurve_metricInner`, with `V = W = γ'`) and `D_t γ' = 0`
(`covDerivAlongCurve_curveVelocity_eq_zero`):
`d/dt⟨γ',γ'⟩ = ⟨D_tγ', γ'⟩ + ⟨γ', D_tγ'⟩ = ⟨0, γ'⟩ + ⟨γ', 0⟩ = 0`. -/
theorem covDerivAlongCurve_curveVelocity_metricInner_deriv_eq_zero
    [ModelWithCorners.Boundaryless I]
    (g : RiemannianMetric I M) (γ : ℝ → M) (t₀ : ℝ)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t₀)
    (hVc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (curveVelocity (I := I) γ t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγdiff : ∀ᶠ t in 𝓝 t₀, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (fun t => g.metricInner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t)) t₀ = 0 := by
  have hγcont : ContinuousAt γ t₀ := (hγdiff.self_of_nhds).continuousAt
  rw [covDerivAlongCurve_metricInner g γ (curveVelocity (I := I) γ)
        (curveVelocity (I := I) γ) t₀ hVc hVc hγc hγcont,
      covDerivAlongCurve_curveVelocity_eq_zero g γ t₀ hgeo hγdiff,
      g.metricInner_zero_left, g.metricInner_zero_right, add_zero]

end Riemannian
