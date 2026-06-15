import OpenGALib.Riemannian.Connection.ParallelTransportBridge

/-!
# Parallel transport moving-foot bridge: chart-transition of the fibre coordinate

The covariant derivative `covDerivAlongCurve g γ V t₀` is computed in the chart
centred at the *moving foot* `γ t₀`. A solution of the parallel-transport ODE
produced by `exists_parallelTransport_coord` lives in a *fixed* chart `α`. To
bridge the two we must relate the moving-chart fibre coordinate
`(trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)` to
the fixed-chart-`α` fibre coordinate.

The mechanism is the tangent-bundle coordinate change `tangentCoordChange`. By
`TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`, the trivialization
coordinate *is* a value of `tangentCoordChange`; the cocycle identity
`tangentCoordChange_comp` then expresses the moving-chart coordinate as the
chart-`α`-to-chart-`γ(t₀)` transition applied to the fixed-chart coordinate.

This is the **base-bundle** half of the moving-foot bridge — the analogue, on
`TangentBundle I M` itself, of the `T(TM)` lemma
`tangentCoordChange_tangent_eq_triv` used in the geodesic layer. It does **not**
yet differentiate the transition (that is the genuine Christoffel-transformation
step, handled by lifting to `T(TM)` so the bundle chain rule packages it).

## Main results

* `continuousLinearMapAt_eq_tangentCoordChange` — the trivialization fibre
  coordinate at `β` equals `tangentCoordChange I x β x`.
* `movingCoord_eq_tangentCoordChange_fixed` — the chart-`β` fibre coordinate is
  the chart-`α`-to-`β` transition applied to the chart-`α` fibre coordinate.
-/

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Trivialization fibre coordinate as a tangent coordinate change.**
On the base set of the trivialization at `β` (i.e. `x ∈ (chartAt H β).source`),
the trivialization's `continuousLinearMapAt ℝ x` coincides with the
tangent-bundle coordinate change `tangentCoordChange I x β x` (from the achart at
`x` to the achart at `β`, evaluated at `x`). This is the base-bundle analogue of
the `T(TM)` identity `tangentCoordChange_tangent_eq_triv`; it is the entry point
that turns trivialization coordinates into the cocycle calculus of
`tangentCoordChange`. -/
theorem continuousLinearMapAt_eq_tangentCoordChange (β : M) {x : M}
    (hx : x ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ x v
      = tangentCoordChange I x β x v := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (I := I) hx]
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Moving-foot transition of the fibre coordinate.** For `x` in the
chart sources of both `α` and `β`, the chart-`β` fibre coordinate of a tangent
vector is the chart-`α`-to-`β` transition `tangentCoordChange I α β x` applied to
its chart-`α` fibre coordinate:
`φ_β(x)·v = tangentCoordChange I α β x (φ_α(x)·v)`.
Both coordinates are rewritten as `tangentCoordChange` values via
`continuousLinearMapAt_eq_tangentCoordChange`, and the cocycle identity
`tangentCoordChange_comp` (with `w = x`, intermediate chart `α`, target `β`)
collapses the composite. This is the pointwise transition law that the
moving-foot bridge differentiates. -/
theorem movingCoord_eq_tangentCoordChange_fixed (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) (v : E) :
    (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ x v
      = tangentCoordChange I α β x
          ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt ℝ x v) := by
  rw [continuousLinearMapAt_eq_tangentCoordChange (I := I) β hxβ,
    continuousLinearMapAt_eq_tangentCoordChange (I := I) α hxα]
  -- The cocycle identity `tangentCoordChange_comp` collapses the composite.
  exact (tangentCoordChange_comp (I := I) (w := x) (x := α) (y := β) (z := x)
    (v := v) (by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact mem_extChartAt_source (I := I) x
      · rw [extChartAt_source]; exact hxα
      · rw [extChartAt_source]; exact hxβ)).symm

end Riemannian
