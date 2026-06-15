import OpenGALib.Riemannian.Connection.CovariantDerivativeAlongCurve

/-!
# Parallel transport bridge: coordinate characterization of `D_t V = 0`

The covariant derivative `covDerivAlongCurve g γ V t₀` is, by definition, the
trivialization-inverse `symmL` applied to an `E`-valued *inner expression* — the
chart-coordinate time-derivative `vCoordDeriv` of `V` plus the Christoffel
`correction`. Since `symmL` is a left inverse of `continuousLinearMapAt` on the
trivialization base set, it is injective there; hence `D_t V = 0` is equivalent to
the vanishing of the inner expression.

This file records that equivalence as two lemmas. It is the "coordinate
characterization" entry point of the parallel-transport moving-foot bridge: the
forward direction (`covDerivAlongCurve_eq_zero_of_coord`) is what *builds* parallel
transport from a solution of the chart-coordinate ODE, and the `iff`
(`covDerivAlongCurve_eq_zero_iff_coord`) is the full characterization. The hard
chart-transition step is separate and not in scope here.

## Main results

* `covDerivAlongCurve_eq_zero_of_coord` — if the inner sum vanishes then `D_t V = 0`.
* `covDerivAlongCurve_eq_zero_iff_coord` — `D_t V = 0 ↔` the inner sum vanishes.
-/

open Bundle
open scoped Manifold ContDiff
open Riemannian.Tensor

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **`symmL`-injectivity at the base point.** The trivialization-inverse
`symmL ℝ b` is a left inverse of `continuousLinearMapAt ℝ b` on the base set, so it
is injective there: if `T.symmL ℝ b x = 0` then `x = 0`. Proved by applying the
left inverse `continuousLinearMapAt` to both sides. -/
theorem symmL_eq_zero_imp {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) b).baseSet)
    {x : E} (hx : (trivializationAt E (TangentSpace I) b).symmL ℝ b x = 0) :
    x = 0 := by
  set T := trivializationAt E (TangentSpace I) b with hT
  calc x = T.continuousLinearMapAt ℝ b (T.symmL ℝ b x) :=
        (T.continuousLinearMapAt_symmL hb x).symm
    _ = T.continuousLinearMapAt ℝ b 0 := by rw [hx]
    _ = 0 := map_zero _

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Coordinate sufficient condition for `D_t V = 0` (the
parallel-transport builder).** If the chart-coordinate time-derivative of `V`
cancels the Christoffel correction — `vCoordDeriv + correction = 0`, i.e.
`vCoordDeriv = -correction` — then the covariant derivative of `V` along `γ`
vanishes at `t₀`. This is the direction used to *build* parallel transport from a
solution of the chart-coordinate linear ODE: the inner `E`-expression in the
definition of `covDerivAlongCurve` is exactly `vCoordDeriv + correction`, and
`symmL` sends `0` to `0`. Mirrors the final assembly of
`covDerivAlongCurve_curveVelocity_eq_zero`. -/
theorem covDerivAlongCurve_eq_zero_of_coord (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hcoord :
      deriv (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
          (γ t) (V t)) t₀
        + Geodesic.chartChristoffelContraction (I := I) g (γ t₀)
            (deriv (fun t => extChartAt I (γ t₀) (γ t)) t₀)
            ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀))
            (extChartAt I (γ t₀) (γ t₀)) = 0) :
    covDerivAlongCurve (I := I) g γ V t₀ = 0 := by
  rw [covDerivAlongCurve, hcoord, map_zero]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Coordinate characterization of `D_t V = 0`.** The covariant
derivative of `V` along `γ` vanishes at `t₀` **iff** its chart-coordinate
time-derivative cancels the Christoffel correction, `vCoordDeriv + correction = 0`.
The `←` direction is `covDerivAlongCurve_eq_zero_of_coord`; the `→` direction uses
`symmL`-injectivity at the base point (`symmL_eq_zero_imp`, via the left inverse
`continuousLinearMapAt_symmL`) to strip the trivialization-inverse from the
definition of `covDerivAlongCurve`. This is the coordinate-ODE characterization
underlying the parallel-transport moving-foot bridge. -/
theorem covDerivAlongCurve_eq_zero_iff_coord (g : RiemannianMetric I M) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ) :
    covDerivAlongCurve (I := I) g γ V t₀ = 0 ↔
      deriv (fun t => (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ
          (γ t) (V t)) t₀
        + Geodesic.chartChristoffelContraction (I := I) g (γ t₀)
            (deriv (fun t => extChartAt I (γ t₀) (γ t)) t₀)
            ((trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (V t₀))
            (extChartAt I (γ t₀) (γ t₀)) = 0 := by
  have hbase : γ t₀ ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet :=
    mem_chart_source H (γ t₀)
  constructor
  · intro h
    rw [covDerivAlongCurve] at h
    exact symmL_eq_zero_imp (I := I) hbase h
  · exact covDerivAlongCurve_eq_zero_of_coord g γ V t₀

end Riemannian
