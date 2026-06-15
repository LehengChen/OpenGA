import OpenGALib.Riemannian.Volume.ChartPullback
import OpenGALib.Riemannian.Volume.Util.ChartLocalIntegral

/-!
# Chart-pullback formula for the Riemannian volume measure

The keystone that unlocks the whole `Volume/` top layer: on any single chart
`(U_β, φ_β)`, the global `volumeMeasure g` agrees with the chart-local measure
`chartLocalMeasure g β` — i.e. `vol_g` IS the chart-pullback of
`√det(g) · Lebesgue`, glued consistently.

The proof unfolds `volumeMeasure = riemannianMeasure (chartAtlasPOU)
= Measure.sum_α (chartLocalMeasure g α).withDensity (ρ α)`, then for a
measurable `A ⊆ source β`:

* each summand `∫⁻_A ρ α d(chartLocalMeasure g α)` equals
  `∫⁻_A ρ α d(chartLocalMeasure g β)` because `ρ α` is supported in `source α`,
  so the integrand lives on the overlap `source α ∩ source β` where the two
  chart-local measures agree (`chartLocalMeasure_restrict_overlap_eq`, 0-sorry);
* summing over `α` and using `∑_α ρ α ≡ 1` collapses to
  `∫⁻_A 1 d(chartLocalMeasure g β) = chartLocalMeasure g β A`.

The sum-over-`M`/integral interchange restricts to the countable set of indices
with nonempty support (`LocallyFinite.countable_univ`, since `M` is σ-compact),
then applies `lintegral_tsum`.

Ground truth: do Carmo Ch.1; Lee Ch.16; this is the universal characterization
referenced by `UniversalProperty.volumeMeasure_unique`.
-/

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

/-- **Math.** **Chart-coordinate volume integral.** On an open `U ⊆ source p`, the
Riemannian volume of `U` is the chart-coordinate integral of the metric density
`√det(g)`:
`vol_g U = ∫_{φ(U)} √det(g ∘ φ⁻¹) dLeb`, where `φ = extChartAt I p`.
Combines the chart-pullback keystone with the chart-local measure's explicit
image integral. This is the measure-theoretic precursor of the exp-volume bridge:
once `φ` is replaced by exp-normal coordinates, the density becomes the volume
Jacobian `|det d exp_p|`. -/
theorem volumeMeasure_eq_setLIntegral_chartSqrtGramDet
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hUopen : IsOpen U) (hUsub : U ⊆ (chartAt H p).source) :
    volumeMeasure g U
      = ∫⁻ y in (extChartAt I p) '' U,
          ENNReal.ofReal (chartSqrtGramDet (I := I) g p ((extChartAt I p).symm y))
          ∂(modelHaar (E := E)) := by
  have key := chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I) g p hUopen hUsub
    (F := fun _ => (1 : ℝ≥0∞)) measurable_const hUopen.measurableSet
  rw [volumeMeasure_eq_chartLocalMeasure g p hUopen.measurableSet hUsub,
    ← setLIntegral_one U, key]
  simp

end Riemannian.Tensor
