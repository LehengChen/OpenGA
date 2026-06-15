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

/-- **Eng.** `ofReal ∘ ρ α` vanishes off `source α`, since the partition of unity
is subordinate to the chart-source family. -/
private theorem ofReal_pou_eq_zero_of_not_mem
    (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate fun x => (chartAt H x).source)
    (α : M) {x : M} (hx : x ∉ (chartAt H α).source) :
    ENNReal.ofReal (ρ α x) = 0 := by
  have hx0 : ρ α x = 0 := by
    by_contra h
    exact hx (hρ α (subset_tsupport (ρ α) (Function.mem_support.mpr h)))
  rw [hx0, ENNReal.ofReal_zero]

/-- **Eng.** Measurability of `x ↦ ofReal (ρ α x)`. -/
private theorem measurable_ofReal_pou
    (ρ : SmoothPartitionOfUnity M I M univ) (α : M) :
    Measurable (fun x : M => ENNReal.ofReal (ρ α x)) :=
  ENNReal.measurable_ofReal.comp (map_continuous (ρ.toFun α)).measurable

/-- **Math.** Per-summand chart swap: the integral of `ρ α` against the
chart-local measure at `α` over a measurable `A ⊆ source β` equals the same
integral against the chart-local measure at `β`. The integrand is supported in
`source α`, hence (as `A ⊆ source β`) in the overlap `source α ∩ source β`,
where the two chart-local measures agree. -/
private theorem setLIntegral_chartLocalMeasure_swap
    (g : RiemannianMetric I M) (ρ : SmoothPartitionOfUnity M I M univ)
    (hρ : ρ.IsSubordinate fun x => (chartAt H x).source)
    (α β : M) {A : Set M} (hA : MeasurableSet A)
    (hAsub : A ⊆ (chartAt H β).source) :
    ∫⁻ x in A, ENNReal.ofReal (ρ α x) ∂(chartLocalMeasure (I := I) g α)
      = ∫⁻ x in A, ENNReal.ofReal (ρ α x) ∂(chartLocalMeasure (I := I) g β) := by
  set f : M → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ α x) with hf
  set W : Set M := (chartAt H α).source ∩ (chartAt H β).source with hW
  have hWmeas : MeasurableSet W :=
    ((chartAt H α).open_source.inter (chartAt H β).open_source).measurableSet
  have hAWmeas : MeasurableSet (A ∩ W) := hA.inter hWmeas
  -- `A.indicator f = (A ∩ W).indicator f` (off `W`, within `A ⊆ source β`, `f = 0`).
  have hind : A.indicator f = (A ∩ W).indicator f := by
    funext x
    by_cases hxA : x ∈ A
    · by_cases hxW : x ∈ W
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem (Set.mem_inter hxA hxW)]
      · rw [Set.indicator_of_mem hxA, Set.indicator_of_notMem (fun h => hxW h.2)]
        have hxnα : x ∉ (chartAt H α).source := fun hxα => hxW ⟨hxα, hAsub hxA⟩
        exact ofReal_pou_eq_zero_of_not_mem ρ hρ α hxnα
    · rw [Set.indicator_of_notMem hxA, Set.indicator_of_notMem (fun h => hxA h.1)]
  -- Reduce both sides to a set-lintegral over `A ∩ W`.
  have hreduce : ∀ μ : Measure M,
      ∫⁻ x in A, f x ∂μ = ∫⁻ x in (A ∩ W), f x ∂μ := by
    intro μ
    rw [← lintegral_indicator hA, ← lintegral_indicator hAWmeas, hind]
  rw [hreduce, hreduce]
  -- On `A ∩ W ⊆ W` the two chart-local measures agree.
  have hsub : A ∩ W ⊆ W := Set.inter_subset_right
  rw [show ∫⁻ x in (A ∩ W), f x ∂(chartLocalMeasure (I := I) g α)
        = ∫⁻ x in (A ∩ W), f x ∂((chartLocalMeasure (I := I) g α).restrict W) by
      rw [Measure.restrict_restrict_of_subset hsub],
    show ∫⁻ x in (A ∩ W), f x ∂(chartLocalMeasure (I := I) g β)
        = ∫⁻ x in (A ∩ W), f x ∂((chartLocalMeasure (I := I) g β).restrict W) by
      rw [Measure.restrict_restrict_of_subset hsub],
    chartLocalMeasure_restrict_overlap_eq (I := I) g α β]

/-- **Math.** **Chart-pullback formula.** On any chart, the global Riemannian
volume measure equals the chart-local measure: for measurable `A ⊆ source β`,
`volumeMeasure g A = chartLocalMeasure g β A`. This is the keystone characterizing
`vol_g` as the chart-pullback of `√det(g) · Lebesgue`. -/
theorem volumeMeasure_eq_chartLocalMeasure
    (g : RiemannianMetric I M) (β : M) {A : Set M}
    (hA : MeasurableSet A) (hAsub : A ⊆ (chartAt H β).source) :
    volumeMeasure g A = chartLocalMeasure (I := I) g β A := by
  set ρ : SmoothPartitionOfUnity M I M univ := chartAtlasPOU I M with hρ_def
  have hρ : ρ.IsSubordinate fun x => (chartAt H x).source := chartAtlasPOU_isSubordinate I M
  -- `vol = Measure.sum_α (chartLocalMeasure α).withDensity (ρ α)`; each term swaps to `β`.
  rw [volumeMeasure, ← hρ_def, riemannianMeasure_def, Measure.sum_apply _ hA]
  have hsummand : ∀ α : M,
      ((chartLocalMeasure (I := I) g α).withDensity
          (fun x => ENNReal.ofReal (ρ α x))) A
        = ∫⁻ x in A, ENNReal.ofReal (ρ α x) ∂(chartLocalMeasure (I := I) g β) := by
    intro α
    rw [withDensity_apply _ hA, setLIntegral_chartLocalMeasure_swap g ρ hρ α β hA hAsub]
  simp_rw [hsummand]
  -- `∑'_α ρ α x = 1` pointwise.
  have hsum_one : ∀ x : M, ∑' α : M, ENNReal.ofReal (ρ α x) = 1 := by
    intro x
    have hfin : (Function.support fun α : M => ρ α x).Finite :=
      ρ.locallyFinite.point_finite x
    rw [tsum_eq_sum (s := hfin.toFinset) (fun α hα => by
      have : ρ α x = 0 := by
        by_contra h; exact hα (hfin.mem_toFinset.mpr (Function.mem_support.mpr h))
      rw [this, ENNReal.ofReal_zero])]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => ρ.nonneg α x)]
    have hone : ∑ α ∈ hfin.toFinset, ρ α x = 1 := by
      rw [← finsum_eq_sum _ hfin]; exact ρ.sum_eq_one (mem_univ x)
    rw [hone, ENNReal.ofReal_one]
  -- The set of indices with nonempty support is countable (σ-compact + locally finite).
  set S : Set M := {α : M | (Function.support (ρ α)).Nonempty} with hS_def
  have hScount : S.Countable := by
    have hlf : LocallyFinite
        (fun α : S => Function.support (ρ (α : M))) :=
      ρ.locallyFinite.comp_injective Subtype.val_injective
    have huniv : (Set.univ : Set S).Countable := hlf.countable_univ (fun α => α.2)
    rw [Set.countable_univ_iff] at huniv
    exact Set.countable_coe_iff.mp huniv
  have : Countable S := hScount.to_subtype
  -- Off `S`, the summand integral vanishes; restrict the tsum to `S`.
  have hsupp_sub : (Function.support fun α : M =>
      ∫⁻ x in A, ENNReal.ofReal (ρ α x) ∂(chartLocalMeasure (I := I) g β)) ⊆ S := by
    intro α hα
    by_contra hαS
    apply hα
    have hz : ∀ x, ENNReal.ofReal (ρ α x) = 0 := by
      intro x; by_contra h
      exact hαS ⟨x, Function.mem_support.mpr (by
        intro hzero; exact h (by rw [hzero, ENNReal.ofReal_zero]))⟩
    simp_rw [hz]; exact lintegral_zero
  -- Restrict the (uncountable) tsum to the countable contributing set `S`.
  have hrestr : (∑' α : M, ∫⁻ x in A, ENNReal.ofReal (ρ α x)
        ∂(chartLocalMeasure (I := I) g β))
      = ∑' α : S, ∫⁻ x in A, ENNReal.ofReal (ρ (α : M) x)
        ∂(chartLocalMeasure (I := I) g β) :=
    (tsum_subtype_eq_of_support_subset hsupp_sub).symm
  rw [hrestr,
    ← lintegral_tsum (fun α : S => (measurable_ofReal_pou ρ (α : M)).aemeasurable)]
  -- Inner sum back to all of `M`, then `= 1`.
  have hinner : ∀ x, ∑' α : S, ENNReal.ofReal (ρ (α : M) x) = 1 := by
    intro x
    have hgs : (Function.support fun α : M => ENNReal.ofReal (ρ α x)) ⊆ S :=
      fun α hα => ⟨x, Function.mem_support.mpr (fun hzero =>
        hα (by simp only [hzero, ENNReal.ofReal_zero]))⟩
    exact (tsum_subtype_eq_of_support_subset hgs).trans (hsum_one x)
  simp_rw [hinner]
  rw [setLIntegral_one]

end Riemannian.Tensor
