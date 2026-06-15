import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import OpenGALib.Riemannian.Metric.RiemannianMetric
import OpenGALib.Riemannian.Volume.Util.PartitionOfUnityGlue
import OpenGALib.Riemannian.Volume.Util.ChartLocalIntegral

/-!
# Riemannian volume measure — chart-pullback definition

Anchor for the canonical Riemannian volume measure `vol_g` on a Riemannian
manifold `(M, g)`. Definition is chart-wise:

  `vol_g(A) = ∫_{φ(A ∩ U)} √det(g_ij ∘ φ⁻¹)(y) dy`   for any chart `(U, φ)`,

glued by partition of unity. Chart-invariance follows from the
change-of-variables formula combined with the transformation
`g_ij ↦ Jᵀ · g_ij · J` (so `√det(g_ij)` transforms by `|det J⁻¹|`,
cancelling the Lebesgue Jacobian factor `|det J|`).

Sibling files in `Riemannian/Volume/` provide alternative-view bridges:
* `VolumeForm.lean`           — bridge `vol_g(A) = ∫_A dV_g` (top form view)
* `Hausdorff.lean`            — bridge `vol_g = α(n) · μH[n]_{d_g}`
                                (Federer §3.2.46; closes the BG stopgap)
* `Exponential.lean`          — bridge `vol_g|_{loc} = exp_{p,*}(det(d exp_p)·dx)`
* `UniversalProperty.lean`    — uniqueness characterization

Ground truth: do Carmo, *Riemannian Geometry*, Ch. 1; Petersen,
*Riemannian Geometry*, Ch. 7 §1; Lee, *Smooth Manifolds*, Ch. 16.

This file lands the **anchor signature** for Phase 1 of the
`riemannian-volume` Layer 3a sub-project. The actual chart-pullback
construction (partition-of-unity glue + chart-invariance proof) carries
PRE-PAPER sorries with full repair plans below; subsequent commits in
this branch fill them in.
-/

open scoped ContDiff Manifold ENNReal

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

/-- **Math.** The **Riemannian volume measure** `vol_g` on a Riemannian
manifold `(M, g)`. Defined chart-wise as the pullback of Lebesgue measure
weighted by `√det(g_ij)`, glued across charts by partition of unity.

Ground truth: do Carmo Ch.1; Petersen Ch.7 §1; Lee Ch.16.

PRE-PAPER. **Construction sketch** (to be filled in subsequent commits):

1. *Local chart-wise measure.* For each chart `(U, φ)` containing
   `x ∈ M`, define `vol_g^{U,φ}` on `U` as the pushforward under `φ⁻¹` of
   `√det(g_ij ∘ φ⁻¹) · (Lebesgue|_{φ(U)})`. Here `g_ij(x) = g(∂_i|_x, ∂_j|_x)`
   for the chart-frame `∂_i = (φ⁻¹)_*(e_i)`.
2. *Chart-invariance.* Under chart change `(U, φ) → (V, ψ)` with transition
   `ψ ∘ φ⁻¹`, the matrix `g_ij` transforms by `g' = Jᵀ · g · J` where
   `J = d(φ ∘ ψ⁻¹)`. So `√det(g') = |det J| · √det(g)`. Combined with
   Lebesgue's change of variables giving a factor `|det J|⁻¹` (pulling
   back), the chart-wise measures **agree** on `U ∩ V`.
3. *Global glue.* Use a smooth partition of unity `{χ_i}` subordinate to
   a locally finite atlas `{(U_i, φ_i)}`: define
   `vol_g(A) := Σᵢ ∫ χᵢ d(vol_g^{Uᵢ,φᵢ})`. Chart-invariance (step 2)
   ensures the sum is independent of the choice of atlas / partition.

**Implementation.** Steps 1-3 land in `Riemannian/Volume/Util/`:
* `chartLocalMeasure g α` (step 1, per-chart pushforward of
  `√det · Lebesgue`),
* `chartLocalMeasure_lintegral_U_eq_of_overlap` (step 2, chart-overlap
  invariance via change of variables),
* `riemannianMeasure g ρ` (step 3, partition-of-unity sum).

The canonical volume measure picks the canonical chart-atlas partition
of unity `chartAtlasPOU I M`. -/
noncomputable def volumeMeasure (g : RiemannianMetric I M) : MeasureTheory.Measure M :=
  Riemannian.Tensor.riemannianMeasure g (Riemannian.Tensor.chartAtlasPOU I M)

@[inherit_doc] scoped[Riemannian]
  notation:max "dV_g[" g "]" => Riemannian.volumeMeasure g


section ChartPullbackFormula

open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace Tensor

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

end Tensor

end ChartPullbackFormula


variable (g : RiemannianMetric I M)

/-- **Math.** `vol_g` is locally finite (every point has a neighborhood of
finite measure). Standard property — every Riemannian metric ball of
finite radius has finite volume since the chart-pullback integrand
`√det(g_ij ∘ φ⁻¹)` is bounded on compact sets.

PRE-PAPER (Phase 1 follow-up). **Repair plan**: take a chart-relative
compact neighborhood, apply the chart-pullback formula
(forthcoming `volumeMeasure_chart_pullback_eq`), bound `√det` by its sup
on the compact image. -/
instance instIsLocallyFiniteMeasure_volumeMeasure :
    MeasureTheory.IsLocallyFiniteMeasure (volumeMeasure g) := by
  classical
  -- File-local Borel structure on the model space `E`, matching the one baked into
  -- `modelHaar` / `chartLocalMeasure` (where it is a `private local instance`).
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  -- `M` is locally compact: finite-dimensional (hence locally compact) model `E`,
  -- boundaryless model-with-corners `I` ⟹ `H` locally compact ⟹ `M` locally compact.
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  refine ⟨fun x => ?_⟩
  -- Pick a compact `K` with `x ∈ interior K ⊆ K ⊆ source`; use the open `V := interior K`.
  obtain ⟨K, hKcompact, hxK, hKsub⟩ :=
    exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)
  set V : Set M := interior K with hV
  have hVopen : IsOpen V := isOpen_interior
  have hVsubK : V ⊆ K := interior_subset
  have hVsub : V ⊆ (chartAt H x).source := hVsubK.trans hKsub
  refine ⟨V, hVopen.mem_nhds hxK, ?_⟩
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  -- **Chart-pullback (local form).** On `V ⊆ source x`, `vol_g V = chartLocalMeasure g x V`,
  -- directly from the in-file keystone `volumeMeasure_eq_chartLocalMeasure`.
  rw [Riemannian.Tensor.volumeMeasure_eq_chartLocalMeasure g x hVmeas hVsub]
  -- `chartLocalMeasure g x V = ∫⁻_{φ(V)} ofReal(√det(g ∘ φ⁻¹)) dLeb`, `φ = extChartAt I x`.
  rw [← MeasureTheory.setLIntegral_one V,
    Riemannian.Tensor.chartLocalMeasure_lintegral_U_eq_setLIntegral_image (I := I)
      g x hVopen hVsub (F := fun _ => (1 : ℝ≥0∞)) measurable_const hVmeas]
  simp only [mul_one]
  -- `√det(g)` is continuous on the source, hence bounded above on the compact `K`.
  have hKsub' : K ⊆ (chartAt H x).source := hKsub
  have hcontOn : ContinuousOn (Riemannian.Tensor.chartSqrtGramDet (I := I) g x)
      (chartAt H x).source :=
    Riemannian.Tensor.chartSqrtGramDet_continuousOn_source (I := I) g x
  obtain ⟨C, hC⟩ : BddAbove
      (Riemannian.Tensor.chartSqrtGramDet (I := I) g x '' K) :=
    hKcompact.bddAbove_image (hcontOn.mono hKsub')
  -- `extChartAt I x '' K` is compact in `E`, so it has finite `modelHaar`.
  have hKEcompact : IsCompact (extChartAt I x '' K) :=
    hKcompact.image_of_continuousOn ((continuousOn_extChartAt x).mono (by
      rw [extChartAt_source]; exact hKsub'))
  have hVimg_meas : MeasurableSet (extChartAt I x '' V) :=
    Riemannian.Tensor.extChartAt_image_measurableSet_of_open_subset_source x hVopen hVsub
  -- Pointwise bound on `φ(V)`: `symm y ∈ V ⊆ K`, so `ofReal(√det(symm y)) ≤ ofReal C`.
  have hbound : ∀ y ∈ extChartAt I x '' V,
      ENNReal.ofReal
          (Riemannian.Tensor.chartSqrtGramDet (I := I) g x ((extChartAt I x).symm y))
        ≤ ENNReal.ofReal C := by
    rintro y ⟨z, hzV, rfl⟩
    have hzsource : z ∈ (extChartAt I x).source := by
      rw [extChartAt_source]; exact hVsub hzV
    rw [(extChartAt I x).left_inv hzsource]
    exact ENNReal.ofReal_le_ofReal (hC ⟨z, hVsubK hzV, rfl⟩)
  -- Bound the lintegral by `ofReal C · modelHaar(φ(V)) < ⊤`.
  calc
    ∫⁻ y in extChartAt I x '' V,
        ENNReal.ofReal
          (Riemannian.Tensor.chartSqrtGramDet (I := I) g x ((extChartAt I x).symm y))
          ∂(Riemannian.Tensor.modelHaar (E := E))
        ≤ ∫⁻ _ in extChartAt I x '' V, ENNReal.ofReal C
          ∂(Riemannian.Tensor.modelHaar (E := E)) :=
        MeasureTheory.setLIntegral_mono' hVimg_meas hbound
    _ = ENNReal.ofReal C * Riemannian.Tensor.modelHaar (E := E) (extChartAt I x '' V) :=
        MeasureTheory.setLIntegral_const _ _
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        exact lt_of_le_of_lt
          (MeasureTheory.measure_mono (Set.image_mono hVsubK)) hKEcompact.measure_lt_top

/-- **Math.** `vol_g` is sigma-finite (M is sigma-compact, vol_g is locally
finite, hence sigma-finite).

PRE-PAPER (Phase 1 follow-up). **Repair plan**: follows from
`isLocallyFinite + sigma_compact ⟹ sigma_finite` (Mathlib lemma). -/
instance instSigmaFinite_volumeMeasure :
    MeasureTheory.SigmaFinite (volumeMeasure g) := by
  infer_instance

end Riemannian
