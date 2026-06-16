import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Covering.Basic
import OpenGALib.Manifold.Covering.SmoothCoveringMap
import OpenGALib.Manifold.Covering.LocalSection

/-!
# Lifted smooth structure of a topological covering

A topological covering map over a smooth base carries to its total space a
*canonical* smooth structure, the unique one making the projection a smooth
covering map. The development is layered so each result is stated at the
weakest input it needs:

1. **Canonical lifted atlas** — `liftedCoveringChart` pulls each base chart
   back along a chosen local inverse branch of the covering projection; these
   charts assemble into `liftedCoveringChartedSpace`. Their transition maps are
   restrictions of base-chart transitions, so the atlas is automatically
   `C^∞`-compatible (`liftedCoveringChartedSpace_isManifold`). This layer needs
   only a topological covering map over a smooth base.
2. **Projection branches** — `liftedProjectionBranch` reads the projection in
   the lifted coordinates, where it is the identity; this packages it as a
   manifold `PartialDiffeomorph` and exhibits `π` as a smooth covering map for
   the canonical structure.
3. **Comparison layer** — in *any* smooth covering structure on the total
   space, the canonical lifted charts already lie in the maximal atlas (their
   local inverse branches are smooth local sections). Inserting a lifted chart
   at each overlap point shows any two such structures share one maximal atlas,
   giving uniqueness.

The base model `I` is arbitrary; Lee's boundaryless `ℝⁿ` formulation is the
specialization `I = 𝓡 n`, and the connectedness hypothesis is unnecessary for
either existence or uniqueness.

## Main definitions

* `Manifold.liftedCoveringChart` — the canonical lifted chart through a point,
  a base chart pulled back along a local inverse branch.
* `Manifold.liftedProjectionBranch` — the canonical local branch of the
  covering projection in lifted coordinates.
* `Manifold.liftedCoveringChartedSpace` — the canonical charted-space structure
  on the total space assembled from the lifted charts.

## Main results

* `Manifold.liftedCoveringChartedSpace_isManifold` — the canonical lifted atlas
  is `C^∞`-compatible.
* `Manifold.exists_smooth_covering_structure` — a surjective topological
  covering map over a smooth manifold admits a smooth structure making it a
  smooth covering map.
* `Manifold.smooth_covering_same_smooth_structure` — any two smooth covering
  structures on the total space have the same maximal smooth atlas.
* `Manifold.exists_unique_smooth_covering_structure` — existence together with
  uniqueness up to the canonical maximal atlas.

Provenance: SmoothManifoldsLee a5f308c — Proposition_4_40.
-/

open scoped Manifold ContDiff
open Manifold

universe u𝕜 uE uH uM uE'

noncomputable section

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I ∞ M]
variable {M' : Type uE'} [TopologicalSpace M'] (π : M' → M)

namespace Manifold

section LocalInverse

variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] {f : X → Y}

/-- **Math.** A chosen local homeomorphism witnessing that `f` is a local
homeomorphism near `x`: a partial homeomorphism agreeing with `f` whose source
contains `x`. -/
noncomputable def localHomeomorphAt (hf : IsLocalHomeomorph f) (x : X) :
    OpenPartialHomeomorph X Y :=
  Classical.choose (hf x)

/-- **Math.** The chosen local homeomorphism near `x` contains `x` in its
source. -/
@[simp] theorem mem_localHomeomorphAt_source (hf : IsLocalHomeomorph f) (x : X) :
    x ∈ (localHomeomorphAt (f := f) hf x).source :=
  (Classical.choose_spec (hf x)).1

/-- **Math.** The chosen local homeomorphism near `x` agrees with `f`
everywhere. -/
@[simp] theorem localHomeomorphAt_apply (hf : IsLocalHomeomorph f) (x z : X) :
    (localHomeomorphAt (f := f) hf x) z = f z :=
  (congrFun (Classical.choose_spec (hf x)).2 z).symm

/-- **Math.** A chosen local inverse branch of a local homeomorphism `f` through a
point `x`: the inverse of the chosen local homeomorphism near `x`, viewed as a
partial homeomorphism from the codomain back to the domain. -/
noncomputable def coveringLocalInverseAt (hf : IsLocalHomeomorph f) (x : X) :
    OpenPartialHomeomorph Y X :=
  (localHomeomorphAt (f := f) hf x).symm

/-- **Math.** The inverse of the chosen local inverse branch through `x` is the
chosen local homeomorphism near `x`. -/
@[simp] theorem coveringLocalInverseAt_symm (hf : IsLocalHomeomorph f) (x : X) :
    (coveringLocalInverseAt (f := f) hf x).symm = localHomeomorphAt (f := f) hf x := by
  simp [coveringLocalInverseAt]

/-- **Math.** The source of the chosen local inverse branch through `x` is the
image of the chosen local homeomorphism near `x`. -/
@[simp] theorem coveringLocalInverseAt_source (hf : IsLocalHomeomorph f) (x : X) :
    (coveringLocalInverseAt (f := f) hf x).source = (localHomeomorphAt (f := f) hf x).target :=
  rfl

/-- **Math.** The target of the chosen local inverse branch through `x` is the
source of the chosen local homeomorphism near `x`. -/
@[simp] theorem coveringLocalInverseAt_target (hf : IsLocalHomeomorph f) (x : X) :
    (coveringLocalInverseAt (f := f) hf x).target = (localHomeomorphAt (f := f) hf x).source :=
  rfl

/-- **Math.** The chosen local inverse branch through `x`, read as a function, is
the inverse of the chosen local homeomorphism near `x`. -/
@[simp] theorem coveringLocalInverseAt_apply (hf : IsLocalHomeomorph f) (x : X) (y : Y) :
    (coveringLocalInverseAt (f := f) hf x) y = (localHomeomorphAt (f := f) hf x).symm y :=
  rfl

/-- **Math.** The chosen local inverse branch through `x` is a genuine right
inverse of `f`: composing `f` with it returns the input on its source. -/
theorem apply_coveringLocalInverseAt_of_mem (hf : IsLocalHomeomorph f) (x : X) {y : Y}
    (hy : y ∈ (coveringLocalInverseAt (f := f) hf x).source) :
    f (coveringLocalInverseAt (f := f) hf x y) = y := by
  have hy' : y ∈ (localHomeomorphAt (f := f) hf x).target := hy
  show f ((localHomeomorphAt (f := f) hf x).symm y) = y
  rw [← localHomeomorphAt_apply (f := f) hf x]
  exact (localHomeomorphAt (f := f) hf x).right_inv hy'

end LocalInverse

/-- **Math.** The canonical lifted chart through `p` is the base chart at `π p`
pulled back along the local inverse branch of the covering projection through
`p`. -/
noncomputable def liftedCoveringChart
    (hπ : IsCoveringMap π) (p : M') : OpenPartialHomeomorph M' H :=
  (coveringLocalInverseAt hπ.isLocalHomeomorph p).symm.trans (chartAt H (π p))

/-- **Math.** The canonical local branch of the covering projection through `p`
is the lifted chart composed with the inverse of the base chart at `π p`. -/
noncomputable def liftedProjectionBranch
    (hπ : IsCoveringMap π) (p : M') : OpenPartialHomeomorph M' M :=
  (liftedCoveringChart (H := H) π hπ p).trans (chartAt H (π p)).symm

/-- **Math.** The canonical lifted chart through `p` contains `p` in its source. -/
theorem mem_liftedCoveringChart_source
    (hπ : IsCoveringMap π) (p : M') :
    p ∈ (liftedCoveringChart (H := H) π hπ p).source := by
  simp [liftedCoveringChart]

/-- **Math.** The canonical lifted charts assemble into a charted-space structure
on the covering space. -/
@[implicit_reducible]
noncomputable def liftedCoveringChartedSpace
    (hπ : IsCoveringMap π) : ChartedSpace H M' where
  atlas := Set.range (liftedCoveringChart (H := H) π hπ)
  chartAt := liftedCoveringChart (H := H) π hπ
  mem_chart_source := mem_liftedCoveringChart_source (H := H) π hπ
  chart_mem_atlas p := ⟨p, rfl⟩

/-- **Math.** The source of a lifted-chart transition is contained in the source
of the corresponding base-chart transition. -/
theorem liftedCoveringChart_transition_source_subset
    (hπ : IsCoveringMap π) (p q : M') :
    ((liftedCoveringChart (H := H) π hπ p).symm.trans
      (liftedCoveringChart (H := H) π hπ q)).source ⊆
      ((chartAt H (π p)).symm.trans (chartAt H (π q))).source := by
  intro x hx
  have hx' := hx
  simp only [liftedCoveringChart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
    PartialEquiv.symm_source, OpenPartialHomeomorph.coe_coe_symm, Set.mem_inter_iff,
    Set.mem_preimage] at hx'
  rcases hx' with ⟨⟨hx_chart, hx_lp_source⟩, -, hx_qsource⟩
  refine ⟨hx_chart, ?_⟩
  have h_apply :
      π ((localHomeomorphAt hπ.isLocalHomeomorph p).symm ((chartAt H (π p)).symm x)) =
        (chartAt H (π p)).symm x := by
    exact apply_coveringLocalInverseAt_of_mem hπ.isLocalHomeomorph p hx_lp_source
  simpa [h_apply] using hx_qsource

/-- **Math.** On the source of the transition between two lifted charts, the
transition map equals the corresponding base-chart transition map. -/
theorem liftedCoveringChart_transition_eqOn
    (hπ : IsCoveringMap π) (p q : M') :
    Set.EqOn
      (((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q)) :
          H → H)
      (((chartAt H (π p)).symm.trans (chartAt H (π q))) : H → H)
      ((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q)).source := by
  intro x hx
  have hx' := hx
  simp only [liftedCoveringChart, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
    PartialEquiv.symm_source, OpenPartialHomeomorph.coe_coe_symm, Set.mem_inter_iff,
    Set.mem_preimage] at hx'
  rcases hx' with ⟨⟨-, hx_lp_source⟩, -, -⟩
  have h_apply :
      π ((localHomeomorphAt hπ.isLocalHomeomorph p).symm ((chartAt H (π p)).symm x)) =
        (chartAt H (π p)).symm x := by
    exact apply_coveringLocalInverseAt_of_mem hπ.isLocalHomeomorph p hx_lp_source
  simpa [liftedCoveringChart, h_apply]

/-- **Math.** The transition between two lifted charts is equivalent on its source
to the restriction of the corresponding base-chart transition. -/
theorem liftedCoveringChart_transition_eqOnSource
    (hπ : IsCoveringMap π) (p q : M') :
    (OpenPartialHomeomorph.EqOnSource
      ((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q))
      (((chartAt H (π p)).symm.trans (chartAt H (π q))).restr
        ((liftedCoveringChart (H := H) π hπ p).symm.trans
          (liftedCoveringChart (H := H) π hπ q)).source)) := by
  constructor
  · rw [(((chartAt H (π p)).symm.trans (chartAt H (π q))).restr_source'
      ((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q)).source
      ((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q)).open_source)]
    exact (Set.inter_eq_right.mpr
      (liftedCoveringChart_transition_source_subset (H := H) π hπ p q)).symm
  · exact liftedCoveringChart_transition_eqOn π hπ p q

/-- **Math.** Every lifted-chart transition belongs to the smooth-structure
groupoid, being a restriction of a smooth base-chart transition. -/
theorem liftedCoveringChart_transition_mem_groupoid
    (hπ : IsCoveringMap π) (p q : M') :
    (liftedCoveringChart (H := H) π hπ p).symm.trans
      (liftedCoveringChart (H := H) π hπ q) ∈ contDiffGroupoid ∞ I := by
  have hbase :
      (chartAt H (π p)).symm.trans (chartAt H (π q)) ∈ contDiffGroupoid ∞ I := by
    exact IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π p))
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π q))
  have hrestr :
      ((chartAt H (π p)).symm.trans (chartAt H (π q))).restr
        ((liftedCoveringChart (H := H) π hπ p).symm.trans
          (liftedCoveringChart (H := H) π hπ q)).source ∈ contDiffGroupoid ∞ I := by
    exact closedUnderRestriction' hbase
      ((liftedCoveringChart (H := H) π hπ p).symm.trans
        (liftedCoveringChart (H := H) π hπ q)).open_source
  exact (contDiffGroupoid ∞ I).mem_of_eqOnSource hrestr
    (liftedCoveringChart_transition_eqOnSource (H := H) π hπ p q)

/-- **Math.** The canonical lifted charted-space structure is smooth: all of its
chart transitions are inherited from smooth base transitions. -/
theorem liftedCoveringChartedSpace_isManifold
    (hπ : IsCoveringMap π) :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    IsManifold I ∞ M' := by
  let cs : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  let hgroupoid :
      @HasGroupoid H _ M' _ cs (contDiffGroupoid ∞ I) :=
    { compatible := by
        intro e e' he he'
        rcases he with ⟨p, rfl⟩
        rcases he' with ⟨q, rfl⟩
        exact liftedCoveringChart_transition_mem_groupoid (I := I) (H := H) (π := π) hπ p q }
  let _ : HasGroupoid M' (contDiffGroupoid ∞ I) := hgroupoid
  exact IsManifold.mk' I ∞ M'

/-- **Math.** On the source of the canonical local branch through `p`, the covering
projection agrees with that branch. -/
theorem liftedProjectionBranch_eqOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    Set.EqOn π
      (liftedProjectionBranch (H := H) π hπ p)
      (liftedProjectionBranch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  change Set.EqOn π
    (liftedProjectionBranch (H := H) π hπ p)
    (liftedProjectionBranch (H := H) π hπ p).source
  intro x hx
  have hx_lifted : x ∈ (liftedCoveringChart (H := H) π hπ p).source := by
    simpa [liftedProjectionBranch] using hx.1
  have hx_chart : π x ∈ (chartAt H (π p)).source := by
    have hx_lifted' := hx_lifted
    simp [liftedCoveringChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hx_lifted'
    exact hx_lifted'.2
  simpa [liftedProjectionBranch, liftedCoveringChart] using
    ((chartAt H (π p)).left_inv hx_chart).symm

/-- **Math.** The marked point lies in the source of its canonical local branch to
the base manifold. -/
theorem mem_liftedProjectionBranch_source
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    p ∈ (liftedProjectionBranch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  simp [liftedProjectionBranch, liftedCoveringChart]

/-- **Math.** The canonical local branch of the covering projection is smooth in
the canonical lifted atlas, since its coordinate representative is the
identity. -/
theorem liftedProjectionBranch_contMDiffOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
    ContMDiffOn I I ∞
      (liftedProjectionBranch (H := H) π hπ p)
      (liftedProjectionBranch (H := H) π hπ p).source := by
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := liftedProjectionBranch (H := H) π hπ p
  have hs : e.source ⊆ (chartAt H p).source := by
    intro x hx
    simpa [e, liftedProjectionBranch]
      using hx.1
  have hmaps : Set.MapsTo e e.source (chartAt H (π p)).source := by
    intro x hx
    have hx_target : (liftedCoveringChart (H := H) π hπ p) x ∈ (chartAt H (π p)).target := by
      simpa [e, liftedProjectionBranch] using hx.2
    exact (chartAt H (π p)).symm_mapsTo hx_target
  have hs_ext : e.source ⊆ (extChartAt I p).source := by
    simpa [extChartAt_source] using hs
  have hmaps_ext : Set.MapsTo e e.source (extChartAt I (π p)).source := by
    simpa [extChartAt_source] using hmaps
  have hsmooth_model :
      ContDiffOn 𝕜 ∞
        (extChartAt I (π p) ∘ e ∘ (extChartAt I p).symm)
        (extChartAt I p '' e.source) := by
    refine contDiffOn_id.congr ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_chart : x ∈ (chartAt H p).source := hs hx
    have hx_target : (chartAt H p) x ∈ (chartAt H (π p)).target := by
      simpa [e, liftedProjectionBranch] using hx.2
    have hstep :
        e x = (chartAt H (π p)).symm ((chartAt H p) x) := by
      change (liftedProjectionBranch (H := H) π hπ p) x =
        (chartAt H (π p)).symm ((liftedCoveringChart (H := H) π hπ p) x)
      rfl
    have hright :
        (chartAt H (π p)) ((chartAt H (π p)).symm ((chartAt H p) x)) = (chartAt H p) x := by
      exact (chartAt H (π p)).right_inv hx_target
    calc
      extChartAt I (π p) (e ((extChartAt I p).symm (extChartAt I p x)))
          = extChartAt I (π p) (e x) := by
              rw [PartialEquiv.left_inv (extChartAt I p) (by simpa [extChartAt_source] using hx_chart)]
      _ = extChartAt I (π p) ((chartAt H (π p)).symm ((chartAt H p) x)) := by rw [hstep]
      _ = I ((chartAt H p) x) := by
            simp [extChartAt_coe, extChartAt_coe_symm, hright]
      _ = extChartAt I p x := by simp [extChartAt_coe]
  exact (contMDiffOn_iff_of_subset_source'
    (I := I) (I' := I) (f := e) (s := e.source) (x := p) (y := π p) hs_ext hmaps_ext).2
    hsmooth_model

/-- **Math.** The inverse of the canonical local branch through `p` is smooth, again
because its coordinate representative is the identity. -/
theorem liftedProjectionBranch_symm_contMDiffOn
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
    ContMDiffOn I I ∞
      (liftedProjectionBranch (H := H) π hπ p).symm
      (liftedProjectionBranch (H := H) π hπ p).target := by
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := liftedProjectionBranch (H := H) π hπ p
  have hs : e.target ⊆ (chartAt H (π p)).source := by
    intro x hx
    simpa [e, liftedProjectionBranch]
      using hx.1
  have hmaps : Set.MapsTo e.symm e.target (chartAt H p).source := by
    intro x hx
    have hx_target : (chartAt H (π p)) x ∈ (liftedCoveringChart (H := H) π hπ p).target := by
      simpa [e, liftedProjectionBranch] using hx.2
    change (liftedCoveringChart (H := H) π hπ p).symm ((chartAt H (π p)) x) ∈
      (liftedCoveringChart (H := H) π hπ p).source
    exact (liftedCoveringChart (H := H) π hπ p).symm_mapsTo hx_target
  have hs_ext : e.target ⊆ (extChartAt I (π p)).source := by
    simpa [extChartAt_source] using hs
  have hmaps_ext : Set.MapsTo e.symm e.target (extChartAt I p).source := by
    simpa [extChartAt_source] using hmaps
  have hsmooth_model :
      ContDiffOn 𝕜 ∞
        (extChartAt I p ∘ e.symm ∘ (extChartAt I (π p)).symm)
        (extChartAt I (π p) '' e.target) := by
    refine contDiffOn_id.congr ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_chart : x ∈ (chartAt H (π p)).source := hs hx
    have hx_target : (chartAt H (π p)) x ∈ (chartAt H p).target := by
      change (chartAt H (π p)) x ∈ (liftedCoveringChart (H := H) π hπ p).target
      simpa [e, liftedProjectionBranch] using hx.2
    have hstep :
        e.symm x = (chartAt H p).symm ((chartAt H (π p)) x) := by
      change (liftedProjectionBranch (H := H) π hπ p).symm x =
        (liftedCoveringChart (H := H) π hπ p).symm ((chartAt H (π p)) x)
      rfl
    have hright :
        (chartAt H p) ((chartAt H p).symm ((chartAt H (π p)) x)) = (chartAt H (π p)) x := by
      exact (chartAt H p).right_inv hx_target
    calc
      extChartAt I p (e.symm ((extChartAt I (π p)).symm (extChartAt I (π p) x)))
          = extChartAt I p (e.symm x) := by
              rw [PartialEquiv.left_inv (extChartAt I (π p))
                (by simpa [extChartAt_source] using hx_chart)]
      _ = extChartAt I p ((chartAt H p).symm ((chartAt H (π p)) x)) := by rw [hstep]
      _ = I ((chartAt H (π p)) x) := by
            simp [extChartAt_coe, extChartAt_coe_symm, hright]
      _ = extChartAt I (π p) x := by simp [extChartAt_coe]
  exact (contMDiffOn_iff_of_subset_source'
    (I := I) (I' := I) (f := e.symm) (s := e.target) (x := π p) (y := p) hs_ext hmaps_ext).2
    hsmooth_model

/-- **Math.** The canonical local branch of the covering projection through `p`
packages to a manifold `PartialDiffeomorph`. -/
theorem lifted_projection_partial_diffeomorph
    (hπ : IsCoveringMap π) (p : M') :
    let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
    let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
    ∃ Φ : PartialDiffeomorph I I M' M ∞,
      p ∈ Φ.source ∧
      Set.EqOn π Φ Φ.source ∧
      Φ.toOpenPartialHomeomorph = liftedProjectionBranch (H := H) π hπ p := by
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  let _ : IsManifold I ∞ M' := liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ
  let e : OpenPartialHomeomorph M' M := liftedProjectionBranch (H := H) π hπ p
  let Φ : PartialDiffeomorph I I M' M ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := liftedProjectionBranch_contMDiffOn (I := I) (H := H) π hπ p
      contMDiffOn_invFun := liftedProjectionBranch_symm_contMDiffOn (I := I) (H := H) π hπ p }
  refine ⟨Φ, ?_, ?_, rfl⟩
  · simpa [Φ, e] using mem_liftedProjectionBranch_source (H := H) π hπ p
  · simpa [Φ, e] using liftedProjectionBranch_eqOn (H := H) π hπ p

/-- **Math.** In any smooth covering structure on `M'`, the canonical topological
branch through `p` is already a smooth local section of `π`. -/
theorem canonical_localInverse_contMDiffOn_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ContMDiffOn I I ∞
      (coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p)
      (coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p).source := by
  let _ : ChartedSpace H M' := cs
  let σ := coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p
  have hσ_cont : ContinuousOn σ σ.source := σ.continuousOn
  have hσ_sec : Set.RightInvOn σ π σ.source := by
    intro y hy
    exact apply_coveringLocalInverseAt_of_mem hsm.2.isCoveringMap.isLocalHomeomorph p hy
  -- A continuous local section of a smooth covering map is smooth on its open domain.
  simpa [σ] using
    hsm.2.contMDiffOn_of_continuous_rightInvOn (IE := I) (IM := I) σ.open_source hσ_cont hσ_sec

/-- **Math.** In any smooth covering structure, the inverse of the canonical
topological branch is smooth because it is the covering projection `π` on its
target. -/
theorem canonical_localInverse_symm_contMDiffOn_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ContMDiffOn I I ∞
      (coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p).symm
      (coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p).target := by
  let _ : ChartedSpace H M' := cs
  have hπsmooth :
      ContMDiffOn I I ∞ π
        (localHomeomorphAt hsm.2.isCoveringMap.isLocalHomeomorph p).source :=
    hsm.2.isLocalDiffeomorph.contMDiff.contMDiffOn
  -- The inverse branch is literally `π` on its source.
  refine hπsmooth.congr ?_
  intro z _
  simp

/-- **Math.** In any smooth covering structure, the canonical topological branch
through `p` packages to a manifold `PartialDiffeomorph`. -/
theorem canonical_localInverse_partial_diffeomorph_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    ∃ Φ : PartialDiffeomorph I I M M' ∞,
      Φ.toOpenPartialHomeomorph = coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p := by
  let _ : ChartedSpace H M' := cs
  let σ := coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p
  let Φ : PartialDiffeomorph I I M M' ∞ :=
    { toPartialEquiv := σ.toPartialEquiv
      open_source := σ.open_source
      open_target := σ.open_target
      contMDiffOn_toFun := canonical_localInverse_contMDiffOn_of_smooth_covering_structure
        (I := I) (H := H) (π := π) hsm p
      contMDiffOn_invFun := canonical_localInverse_symm_contMDiffOn_of_smooth_covering_structure
        (I := I) (H := H) (π := π) hsm p }
  exact ⟨Φ, rfl⟩

/-- **Math.** A model-space partial homeomorphism belongs to the smooth groupoid
once it is locally represented by smooth structomorphisms on its whole source. -/
theorem mem_contDiffGroupoid_of_local_structomorphOn_source
    {f : OpenPartialHomeomorph H H}
    (hf : ChartedSpace.LiftPropOn
      ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt) f f.source) :
    f ∈ contDiffGroupoid ∞ I := by
  refine (contDiffGroupoid ∞ I).locality ?_
  intro x hx
  have hfx := hf x hx
  have hfx' := hfx
  simp only [ChartedSpace.liftPropWithinAt_iff', chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm] at hfx'
  obtain ⟨-, hfx_prop⟩ := hfx'
  have hfx_prop' : (contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt f f.source x := by
    simpa using hfx_prop
  rw [OpenPartialHomeomorph.isLocalStructomorphWithinAt_source_iff
    (G := contDiffGroupoid ∞ I) (f := f)] at hfx_prop'
  obtain ⟨e, he, hsource, hEq, hxe⟩ := hfx_prop' hx
  refine ⟨e.source, e.open_source, hxe, ?_⟩
  have hEq' : Set.EqOn f e (f.source ∩ e.source) := by
    intro y hy
    exact hEq hy.2
  have hrestr : f.restr e.source ≈ e.restr f.source := by
    exact OpenPartialHomeomorph.Set.EqOn.restr_eqOn_source hEq'
  have hEqOnSource : f.restr e.source ≈ e := by
    simpa [OpenPartialHomeomorph.restr_eq_of_source_subset hsource] using hrestr
  exact (contDiffGroupoid ∞ I).mem_of_eqOnSource he hEqOnSource

/-- **Math.** Writing a manifold partial diffeomorphism in maximal-atlas charts
produces a smooth transition map on the model space. -/
theorem writtenIn_partial_diffeomorph_mem_contDiffGroupoid
    [ChartedSpace H M'] [IsManifold I ∞ M']
    {Φ : PartialDiffeomorph I I M M' ∞} {e : OpenPartialHomeomorph M H}
    {c : OpenPartialHomeomorph M' H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hc : c ∈ IsManifold.maximalAtlas I ∞ M') :
    (e.symm.trans Φ.toOpenPartialHomeomorph).trans c ∈ contDiffGroupoid ∞ I := by
  let f : OpenPartialHomeomorph H H := (e.symm.trans Φ.toOpenPartialHomeomorph).trans c
  have hΦ :
      ChartedSpace.LiftPropOn
        ((contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt)
        Φ.toOpenPartialHomeomorph Φ.source := by
    exact (isLocalStructomorphOn_contDiffGroupoid_iff
      (I := I) (n := ∞) (f := Φ.toOpenPartialHomeomorph)).2
      ⟨Φ.contMDiffOn_toFun, Φ.contMDiffOn_invFun⟩
  refine mem_contDiffGroupoid_of_local_structomorphOn_source (I := I) ?_
  intro y hy
  rw [ChartedSpace.liftPropWithinAt_iff']
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, Set.preimage_id_eq]
  refine ⟨f.continuousOn_toFun.continuousWithinAt hy, ?_⟩
  intro hyf
  have hy_chart :
      y ∈ e.target ∩ e.symm ⁻¹' (Φ.source ∩ Φ.toOpenPartialHomeomorph ⁻¹' c.source) := by
    have hyf' := hyf
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hyf'
    rcases hyf' with ⟨⟨hy_target, hy_source⟩, hy_csource⟩
    exact ⟨hy_target, hy_source, hy_csource⟩
  have htransport :
      (contDiffGroupoid ∞ I).IsLocalStructomorphWithinAt
        (c ∘ Φ.toOpenPartialHomeomorph ∘ e.symm)
        (e.symm ⁻¹' Φ.source) y := by
    exact StructureGroupoid.LocalInvariantProp.liftPropOn_indep_chart
      (hG := StructureGroupoid.isLocalStructomorphWithinAt_localInvariantProp
        (contDiffGroupoid ∞ I))
      he hc hΦ hy_chart
  rcases htransport hy_chart.2.1 with ⟨φ, hφ, hEq, hyφ⟩
  refine ⟨φ, hφ, ?_, hyφ⟩
  intro z hz
  have hz_big : z ∈ (e.symm ⁻¹' Φ.source) ∩ φ.source := by
    refine ⟨?_, hz.2⟩
    have hz' := hz.1
    simp only [f, OpenPartialHomeomorph.trans_source, PartialEquiv.trans_source,
      PartialEquiv.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hz'
    exact hz'.1.2
  simpa [f, OpenPartialHomeomorph.coe_trans, Function.comp_assoc] using hEq hz_big

/-- **Math.** Pulling a maximal-atlas chart back along a smooth partial
diffeomorphism yields a maximal-atlas chart on the target manifold. -/
theorem pullback_chart_mem_maximalAtlas_of_partial_diffeomorph
    [ChartedSpace H M'] [IsManifold I ∞ M']
    {Φ : PartialDiffeomorph I I M M' ∞}
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) :
    Φ.symm.toOpenPartialHomeomorph.trans e ∈ IsManifold.maximalAtlas I ∞ M' := by
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  have hc_max : c ∈ IsManifold.maximalAtlas I ∞ M' := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  constructor
  · simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      writtenIn_partial_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ) (e := e) (c := c) he hc_max
  · simpa [OpenPartialHomeomorph.trans_assoc,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm] using
      writtenIn_partial_diffeomorph_mem_contDiffGroupoid
        (I := I) (Φ := Φ.symm) (e := c) (c := e) hc_max he

/-- **Math.** Every canonical lifted covering chart belongs to any smooth-covering
maximal atlas on the total space. -/
theorem canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
    {cs : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (p : M') :
    let _ : ChartedSpace H M' := cs
    let _ : IsManifold I ∞ M' := hsm.1
    liftedCoveringChart (H := H) π hsm.2.isCoveringMap p ∈ IsManifold.maximalAtlas I ∞ M' := by
  let _ : ChartedSpace H M' := cs
  let _ : IsManifold I ∞ M' := hsm.1
  rcases canonical_localInverse_partial_diffeomorph_of_smooth_covering_structure
      (I := I) (H := H) (π := π) hsm p with ⟨Φ, hΦ⟩
  have hΦsymm :
      Φ.symm.toOpenPartialHomeomorph =
        (coveringLocalInverseAt hsm.2.isCoveringMap.isLocalHomeomorph p).symm := by
    simpa using congrArg OpenPartialHomeomorph.symm hΦ
  simpa [liftedCoveringChart, hΦsymm] using
    pullback_chart_mem_maximalAtlas_of_partial_diffeomorph
      (I := I) (Φ := Φ)
      (e := chartAt H (π p))
      (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞) (π p))

/-- **Math.** Once both smooth-covering structures contain the canonical lifted
charts, every chart of one maximal atlas is locally compatible with the
other. -/
theorem smooth_covering_maximalAtlas_subset_via_canonical
    {cs cs' : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (hsm' : let _ : ChartedSpace H M' := cs'
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π) :
    (let _ : ChartedSpace H M' := cs
     let _ : IsManifold I ∞ M' := hsm.1
     IsManifold.maximalAtlas I ∞ M') ⊆
      (let _ : ChartedSpace H M' := cs'
       let _ : IsManifold I ∞ M' := hsm'.1
       IsManifold.maximalAtlas I ∞ M') := by
  intro e he
  have hπ : IsCoveringMap π := by
    let _ : ChartedSpace H M' := cs
    exact hsm.2.isCoveringMap
  have hπ' : IsCoveringMap π := by
    let _ : ChartedSpace H M' := cs'
    exact hsm'.2.isCoveringMap
  let _ : ChartedSpace H M' := cs'
  let _ : IsManifold I ∞ M' := hsm'.1
  rw [IsManifold.mem_maximalAtlas_iff]
  intro d hd
  have hd_max : d ∈ IsManifold.maximalAtlas I ∞ M' := by
    exact IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have hforward : e.symm.trans d ∈ contDiffGroupoid ∞ I := by
    refine (contDiffGroupoid ∞ I).locality ?_
    intro x hx
    let p : M' := e.symm x
    let k : OpenPartialHomeomorph M' H :=
      liftedCoveringChart (H := H) π hπ p
    let s : Set H := e.target ∩ e.symm ⁻¹' k.source
    have hs : IsOpen s := by
      dsimp [s]
      exact e.symm.continuousOn_toFun.isOpen_inter_preimage e.open_target k.open_source
    have hxp : p ∈ k.source := by
      simpa [p, k] using
        mem_liftedCoveringChart_source (H := H) π hπ p
    have hxs : x ∈ s := by
      refine ⟨hx.1, ?_⟩
      simpa [p] using hxp
    have hk_source :
        let _ : ChartedSpace H M' := cs
        let _ : IsManifold I ∞ M' := hsm.1
        k ∈ IsManifold.maximalAtlas I ∞ M' := by
      let _ : ChartedSpace H M' := cs
      let _ : IsManifold I ∞ M' := hsm.1
      simpa [k] using
        canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
          (I := I) (H := H) (π := π) hsm p
    have hk_target : k ∈ IsManifold.maximalAtlas I ∞ M' := by
      have hcover : hπ' = hπ := Subsingleton.elim _ _
      simpa [k, hcover] using
        canonical_lifted_chart_mem_maximalAtlas_of_smooth_covering_structure
          (I := I) (H := H) (π := π) hsm' p
    have hek : e.symm.trans k ∈ contDiffGroupoid ∞ I := by
      let _ : ChartedSpace H M' := cs
      let _ : IsManifold I ∞ M' := hsm.1
      exact IsManifold.compatible_of_mem_maximalAtlas he hk_source
    have hkd : k.symm.trans d ∈ contDiffGroupoid ∞ I :=
      IsManifold.compatible_of_mem_maximalAtlas hk_target hd_max
    have hcomp : (e.symm.trans k).trans (k.symm.trans d) ∈ contDiffGroupoid ∞ I :=
      (contDiffGroupoid ∞ I).trans hek hkd
    have hEq :
        (e.symm.trans k).trans (k.symm.trans d) ≈ (e.symm.trans d).restr s := by
      calc
        (e.symm ≫ₕ k) ≫ₕ k.symm ≫ₕ d = e.symm ≫ₕ (k ≫ₕ k.symm) ≫ₕ d := by
          simp only [OpenPartialHomeomorph.trans_assoc]
        _ ≈ e.symm ≫ₕ OpenPartialHomeomorph.ofSet k.source k.open_source ≫ₕ d :=
          OpenPartialHomeomorph.EqOnSource.trans'
            (_root_.refl _)
            (OpenPartialHomeomorph.EqOnSource.trans'
              (OpenPartialHomeomorph.self_trans_symm _) (_root_.refl _))
        _ ≈ (e.symm ≫ₕ OpenPartialHomeomorph.ofSet k.source k.open_source) ≫ₕ d := by
          rw [OpenPartialHomeomorph.trans_assoc]
        _ ≈ e.symm.restr s ≫ₕ d := by
          rw [OpenPartialHomeomorph.trans_of_set']
          exact _root_.refl _
        _ ≈ (e.symm ≫ₕ d).restr s := by
          rw [OpenPartialHomeomorph.restr_trans]
    exact ⟨s, hs, hxs, (contDiffGroupoid ∞ I).mem_of_eqOnSource hcomp (Setoid.symm hEq)⟩
  constructor
  · exact hforward
  · simpa using (contDiffGroupoid ∞ I).symm hforward

/-- **Math.** A surjective topological covering map over a smooth manifold `M`
admits a smooth structure modelled on the same `I` for which `π` is a smooth
covering map. -/
theorem exists_smooth_covering_structure
    (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ cs : ChartedSpace H M',
      let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π := by
  refine ⟨liftedCoveringChartedSpace (H := H) π hπ, ?_⟩
  let _ : ChartedSpace H M' := liftedCoveringChartedSpace (H := H) π hπ
  refine ⟨liftedCoveringChartedSpace_isManifold (I := I) (H := H) π hπ, ?_⟩
  refine ⟨hπ, h_surj, ?_⟩
  intro p
  rcases lifted_projection_partial_diffeomorph (I := I) (H := H) π hπ p with
    ⟨Φ, hp, hEq, -⟩
  exact ⟨Φ, hp, hEq⟩

/-- **Math.** Any two smooth structures on the total space making the covering
projection a smooth covering map determine the same maximal smooth atlas. -/
theorem smooth_covering_same_smooth_structure
    {cs cs' : ChartedSpace H M'}
    (hsm : let _ : ChartedSpace H M' := cs
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π)
    (hsm' : let _ : ChartedSpace H M' := cs'
      IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π) :
    (let _ : ChartedSpace H M' := cs
     let _ : IsManifold I ∞ M' := hsm.1
     IsManifold.maximalAtlas I ∞ M') =
      (let _ : ChartedSpace H M' := cs'
       let _ : IsManifold I ∞ M' := hsm'.1
       IsManifold.maximalAtlas I ∞ M') := by
  apply Set.Subset.antisymm
  · exact smooth_covering_maximalAtlas_subset_via_canonical
      (I := I) (H := H) (π := π) hsm hsm'
  · exact smooth_covering_maximalAtlas_subset_via_canonical
      (I := I) (H := H) (π := π) hsm' hsm

/-- **Math.** Existence together with uniqueness up to the canonical owner
`IsManifold.maximalAtlas I ∞ M'`: a surjective topological covering map over a
smooth manifold has a smooth structure making it a smooth covering map, unique
as a maximal smooth atlas. -/
theorem exists_unique_smooth_covering_structure
    (hπ : IsCoveringMap π) (h_surj : Function.Surjective π) :
    ∃ cs : ChartedSpace H M',
      ∃ hsm : let _ : ChartedSpace H M' := cs
        IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π,
      ∀ {cs' : ChartedSpace H M'}
        (hsm' : let _ : ChartedSpace H M' := cs'
          IsManifold I ∞ M' ∧ IsSmoothCoveringMap I I π),
        (let _ : ChartedSpace H M' := cs
         let _ : IsManifold I ∞ M' := hsm.1
         IsManifold.maximalAtlas I ∞ M') =
          (let _ : ChartedSpace H M' := cs'
           let _ : IsManifold I ∞ M' := hsm'.1
           IsManifold.maximalAtlas I ∞ M') := by
  rcases exists_smooth_covering_structure (I := I) (H := H) π hπ h_surj with ⟨cs, hcs⟩
  refine ⟨cs, hcs, ?_⟩
  intro cs' hsm'
  exact smooth_covering_same_smooth_structure (I := I) (H := H) (π := π) hcs hsm'

end Manifold

end
