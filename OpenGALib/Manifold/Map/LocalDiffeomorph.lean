import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Local diffeomorphisms and the inverse function theorem for manifolds

The inverse function theorem at the level of smooth manifolds, plus the
detection of smoothness through composition with local diffeomorphisms.
Mathlib supplies the inverse function theorem on Banach spaces but leaves
its manifold counterpart open; this file closes that gap and records the
companion composition characterizations.

The development is layered by how much structure each statement needs:

1. **Model-space bridge** — a chart-representative passes ordinary
   smoothness, derivatives, and invertibility back and forth between a
   manifold map and its preferred extended-chart representative. This is the
   private plumbing that ports the Banach-space inverse function theorem
   through charts; it needs only an interior point.
2. **Interior-point inverse function theorem** —
   `isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible`: at an interior
   point, a `C^n` map with invertible manifold derivative is a `C^n` local
   diffeomorphism. The interior hypothesis is essential; the statement fails
   at boundary points.
3. **Connected-neighborhood packaging** — a local diffeomorphism restricts to
   a genuine diffeomorphism between connected open neighborhoods. Stated
   generally and then specialized to the boundaryless Euclidean model, where
   interiority is automatic, giving the classical inverse function theorem.
4. **Composition characterizations** — composing with a smooth local
   diffeomorphism (on the left, or on the right when surjective) both
   preserves and detects smoothness. These are the reusable lemmas behind
   later smoothness-by-comparison arguments.

## Main results

* `Manifold.isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible` — the
  interior-point inverse function theorem.
* `Manifold.partialDiffeomorph_diffeomorph_image_of_open_subset` — restricting
  a partial diffeomorphism to an open subset of its source gives a
  diffeomorphism onto the open image.
* `Manifold.IsLocalDiffeomorphAt.exists_connected_open_diffeomorph` — a local
  diffeomorphism restricts to a diffeomorphism between connected open
  neighborhoods.
* `Manifold.exists_connected_open_neighborhoods_diffeomorph_of_mfderiv_isInvertible` —
  the inverse function theorem for boundaryless Euclidean-model manifolds.
* `Manifold.smooth_iff_comp_left_of_isLocalDiffeomorph` — left-composition with
  a smooth local diffeomorphism preserves and detects smoothness.
* `Manifold.smooth_iff_comp_right_of_surjective_isLocalDiffeomorph` —
  right-composition with a surjective smooth local diffeomorphism preserves and
  detects smoothness.

Provenance: SmoothManifoldsLee a5f308c — Theorem_4_5, Exercise_4_10.
-/

noncomputable section

open Set
open scoped Manifold ContDiff Topology

universe u𝕜 uE uF uH uG uM uN

namespace Manifold

section LocalInverseFunction

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}

private lemma writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint
    {f : M → N} {p : M} {f' : TangentSpace I p →L[𝕜] TangentSpace J (f p)}
    (hp : I.IsInteriorPoint p)
    (hf : HasMFDerivAt I J f p f') :
    HasFDerivAt (writtenInExtChartAt I J p f : E → F) f' (extChartAt I p p) := by
  -- The manifold derivative already controls the chart representative within `range I`.
  refine hf.2.hasFDerivAt ?_
  -- Interior points see `range I` as a genuine neighborhood in the chart.
  exact range_mem_nhds_isInteriorPoint hp

private lemma writtenInExtChartAt_contDiffAt_of_isInteriorPoint
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p)
    (hf : ContMDiffAt I J n f p) :
    ContDiffAt 𝕜 n (writtenInExtChartAt I J p f : E → F) (extChartAt I p p) := by
  -- Rewrite manifold smoothness into smoothness of the preferred chart representative on `range I`.
  rw [contMDiffAt_iff_of_mem_source (I := I) (I' := J) (x := p) (y := f p)
    (x' := p) (f := f) (mem_chart_source H p) (mem_chart_source G (f p))] at hf
  -- Interior points let us drop the `WithinAt` restriction to `range I`.
  exact hf.2.contDiffAt (range_mem_nhds_isInteriorPoint hp)

private lemma writtenInExtChartAt_contDiffOn_of_contMDiff
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hf : ContMDiff I J n f) :
    ContDiffOn 𝕜 n (writtenInExtChartAt I J p f : E → F)
      ((extChartAt I p).target ∩
        (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source) := by
  let s : Set M := (extChartAt I p).source ∩ f ⁻¹' (extChartAt J (f p)).source
  have hs : s ⊆ (extChartAt I p).source := by
    intro x hx
    exact hx.1
  have hmaps : Set.MapsTo f s (extChartAt J (f p)).source := by
    intro x hx
    exact hx.2
  have hfOn : ContMDiffOn I J n f s := by
    -- The global smoothness hypothesis restricts to any subset of the manifold source.
    exact hf.contMDiffOn
  have hchart :
      ContDiffOn 𝕜 n (writtenInExtChartAt I J p f : E → F) ((extChartAt I p) '' s) := by
    -- Work first on the open chart image supplied by `contMDiffOn_iff_of_subset_source'`.
    exact (contMDiffOn_iff_of_subset_source' (I := I) (I' := J) (n := n)
      (x := p) (y := f p) (f := f) hs hmaps).1 hfOn
  have himage :
      (extChartAt I p) '' s =
        ((extChartAt I p).target ∩
          (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source) := by
    -- This is the standard image-of-source-intersection formula for a partial equivalence.
    simpa [s, Function.comp, extChartAt_target, extChartAt_coe_symm] using
      (extChartAt I p).image_source_inter_eq' (f ⁻¹' (extChartAt J (f p)).source)
  -- Rewriting the chart image into the natural chart domain gives the desired ordinary statement.
  rw [himage] at hchart
  simpa using hchart

private lemma isOpen_setOf_isInvertible :
    IsOpen {A : E →L[𝕜] F | A.IsInvertible} := by
  -- The predicate `IsInvertible` is definitionally the range of the coercion from
  -- continuous linear equivalences.
  simpa [ContinuousLinearMap.IsInvertible] using
    (ContinuousLinearEquiv.isOpen :
      IsOpen (Set.range (fun e : E ≃L[𝕜] F => (e : E →L[𝕜] F))))

private lemma exists_open_subset_chart_domain_with_invertible_fderiv
    {n : WithTop ℕ∞} {g : E → F} {a : E} {Ω : Set E}
    (hΩ : Ω ∈ nhds a)
    (hgΩ : ContDiffOn 𝕜 n g Ω)
    (hn : n ≠ 0)
    (haInv : (fderiv 𝕜 g a).IsInvertible) :
    ∃ s : Set E, IsOpen s ∧ a ∈ s ∧ s ⊆ Ω ∧ ContDiffOn 𝕜 n g s ∧
      ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible := by
  -- First choose an honest open neighborhood inside the original chart domain.
  rcases mem_nhds_iff.mp hΩ with ⟨t, ht_subset, ht_open, ha_t⟩
  have hcont_t : ContinuousOn (fderiv 𝕜 g) t := by
    exact (hgΩ.mono ht_subset).continuousOn_fderiv_of_isOpen ht_open
      (ENat.one_le_iff_ne_zero_withTop.mpr hn)
  -- Then intersect it with the open preimage of the invertible locus of the derivative.
  have hpre_inv : (fderiv 𝕜 g) ⁻¹' {A : E →L[𝕜] F | A.IsInvertible} ∈ nhds a := by
    have haInv_nhds : {A : E →L[𝕜] F | A.IsInvertible} ∈ nhds (fderiv 𝕜 g a) := by
      exact (isOpen_setOf_isInvertible (𝕜 := 𝕜) (E := E) (F := F)).mem_nhds haInv
    exact (hcont_t.continuousAt (ht_open.mem_nhds ha_t)).preimage_mem_nhds haInv_nhds
  rcases mem_nhds_iff.mp hpre_inv with ⟨u, hu_subset, hu_open, ha_u⟩
  refine ⟨t ∩ u, ht_open.inter hu_open, ⟨ha_t, ha_u⟩, ?_, ?_, ?_⟩
  · -- The shrunken set still sits inside the original chart-domain neighborhood.
    intro x hx
    exact ht_subset hx.1
  · -- Smoothness restricts from the original chart representative.
    exact hgΩ.mono (by intro x hx; exact ht_subset hx.1)
  · -- By construction, the derivative is invertible everywhere on the shrunken set.
    intro x hx
    exact hu_subset hx.2

private lemma contDiffOn_symm_of_restricted_toOpenPartialHomeomorph
    {n : WithTop ℕ∞} {g : E → F} {a : E} {f' : E ≃L[𝕜] F}
    (hgAt : ContDiffAt 𝕜 n g a)
    (hg_fderiv : HasFDerivAt g (f' : E →L[𝕜] F) a)
    (hn : n ≠ 0)
    {s : Set E} (hs_open : IsOpen s)
    (hs_source : s ⊆ (hgAt.toOpenPartialHomeomorph g hg_fderiv hn).source)
    (hg_s : ContDiffOn 𝕜 n g s)
    (hInv_s : ∀ x ∈ s, (fderiv 𝕜 g x).IsInvertible) :
    ContDiffOn 𝕜 n
      (hgAt.toOpenPartialHomeomorph g hg_fderiv hn).symm
      ((hgAt.toOpenPartialHomeomorph g hg_fderiv hn).restr s).target := by
  let R := hgAt.toOpenPartialHomeomorph g hg_fderiv hn
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr hs_source
  -- The restricted target is open, so pointwise smoothness of `R.symm` upgrades to `ContDiffOn`.
  rw [(R.restr s).open_target.contDiffOn_iff]
  intro y hy
  have hy' : y ∈ R.target ∧ R.symm y ∈ s := by
    simpa [OpenPartialHomeomorph.restr, hs_open.interior_eq, Set.mem_inter_iff, Set.mem_preimage]
      using hy
  have hy_target : y ∈ R.target := hy'.1
  have hy_s : R.symm y ∈ s := hy'.2
  let x : E := R.symm y
  have hx : x ∈ s := hy_s
  have hx_cont : ContDiffAt 𝕜 n g x := (hg_s x hx).contDiffAt (hs_open.mem_nhds hx)
  have hx_deriv : HasFDerivAt g (fderiv 𝕜 g x) x := by
    exact (hx_cont.differentiableAt hn).hasFDerivAt
  have hx_R_source : x ∈ R.source := hs_source hx
  have hx_deriv' :
      HasFDerivAt g ((Classical.choose (hInv_s x hx) : E ≃L[𝕜] F) : E →L[𝕜] F) x := by
    simpa [Classical.choose_spec (hInv_s x hx)] using hx_deriv
  have hx_left : R.symm (g x) = x := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe] using R.left_inv hx_R_source
  have hx_derivR :
      HasFDerivAt R ((Classical.choose (hInv_s x hx) : E ≃L[𝕜] F) : E →L[𝕜] F) (R.symm (g x)) := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, hx_left] using hx_deriv'
  have hx_contR : ContDiffAt 𝕜 n R (R.symm (g x)) := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, hx_left] using hx_cont
  -- Apply the easy direction of the inverse function theorem at the concrete point `x`.
  have hx_symm : ContDiffAt 𝕜 n R.symm (g x) := by
    refine R.contDiffAt_symm (R.map_source hx_R_source) hx_derivR hx_contR
  have hy_eq : g (R.symm y) = y := by
    simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x] using R.right_inv hy_target
  simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe, x, hy_eq] using hx_symm

private lemma model_partialDiffeomorph_of_inverse_function_theorem
    {n : WithTop ℕ∞} {g : E → F} {a : E} {Ω : Set E} {T : Set F} {f' : E ≃L[𝕜] F}
    (hΩ : Ω ∈ nhds a)
    (hgΩ : ContDiffOn 𝕜 n g Ω)
    (hgT : Set.MapsTo g Ω T)
    (hgAt : ContDiffAt 𝕜 n g a)
    (hg_fderiv : HasFDerivAt g (f' : E →L[𝕜] F) a)
    (hn : n ≠ 0)
    (haInv : (fderiv 𝕜 g a).IsInvertible) :
    ∃ Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n,
      a ∈ Ψ.source ∧ Ψ.source ⊆ Ω ∧ Ψ.target ⊆ T ∧ Set.EqOn g Ψ Ψ.source := by
  let R := hgAt.toOpenPartialHomeomorph g hg_fderiv hn
  have haR : a ∈ R.source := hgAt.mem_toOpenPartialHomeomorph_source hg_fderiv hn
  have hΩR : Ω ∩ R.source ∈ nhds a := Filter.inter_mem hΩ (R.open_source.mem_nhds haR)
  have haInvR : (fderiv 𝕜 g a).IsInvertible := haInv
  obtain ⟨s, hs_open, ha_s, hs_subset, hg_s, hInv_s⟩ :=
    exists_open_subset_chart_domain_with_invertible_fderiv
      (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a) (Ω := Ω ∩ R.source)
      hΩR (hgΩ.mono Set.inter_subset_left) hn haInvR
  have hs_Ω : s ⊆ Ω := fun x hx => (hs_subset hx).1
  have hs_R : s ⊆ R.source := fun x hx => (hs_subset hx).2
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr hs_R
  have htarget_restr : (R.restr s).target = g '' s := by
    rw [← (R.restr s).image_source_eq_target, hsource_restr]
    simp [R, ContDiffAt.toOpenPartialHomeomorph_coe]
  have hsymm :
      ContDiffOn 𝕜 n R.symm (R.restr s).target := by
    exact contDiffOn_symm_of_restricted_toOpenPartialHomeomorph
      (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a)
      hgAt hg_fderiv hn hs_open hs_R hg_s hInv_s
  let Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n :=
    { toPartialEquiv := (R.restr s).toPartialEquiv
      open_source := (R.restr s).open_source
      open_target := (R.restr s).open_target
      contMDiffOn_toFun := by
        -- On model spaces, the restricted forward branch is just `g` on the shrunken source.
        rw [hsource_restr]
        simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe] using hg_s.contMDiffOn
      contMDiffOn_invFun := by
        -- The previous lemma gives smoothness of the inverse branch on the concrete open target.
        simpa [R] using hsymm.contMDiffOn }
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · -- The base point stays in the shrunken source.
    change a ∈ (R.restr s).source
    rwa [hsource_restr]
  · -- The packaged source is still contained in the original chart-domain set.
    change (R.restr s).source ⊆ Ω
    rw [hsource_restr]
    exact hs_Ω
  · -- The packaged target stays in the prescribed codomain chart target.
    intro y hy
    have hy' : y ∈ R.target ∧ R.symm y ∈ s := by
      simpa [Ψ, OpenPartialHomeomorph.restr, hs_open.interior_eq, Set.mem_inter_iff,
        Set.mem_preimage] using hy
    have hy_eq : g (R.symm y) = y := by
      simpa [R, ContDiffAt.toOpenPartialHomeomorph_coe] using R.right_inv hy'.1
    have hy_mem : g (R.symm y) ∈ T := hgT (hs_Ω hy'.2)
    simpa [hy_eq] using hy_mem
  · -- The forward function of the packaged partial diffeomorphism is literally `g`.
    intro x hx
    simpa [Ψ, R, ContDiffAt.toOpenPartialHomeomorph_coe]

private lemma partialDiffeomorph_of_writtenInExtChartAt
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    {Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n}
    (hpΨ : extChartAt I p p ∈ Ψ.source)
    (hsource :
      Ψ.source ⊆
        (extChartAt I p).target ∩
          (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source)
    (htarget : Ψ.target ⊆ (extChartAt J (f p)).target)
    (hEq : Set.EqOn (writtenInExtChartAt I J p f) Ψ Ψ.source) :
    ∃ Φ : PartialDiffeomorph I J M N n, p ∈ Φ.source ∧ Set.EqOn f Φ Φ.source := by
  let Γ : PartialEquiv M N :=
    (extChartAt I p).trans (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm)
  have hinner_source :
      (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).source = Ψ.source := by
    ext y
    constructor
    · intro hy
      simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
        Set.mem_preimage] at hy
      exact hy.1
    · intro hy
      have hy_target : Ψ y ∈ Ψ.target := Ψ.map_source hy
      simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
        Set.mem_preimage]
      exact ⟨hy, htarget hy_target⟩
  have hΓ_source :
      Γ.source = (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Ψ.source := by
    change
      ((extChartAt I p).trans (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm)).source =
        (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Ψ.source
    rw [PartialEquiv.trans_source, hinner_source]
  have hinner_target :
      (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).target =
        (extChartAt J (f p)).source ∩
          (extChartAt J (f p)) ⁻¹' Ψ.target := by
    rw [PartialEquiv.trans_target]
    rfl
  have hΓ_target :
      Γ.target =
        (extChartAt J (f p)).source ∩
          (extChartAt J (f p)) ⁻¹' Ψ.target := by
    calc
      Γ.target = (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).target := by
        ext y
        constructor
        · intro hy
          simp only [Γ, PartialEquiv.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hy
          exact hy.1
        · intro hy
          have hy_source :
              (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).symm y ∈
                (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).source :=
            (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).map_target hy
          have hy_Ψ_source :
              (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).symm y ∈ Ψ.source := by
            rwa [hinner_source] at hy_source
          have hy_chart :
              (Ψ.toPartialEquiv.trans (extChartAt J (f p)).symm).symm y ∈
                (extChartAt I p).target := (hsource hy_Ψ_source).1
          simp only [Γ, PartialEquiv.trans_target, Set.mem_inter_iff, Set.mem_preimage]
          exact ⟨hy, hy_chart⟩
      _ = (extChartAt J (f p)).source ∩ (extChartAt J (f p)) ⁻¹' Ψ.target := hinner_target
  have hmid_to :
      ContMDiffOn 𝓘(𝕜, E) J n ((extChartAt J (f p)).symm ∘ Ψ) Ψ.source := by
    -- Transport smoothness by plain composition with the extended charts.
    refine (contMDiffOn_extChartAt_symm (I := J) (n := n) (f p)).comp Ψ.contMDiffOn_toFun ?_
    intro x hx
    exact htarget (Ψ.map_source hx)
  have hmid_inv :
      ContMDiffOn 𝓘(𝕜, F) I n ((extChartAt I p).symm ∘ Ψ.symm) Ψ.target := by
    -- The inverse branch lands back in the preferred source chart by the source inclusion
    -- hypothesis on `Ψ`.
    refine (contMDiffOn_extChartAt_symm (I := I) (n := n) p).comp Ψ.contMDiffOn_invFun ?_
    intro y hy
    exact (hsource (Ψ.map_target hy)).1
  let Φ : PartialDiffeomorph I J M N n :=
    { toPartialEquiv := Γ
      open_source := by
        rw [hΓ_source]
        exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
          (isOpen_extChartAt_source (I := I) p) Ψ.open_source
      open_target := by
        rw [hΓ_target]
        exact (continuousOn_extChartAt (I := J) (f p)).isOpen_inter_preimage
          (isOpen_extChartAt_source (I := J) (f p)) Ψ.open_target
      contMDiffOn_toFun := by
        -- Compose the model-space smooth branch with the preferred source and target charts.
        rw [hΓ_source]
        simpa [Γ, Function.comp_assoc] using
          hmid_to.comp' (contMDiffOn_extChartAt (I := I) (n := n) (x := p))
      contMDiffOn_invFun := by
        -- Apply the same chart-composition argument to the inverse branch.
        rw [hΓ_target]
        simpa [Γ, Function.comp_assoc] using
          hmid_inv.comp' (contMDiffOn_extChartAt (I := J) (n := n) (x := f p)) }
  refine ⟨Φ, ?_, ?_⟩
  · -- The base point belongs to the transported source because its chart image belongs to `Ψ.source`.
    rw [show Φ.source = Γ.source by rfl, hΓ_source]
    exact ⟨mem_extChartAt_source (I := I) p, hpΨ⟩
  · intro x hx
    have hx' : x ∈ (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Ψ.source := by
      simpa [Φ, hΓ_source] using hx
    have hxΨ : extChartAt I p x ∈ Ψ.source := hx'.2
    have hx_left : (extChartAt I p).symm (extChartAt I p x) = x :=
      (extChartAt I p).left_inv hx'.1
    have hfx_source : f x ∈ (extChartAt J (f p)).source := by
      have hpre : f ((extChartAt I p).symm (extChartAt I p x)) ∈ (extChartAt J (f p)).source := by
        simpa [Function.comp] using (hsource hxΨ).2
      have hfx_eq : f ((extChartAt I p).symm (extChartAt I p x)) = f x := by
        change f ((extChartAt I p).symm (extChartAt I p x)) = f x
        exact congrArg f hx_left
      exact hfx_eq ▸ hpre
    -- On the transported source, the chart representative agrees with `Ψ`, so the charts cancel.
    have hΦx : Φ x = f x := by
      calc
        Φ x = (extChartAt J (f p)).symm (Ψ (extChartAt I p x)) := by
          simp [Φ, Γ, PartialEquiv.trans_apply]
        _ = (extChartAt J (f p)).symm (writtenInExtChartAt I J p f (extChartAt I p x)) := by
          rw [(hEq hxΨ).symm]
        _ = f x := by
          rw [show writtenInExtChartAt I J p f (extChartAt I p x) =
              extChartAt J (f p) (f x) by
                change extChartAt J (f p) (f ((extChartAt I p).symm (extChartAt I p x))) =
                  extChartAt J (f p) (f x)
                exact congrArg (extChartAt J (f p)) (congrArg f hx_left)]
          exact (extChartAt J (f p)).left_inv hfx_source
    exact hΦx.symm

private lemma isLocalDiffeomorphAt_of_writtenInExtChartAt
    {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    {Ψ : PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, F) E F n}
    (hpΨ : extChartAt I p p ∈ Ψ.source)
    (hsource :
      Ψ.source ⊆
        (extChartAt I p).target ∩
          (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source)
    (htarget : Ψ.target ⊆ (extChartAt J (f p)).target)
    (hEq : Set.EqOn (writtenInExtChartAt I J p f) Ψ Ψ.source) :
    IsLocalDiffeomorphAt I J n f p := by
  -- Once the transported partial diffeomorphism exists, the local-diffeomorphism witness is
  -- exactly the transported source membership plus equality on that source.
  obtain ⟨Φ, hpΦ, hΦ⟩ :=
    partialDiffeomorph_of_writtenInExtChartAt
      (I := I) (J := J) (f := f) (p := p) hpΨ hsource htarget hEq
  exact ⟨Φ, hpΦ, hΦ⟩

private lemma writtenInExtChartAt_fderiv_eq_mfderiv_of_isInteriorPoint
    {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p)
    (hmd : MDifferentiableAt I J f p) :
    fderiv 𝕜 (writtenInExtChartAt I J p f : E → F) (extChartAt I p p) = mfderiv I J f p := by
  -- Identify the chart derivative through `mfderiv = fderivWithin`, then remove the `Within`
  -- because interior points see `range I` as a neighborhood.
  calc
    fderiv 𝕜 (writtenInExtChartAt I J p f : E → F) (extChartAt I p p)
      = fderivWithin 𝕜 (writtenInExtChartAt I J p f : E → F) (Set.range I) (extChartAt I p p) := by
          symm
          exact fderivWithin_of_mem_nhds (range_mem_nhds_isInteriorPoint hp)
    _ = mfderiv I J f p := by
          symm
          simpa using (MDifferentiableAt.mfderiv (I := I) (I' := J) (f := f) (x := p) hmd)

private lemma writtenInExtChartAt_fderiv_isInvertible_of_isInteriorPoint
    {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p)
    (hmd : MDifferentiableAt I J f p)
    (hfp : (mfderiv I J f p).IsInvertible) :
    (fderiv 𝕜 (writtenInExtChartAt I J p f : E → F) (extChartAt I p p)).IsInvertible := by
  -- Rewriting the chart derivative into `mfderiv` makes the claimed invertibility immediate.
  rw [writtenInExtChartAt_fderiv_eq_mfderiv_of_isInteriorPoint (I := I) (J := J) hp hmd]
  exact hfp

private lemma writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint_choose
    {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p)
    (hmd : MDifferentiableAt I J f p)
    (hfp : (mfderiv I J f p).IsInvertible) :
    HasFDerivAt (writtenInExtChartAt I J p f : E → F)
      (((Classical.choose hfp : E ≃L[𝕜] F) : E →L[𝕜] F)) (extChartAt I p p) := by
  -- The manifold derivative already gives the chart derivative; we only retarget it to the
  -- chosen continuous linear equivalence witnessing invertibility.
  have hbase :
      HasFDerivAt (writtenInExtChartAt I J p f : E → F) (mfderiv I J f p) (extChartAt I p p) :=
    writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := I) (J := J) (f := f) (p := p) hp
      hmd.hasMFDerivAt
  rw [← Classical.choose_spec hfp] at hbase
  simpa using hbase

/-- **Math.** At an interior point `p`, a `C^n` map with invertible manifold derivative is a
`C^n` local diffeomorphism at `p`. This is the inverse function theorem for manifolds; the
interior hypothesis is essential, since the statement fails at boundary points. -/
theorem isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    {n : WithTop ℕ∞} (hn : n ≠ 0) [IsManifold I n M] [IsManifold J n N] {f : M → N} {p : M}
    (hp : I.IsInteriorPoint p)
    (hf : ContMDiff I J n f)
    (hfp : (mfderiv I J f p).IsInvertible) :
    IsLocalDiffeomorphAt I J n f p := by
  let g : E → F := writtenInExtChartAt I J p f
  let a : E := extChartAt I p p
  let Ω : Set E :=
    (extChartAt I p).target ∩
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source
  let T : Set F := (extChartAt J (f p)).target
  have hmd : MDifferentiableAt I J f p := (hf.contMDiffAt).mdifferentiableAt hn
  have hΩ_target : (extChartAt I p).target ∈ nhds a := by
    -- Interiority upgrades the chart target from a neighborhood within `range I` to an ambient one.
    change (extChartAt I p).target ∈ nhds (extChartAt I p p)
    rw [← nhdsWithin_eq_nhds.2 (range_mem_nhds_isInteriorPoint hp)]
    exact extChartAt_target_mem_nhdsWithin (I := I) p
  have hΩ_source :
      (f ∘ (extChartAt I p).symm) ⁻¹' (extChartAt J (f p)).source ∈ nhds a := by
    -- The common chart domain is also a neighborhood because `f p` lies in the target chart source.
    simpa [a, Function.comp] using
      (extChartAt_preimage_mem_nhds (I := I) (x := p)
        ((hf.contMDiffAt.continuousAt).preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) (f p))))
  have hΩ : Ω ∈ nhds a := by
    -- Shrink inside the intersection of the preferred source and target charts.
    exact Filter.inter_mem hΩ_target hΩ_source
  have hgΩ : ContDiffOn 𝕜 n g Ω := by
    -- Global manifold smoothness gives ordinary smoothness of the chart representative on `Ω`.
    simpa [g, Ω] using
      writtenInExtChartAt_contDiffOn_of_contMDiff (I := I) (J := J) (n := n) (f := f) (p := p) hf
  have hgT : Set.MapsTo g Ω T := by
    -- By construction, the preferred chart representative maps the common chart domain into the
    -- preferred target chart.
    simpa [g, Ω, T] using (writtenInExtChartAt_mapsTo (I := I) (I' := J) (x := p) (f := f))
  have hgAt : ContDiffAt 𝕜 n g a := by
    -- At the interior point, the chart representative is `C^n` in the ordinary sense.
    simpa [g, a] using
      writtenInExtChartAt_contDiffAt_of_isInteriorPoint
        (I := I) (J := J) (n := n) (f := f) (p := p) hp hf.contMDiffAt
  have hg_fderiv_choose :
      HasFDerivAt g (((Classical.choose hfp : E ≃L[𝕜] F) : E →L[𝕜] F)) a := by
    -- The chosen inverse witness for `mfderiv` is also the derivative of the chart representative.
    simpa [g, a] using
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint_choose
        (I := I) (J := J) (f := f) (p := p) hp hmd hfp
  have haInv_chart : (fderiv 𝕜 g a).IsInvertible := by
    -- The ordinary derivative is invertible because it is literally the manifold derivative.
    simpa [g, a] using
      writtenInExtChartAt_fderiv_isInvertible_of_isInteriorPoint
        (I := I) (J := J) (f := f) (p := p) hp hmd hfp
  obtain ⟨Ψ, hpΨ, hsource, htarget, hEq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := 𝕜) (E := E) (F := F) (g := g) (a := a) (Ω := Ω) (T := T)
      (f' := Classical.choose hfp) hΩ hgΩ hgT hgAt hg_fderiv_choose hn haInv_chart
  -- Transport the model-space partial diffeomorphism back through the preferred charts.
  refine isLocalDiffeomorphAt_of_writtenInExtChartAt (I := I) (J := J) (n := n)
    (f := f) (p := p) (Ψ := Ψ) ?_ ?_ ?_ ?_
  · simpa [a] using hpΨ
  · simpa [Ω] using hsource
  · simpa [T] using htarget
  · simpa [g] using hEq

end LocalInverseFunction

section ConnectedNeighborhoods

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [TopologicalSpace G]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace G N]
variable {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}

/-- **Math.** Restricting a smooth partial diffeomorphism to an open subset of its source yields a
genuine diffeomorphism onto the corresponding open image. -/
theorem partialDiffeomorph_diffeomorph_image_of_open_subset
    (Φ : PartialDiffeomorph I J M N ∞) {s : Set M} (hs : IsOpen s) (hsub : s ⊆ Φ.source) :
    ∃ V : TopologicalSpace.Opens N,
      ∃ Ψ : (⟨s, hs⟩ : TopologicalSpace.Opens M) ≃ₘ⟮I, J⟯ V,
        ∀ x : (⟨s, hs⟩ : TopologicalSpace.Opens M), (Ψ x : N) = Φ x := by
  let U : TopologicalSpace.Opens M := ⟨s, hs⟩
  let V : TopologicalSpace.Opens N :=
    ⟨Φ '' s, Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hs hsub⟩
  let e : U ≃ₜ V :=
    Φ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hsub rfl
  let Ψ : U ≃ₘ⟮I, J⟯ V := by
    refine
      { toEquiv := e.toEquiv
        contMDiff_toFun := ?_
        contMDiff_invFun := ?_ }
    · intro x
      -- On the restricted source, the forward map is still the ambient smooth branch `Φ`.
      refine (ContMDiffAt.subtypeVal_comp_iff V (fun y : U ↦ e y) x).1 ?_
      refine (contMDiffAt_subtype_iff (U := U) (f := Φ) (x := x)).2 ?_
      exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hsub x.2))
    · intro y
      -- On the open image, the inverse branch is just `Φ.symm` restricted to that image.
      refine (ContMDiffAt.subtypeVal_comp_iff U (fun z : V ↦ e.symm z) y).1 ?_
      refine (contMDiffAt_subtype_iff (U := V) (f := Φ.symm) (x := y)).2 ?_
      rcases y.2 with ⟨x, hx, hy⟩
      have hCont :
          ContMDiffAt J I ∞ Φ.symm (Φ x) := by
        exact Φ.contMDiffOn_invFun.contMDiffAt
          (Φ.open_target.mem_nhds (Φ.map_source (hsub hx)))
      simpa [hy] using hCont
  refine ⟨V, Ψ, ?_⟩
  intro x
  rfl

namespace IsLocalDiffeomorphAt

/-- **Math.** A smooth local diffeomorphism at a point restricts to a diffeomorphism between
connected open neighborhoods, obtained by passing to the connected component of a local source
neighborhood. -/
theorem exists_connected_open_diffeomorph
    [LocallyConnectedSpace M] {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ (U : Set M) ∧ IsConnected (U : Set M) ∧
      ∃ V : TopologicalSpace.Opens N, f x ∈ (V : Set N) ∧ IsConnected (V : Set N) ∧
        ∃ Φ : U ≃ₘ⟮I, J⟯ V, ∀ y : U, (Φ y : N) = f y := by
  rcases hf with ⟨Φ₀, hx, hEq⟩
  let s : Set M := connectedComponentIn Φ₀.source x
  have hs_open : IsOpen s := Φ₀.open_source.connectedComponentIn
  have hx_mem : x ∈ s := mem_connectedComponentIn hx
  have hs_subset : s ⊆ Φ₀.source := connectedComponentIn_subset _ _
  have hs_connected : IsConnected s := isConnected_connectedComponentIn_iff.mpr hx
  obtain ⟨V, Φ, hΦ⟩ :=
    partialDiffeomorph_diffeomorph_image_of_open_subset (I := I) (J := J) Φ₀ hs_open hs_subset
  let U : TopologicalSpace.Opens M := ⟨s, hs_open⟩
  have hfx_mem : f x ∈ (V : Set N) := by
    have hΦx : (Φ ⟨x, hx_mem⟩ : N) = f x := by
      rw [hΦ]
      exact (hEq (hs_subset hx_mem)).symm
    exact hΦx.symm ▸ (Φ ⟨x, hx_mem⟩).2
  have hV_connected : IsConnected (V : Set N) := by
    letI : ConnectedSpace U := isConnected_iff_connectedSpace.mp hs_connected
    letI : ConnectedSpace V := (Φ.toHomeomorph.connectedSpace_iff).1 inferInstance
    exact isConnected_iff_connectedSpace.mpr inferInstance
  refine ⟨U, hx_mem, hs_connected, V, hfx_mem, hV_connected, Φ, ?_⟩
  intro y
  rw [hΦ]
  exact (hEq (hs_subset y.2)).symm

end IsLocalDiffeomorphAt

end ConnectedNeighborhoods

section SourceSpecialization

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- **Math.** Inverse function theorem for boundaryless Euclidean-model manifolds: if `F : M → N`
is smooth and its manifold derivative at `p` is invertible, then `F` restricts to a diffeomorphism
between connected open neighborhoods of `p` and `F p`. In the Euclidean-model setting the required
interior-point hypothesis is automatic. -/
theorem exists_connected_open_neighborhoods_diffeomorph_of_mfderiv_isInvertible
    {F : M → N} {p : M} (hF : ContMDiff I_m I_n ∞ F)
    (hFp : (mfderiv I_m I_n F p).IsInvertible) :
    ∃ U : TopologicalSpace.Opens M, p ∈ (U : Set M) ∧ IsConnected (U : Set M) ∧
      ∃ V : TopologicalSpace.Opens N, F p ∈ (V : Set N) ∧ IsConnected (V : Set N) ∧
        ∃ Φ : U ≃ₘ⟮I_m, I_n⟯ V, ∀ x : U, (Φ x : N) = F x := by
  -- The hypothesis is global smoothness `ContMDiff`, not a pointwise `ContMDiffAt`.
  let _ : LocallyConnectedSpace (EuclideanSpace ℝ (Fin m)) := inferInstance
  let _ : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin m)) M
  have hLocal : IsLocalDiffeomorphAt I_m I_n ∞ F p := by
    -- In Euclidean-model manifolds every point is interior, so the interior-point theorem applies.
    exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
      (I := I_m) (J := I_n) (n := ∞) (by simp) BoundarylessManifold.isInteriorPoint hF hFp
  -- Shrink the local source neighborhood to its connected component and transport the target along
  -- the induced diffeomorphism.
  exact IsLocalDiffeomorphAt.exists_connected_open_diffeomorph hLocal

end SourceSpecialization

section CompositionCharacterizations

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uF} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uG} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type*} [TopologicalSpace H'']
variable {K : ModelWithCorners 𝕜 E'' H''}
variable {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

/-- **Math.** Left-composition with a smooth local diffeomorphism `F` both preserves and detects
smoothness: for a continuous `G`, the map `G` is smooth iff `F ∘ G` is smooth. -/
theorem smooth_iff_comp_left_of_isLocalDiffeomorph
    {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) {G : P → M} (hG : Continuous G) :
    ContMDiff K I ∞ G ↔ ContMDiff K J ∞ (F ∘ G) := by
  constructor
  · intro h
    exact hF.contMDiff.comp h
  · intro h p
    -- Continuity of `G` keeps us inside a source neighborhood where `F` has a smooth local inverse,
    -- and there `G` is locally `localInverse ∘ (F ∘ G)`.
    have hFp : IsLocalDiffeomorphAt I J ∞ F (G p) := hF (G p)
    have hlocal :
        ContMDiffAt K I ∞ (hFp.localInverse ∘ (F ∘ G)) p :=
      hFp.localInverse_contMDiffAt.comp p (h p)
    have heq : (hFp.localInverse ∘ (F ∘ G)) =ᶠ[𝓝 p] G := by
      simpa [Function.comp_assoc] using
        hFp.localInverse_eventuallyEq_left.comp_tendsto hG.continuousAt
    exact hlocal.congr_of_eventuallyEq heq.symm

/-- **Math.** Right-composition with a surjective smooth local diffeomorphism `F` both preserves and
detects smoothness: the map `G` is smooth iff `G ∘ F` is smooth. -/
theorem smooth_iff_comp_right_of_surjective_isLocalDiffeomorph
    {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) (hFs : Function.Surjective F) {G : N → P} :
    ContMDiff J K ∞ G ↔ ContMDiff I K ∞ (G ∘ F) := by
  constructor
  · intro h
    exact h.comp hF.contMDiff
  · intro h y
    -- For each `y`, choose `x` with `F x = y`; a smooth local inverse to `F` at `x` writes `G`
    -- locally near `y` as `(G ∘ F) ∘ localInverse`.
    obtain ⟨x, rfl⟩ := hFs y
    have hFx : IsLocalDiffeomorphAt I J ∞ F x := hF x
    have hlocal :
        ContMDiffAt J K ∞ ((G ∘ F) ∘ hFx.localInverse) (F x) :=
      ContMDiffAt.comp_of_eq (h x) hFx.localInverse_contMDiffAt
        (hFx.localInverse_left_inv hFx.localInverse_mem_target)
    have heq : ((G ∘ F) ∘ hFx.localInverse) =ᶠ[𝓝 (F x)] G := by
      simpa [Function.comp_assoc] using hFx.localInverse_eventuallyEq_right.fun_comp G
    exact hlocal.congr_of_eventuallyEq heq.symm

end CompositionCharacterizations

end Manifold
