import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Immersed and embedded submanifolds

Submanifold structures on a smooth manifold `M`, layered by how much of the
ambient topology they pin down so downstream code takes only the strength it
needs:

1. **Owner object** — `ImmersedSubmanifold` bundles a boundaryless smooth
   manifold with an injective smooth immersion into `M`. It is the reusable
   carrier: it does *not* assume the chosen topology agrees with the subspace
   topology, so it covers genuinely immersed (non-embedded) images. The
   codimension and hypersurface predicates live here, computed from the model
   spaces alone.
2. **Bridges in** — a smooth embedding, or any injective smooth immersion,
   canonically yields an `ImmersedSubmanifold`; these are the standard
   constructors feeding the owner object.
3. **Embedded class** — `IsEmbeddedSubmanifold` is the `Prop`-valued strengthening
   for a subset `S ⊆ M`: the subtype carries a boundaryless smooth structure and
   its inclusion is a smooth embedding. It records the same codimension data and
   views back into the owner object.
4. **Topology comparison** — for an immersed submanifold the chosen topology is
   always finer than the ambient subspace topology, with equality exactly when the
   inclusion is a topological embedding.
5. **Restriction** — a smooth map landing inside an embedded submanifold is smooth
   into the submanifold; this codomain-restriction is the canonical way to obtain
   maps into `S`.

## Main definitions

* `Manifold.ImmersedSubmanifold` — boundaryless manifold with an injective smooth immersion into `M`.
* `Manifold.ImmersedSubmanifold.carrier` — the underlying subset (range of the inclusion).
* `Manifold.ImmersedSubmanifold.codimension` — ambient dimension minus submanifold dimension.
* `Manifold.IsEmbeddedSubmanifold` — a subset whose subtype is a boundaryless manifold with smoothly
  embedded inclusion.

## Main results

* `Manifold.IsSmoothEmbedding.toImmersedSubmanifold` — a smooth embedding gives an immersed submanifold.
* `Manifold.ImmersedSubmanifold.continuous_inclusion` — the inclusion is continuous.
* `Manifold.ImmersedSubmanifold.givenTopology_le_subspaceTopology` — the chosen topology is finer
  than the ambient subspace topology.
* `Manifold.ImmersedSubmanifold.subspaceTopology_le_givenTopology_iff_isEmbedding` — equality holds
  iff the inclusion is a topological embedding.
* `Manifold.IsSmoothEmbedding.contMDiff_toSubtype` — a smooth map into the image of a smooth
  embedding is smooth as a map to the subtype.
* `Manifold.contMDiff_toSubtype_of_isEmbeddedSubmanifold` — codomain restriction of a smooth map
  to an embedded submanifold is smooth.

Provenance: SmoothManifoldsLee a5f308c — Definition_5_31_extra_1, Definition_5_28_extra_1, Exercise_5_20, Corollary_5_30.
-/

open Topology
open scoped ContDiff Manifold

universe u v w u1 u2 u3

namespace Manifold

section ImmersedSubmanifolds

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]

section

variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type u2) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- **Math.** An *immersed submanifold* of a smooth manifold `M` is a boundaryless smooth manifold
together with an injective smooth immersion into `M`; its underlying subset is the range of the
inclusion map. -/
structure ImmersedSubmanifold where
  /-- The model vector space for the boundaryless manifold structure on the immersed submanifold. -/
  ModelSpace : Type u1
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The type carrying the chosen topology and smooth structure on the immersed submanifold. -/
  domain : Type u3
  /-- The chosen topology on the immersed submanifold. -/
  instTopologicalSpaceDomain : TopologicalSpace domain
  /-- The chosen atlas on the immersed submanifold. -/
  instChartedSpaceDomain : ChartedSpace ModelSpace domain
  /-- The immersed submanifold is a boundaryless smooth manifold. -/
  instIsManifoldDomain :
    IsManifold (modelWithCornersSelf 𝕜 ModelSpace) (⊤ : WithTop ℕ∞) domain
  /-- The inclusion map of the immersed submanifold into the ambient manifold. -/
  inclusion : domain → M
  /-- The inclusion map is injective, so its image is a genuine subset of the ambient manifold. -/
  inclusion_injective : Function.Injective inclusion
  /-- The inclusion map is a smooth immersion. -/
  inclusion_isImmersion :
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) I (⊤ : WithTop ℕ∞) inclusion

end

attribute [instance] ImmersedSubmanifold.instNormedAddCommGroupModelSpace
attribute [instance] ImmersedSubmanifold.instNormedSpaceModelSpace
attribute [instance] ImmersedSubmanifold.instTopologicalSpaceDomain
attribute [instance] ImmersedSubmanifold.instChartedSpaceDomain
attribute [instance] ImmersedSubmanifold.instIsManifoldDomain

namespace ImmersedSubmanifold

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- **Math.** An immersed submanifold coerces to the boundaryless manifold type carrying its chosen
smooth structure. -/
instance : CoeSort (ImmersedSubmanifold I M) (Type u3) where
  coe S := S.domain

/-- **Math.** The coerced type underlying an immersed submanifold carries its chosen topology. -/
instance (S : ImmersedSubmanifold I M) : TopologicalSpace S :=
  S.instTopologicalSpaceDomain

/-- **Math.** The underlying subset of an immersed submanifold is the range of its inclusion into
the ambient manifold. -/
def carrier (S : ImmersedSubmanifold I M) : Set M :=
  Set.range S.inclusion

/-- **Math.** The codimension of an immersed submanifold is the ambient dimension minus the
dimension of its boundaryless manifold structure. -/
noncomputable def codimension [FiniteDimensional 𝕜 E] (S : ImmersedSubmanifold I M)
    [FiniteDimensional 𝕜 S.ModelSpace] : ℕ :=
  Module.finrank 𝕜 E - Module.finrank 𝕜 S.ModelSpace

/-- **Math.** An immersed submanifold is a hypersurface when its codimension is `1`. -/
noncomputable def IsHypersurface [FiniteDimensional 𝕜 E] (S : ImmersedSubmanifold I M)
    [FiniteDimensional 𝕜 S.ModelSpace] : Prop :=
  S.codimension = 1

end ImmersedSubmanifold

namespace IsSmoothEmbedding

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type u3} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]
variable {f : N → M}

/-- **Math.** A smooth embedding of a boundaryless manifold into `M` canonically determines an
immersed submanifold of `M`. -/
def toImmersedSubmanifold
    (hf : IsSmoothEmbedding (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) f) :
    ImmersedSubmanifold I M where
  ModelSpace := E'
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := N
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := f
  inclusion_injective := hf.isEmbedding.injective
  inclusion_isImmersion := hf.isImmersion

end IsSmoothEmbedding

namespace IsImmersion

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type u3} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]
variable {f : N → M}

/-- **Math.** An injective smooth immersion of a boundaryless manifold into `M` canonically
determines an immersed submanifold of `M`. -/
def toImmersedSubmanifold
    (hf : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) f)
    (hf_injective : Function.Injective f) :
    ImmersedSubmanifold I M where
  ModelSpace := E'
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := N
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := f
  inclusion_injective := hf_injective
  inclusion_isImmersion := hf

end IsImmersion

namespace ImmersedSubmanifold

section Topology

variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M]

/-- **Math.** The inclusion of an immersed submanifold into the ambient manifold is continuous. -/
theorem continuous_inclusion (S : ImmersedSubmanifold I M) : Continuous S.inclusion := by
  rw [continuous_iff_continuousAt]
  intro x
  let h := S.inclusion_isImmersion.isImmersionAt x
  have hdomChart_source : h.domChart.source ∈ 𝓝 x :=
    IsOpen.mem_nhds h.domChart.open_source h.mem_domChart_source
  have hsource : S.inclusion ⁻¹' h.codChart.source ∈ 𝓝 x :=
    Filter.mem_of_superset hdomChart_source h.source_subset_preimage_source
  have hEqOn :
      Set.EqOn ((h.codChart.extend I) ∘ S.inclusion)
        (h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement)))
        h.domChart.source := by
    intro y hy
    have hy_target :
        h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y ∈
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target :=
      (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, OpenPartialHomeomorph.extend_coe, h.domChart.left_inv hy] using
      h.writtenInCharts hy_target
  have hEq :
      ((h.codChart.extend I) ∘ S.inclusion) =ᶠ[𝓝 x]
        h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement)) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hcont_rhs :
      ContinuousAt
        (h.equiv ∘ fun y : S ↦
          (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement))) x := by
    have hcont_dom :
        ContinuousAt (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) x :=
      h.domChart.continuousAt_extend h.mem_domChart_source
    have hcont_pair :
        ContinuousAt
          (fun y : S ↦
            (h.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) y, (0 : h.complement))) x :=
      hcont_dom.prodMk continuousAt_const
    simpa [Function.comp] using ContinuousAt.comp h.equiv.continuousAt hcont_pair
  have hcont_extend : ContinuousAt ((h.codChart.extend I) ∘ S.inclusion) x :=
    hcont_rhs.congr hEq.symm
  have hcont_chart : ContinuousAt (h.codChart ∘ S.inclusion) x := by
    convert I.continuousAt_symm.comp hcont_extend using 1
    funext y
    simp [Function.comp]
  exact (h.codChart.continuousAt_iff_continuousAt_comp_left hsource).2 hcont_chart

/-- **Math.** The topology carried by an immersed submanifold is finer than the ambient subspace
topology pulled back along its inclusion map. -/
theorem givenTopology_le_subspaceTopology (S : ImmersedSubmanifold I M) :
    (inferInstance : TopologicalSpace S) ≤ TopologicalSpace.induced S.inclusion inferInstance :=
  S.continuous_inclusion.le_induced

/-- **Math.** The ambient subspace topology on the image of an immersed submanifold is finer than
the chosen topology exactly when the inclusion is an embedding. -/
theorem subspaceTopology_le_givenTopology_iff_isEmbedding (S : ImmersedSubmanifold I M) :
    TopologicalSpace.induced S.inclusion inferInstance ≤ (inferInstance : TopologicalSpace S) ↔
      IsEmbedding S.inclusion := by
  constructor
  · intro hle
    exact ⟨⟨le_antisymm S.givenTopology_le_subspaceTopology hle⟩, S.inclusion_injective⟩
  · intro hEmbedding
    rw [hEmbedding.eq_induced]

end Topology

end ImmersedSubmanifold

end ImmersedSubmanifolds

section EmbeddedSubmanifolds

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type u3} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞ω) S]

/-- **Math.** A subset `S ⊆ M` is an *embedded submanifold* if the subtype `S` inherits its
subspace topology, carries a boundaryless smooth manifold structure, and the inclusion `S ↪ M` is a
smooth embedding. Some authors call this a regular submanifold. -/
class IsEmbeddedSubmanifold : Prop extends BoundarylessManifold J S where
  /-- The subtype inclusion of the embedded submanifold into the ambient manifold is smooth. -/
  isSmoothEmbedding_subtype_val :
    IsSmoothEmbedding J I (⊤ : ℕ∞ω) (Subtype.val : S → M)

/-- **Math.** The empty subset is an embedded submanifold for any chosen smooth manifold structure on
the empty subtype: the empty set carries every dimension. -/
instance isEmbeddedSubmanifold_empty [ChartedSpace H' (∅ : Set M)]
    [IsManifold J (⊤ : ℕ∞ω) (∅ : Set M)] :
    IsEmbeddedSubmanifold I J (∅ : Set M) where
  toBoundarylessManifold := by
    refine ⟨fun x ↦ False.elim x.2⟩
  isSmoothEmbedding_subtype_val := by
    refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
    exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

end EmbeddedSubmanifolds

section EmbeddedToImmersedBridge

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (S : Set M)
variable [ChartedSpace E' S] [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

/-- **Math.** When the embedded submanifold is modeled on the boundaryless vector-space model, its
subtype inclusion canonically defines the corresponding `ImmersedSubmanifold` owner. -/
abbrev toImmersedSubmanifold
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S) :
    Manifold.ImmersedSubmanifold I M :=
  hS.isSmoothEmbedding_subtype_val.toImmersedSubmanifold

end IsEmbeddedSubmanifold

end EmbeddedToImmersedBridge

section EmbeddedSubmanifoldCodimension

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type u3} [TopologicalSpace H']
variable (J : ModelWithCorners 𝕜 E' H') (S : Set M)
variable [ChartedSpace H' S] [IsManifold J (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- **Math.** The codimension of an embedded submanifold is the ambient dimension minus the
dimension of its boundaryless manifold structure. -/
noncomputable def codimension (_ : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] : ℕ :=
  Module.finrank 𝕜 E - Module.finrank 𝕜 E'

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- **Math.** The codimension is the difference of the model-space dimensions. -/
lemma codimension_eq_finrank_sub (hS : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.codimension = Module.finrank 𝕜 E - Module.finrank 𝕜 E' := rfl
attribute [simp] codimension_eq_finrank_sub

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- **Math.** An embedded hypersurface is an embedded submanifold of codimension `1`. -/
def IsHypersurface (hS : IsEmbeddedSubmanifold I J S) [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 E'] : Prop :=
  hS.codimension = 1

omit [IsManifold I (⊤ : ℕ∞ω) M] [IsManifold J (⊤ : ℕ∞ω) S] in
/-- **Math.** An embedded submanifold is a hypersurface exactly when its codimension is `1`. -/
lemma isHypersurface_iff (hS : IsEmbeddedSubmanifold I J S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.IsHypersurface ↔ hS.codimension = 1 := Iff.rfl

end IsEmbeddedSubmanifold

end EmbeddedSubmanifoldCodimension

section EmbeddedToImmersedCodimension

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
variable (I : ModelWithCorners 𝕜 E H) [IsManifold I (⊤ : ℕ∞ω) M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable (S : Set M)
variable [ChartedSpace E' S] [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : ℕ∞ω) S]

namespace IsEmbeddedSubmanifold

instance instFiniteDimensionalToImmersedSubmanifoldModelSpace
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S)
    [FiniteDimensional 𝕜 E'] :
    FiniteDimensional 𝕜 hS.toImmersedSubmanifold.ModelSpace := by
  simpa [toImmersedSubmanifold, Manifold.IsSmoothEmbedding.toImmersedSubmanifold] using
    (inferInstance : FiniteDimensional 𝕜 E')

omit [IsManifold I (⊤ : ℕ∞ω) M] in
/-- **Math.** In the self-model case, the source-facing codimension agrees definitionally with the
core immersed-submanifold codimension. -/
@[simp] lemma toImmersedSubmanifold_codimension
    (hS : IsEmbeddedSubmanifold I (modelWithCornersSelf 𝕜 E') S)
    [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 E'] :
    hS.toImmersedSubmanifold.codimension = hS.codimension := rfl

end IsEmbeddedSubmanifold

end EmbeddedToImmersedCodimension

section RestrictingMapsToEmbeddedSubmanifolds

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type u2} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type u1} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type u3} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]
variable {E'' : Type u} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H'' : Type w} [TopologicalSpace H'']
variable {N : Type u2} [TopologicalSpace N] [ChartedSpace H'' N]
variable {K : ModelWithCorners 𝕜 E'' H''} [IsManifold K ⊤ N]

namespace IsSmoothEmbedding

/-- **Math.** The codomain-restricted map is continuous because the embedded submanifold carries the
induced subspace topology. -/
lemma continuous_codRestrict
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    Continuous (Set.codRestrict F S hFS) := by
  refine hS.isEmbedding.isInducing.continuous_iff.2 ?_
  simpa [Function.comp] using hF.continuous

/-- **Math.** In immersion charts for the inclusion `S ↪ M`, the restricted map to `S` is recovered
from the ambient chart expression by the projected inverse equivalence. -/
lemma writtenInCharts_codRestrict_eqOn
    {F : N → M} (hFS : ∀ x, F x ∈ S) {y : S}
    (hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y) :
    Set.EqOn ((hImm.domChart.extend J) ∘ Set.codRestrict F S hFS)
      ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
      ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) := by
  intro z hz
  have hz_target :
      hImm.domChart.extend J (Set.codRestrict F S hFS z) ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
    (congrArg (fun v => Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm

/-- **Math.** Each pointwise codomain restriction is smooth in the embedded manifold structure. -/
lemma contMDiffAt_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) (x : N) :
    ContMDiffAt K J ⊤ (Set.codRestrict F S hFS) x := by
  let fS : N → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt J I ⊤ (Subtype.val : S → M) y := hS.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph N H'' := chartAt H'' x
  let x' : E'' := e.extend K x
  have hcont : ContinuousAt fS x := (continuous_codRestrict hS hF hFS).continuousAt
  have hx : x ∈ e.source := mem_chart_source H'' x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
    (e' := hImm.domChart) (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas
    hx hy,
    continuousWithinAt_univ, Set.preimage_univ, Set.univ_inter]
  refine ⟨hcont, ?_⟩
  have hambient :
      ContDiffWithinAt 𝕜 ⊤ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    simpa [Set.preimage_univ] using
      ((contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ) (e := e)
        (e' := hImm.codChart) (IsManifold.chart_mem_maximalAtlas x)
        hImm.codChart_mem_maximalAtlas hx hy').1 (hF.contMDiffAt.contMDiffWithinAt)).2
  have hproj :
      ContDiff 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) := by
    simpa using contDiff_fst.comp hImm.equiv.symm.contDiff
  have hprojWithin :
      ContDiffWithinAt 𝕜 ⊤ (fun v ↦ (hImm.equiv.symm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 ⊤
        ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ 𝓝 x := by
    have : hImm.domChart.source ∈ 𝓝 (fS x) :=
      hImm.domChart.open_source.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ 𝓝[Set.range K] x' := by
    simpa [e, x', nhdsWithin_univ] using
      e.extend_preimage_mem_nhdsWithin (I := K) (s := Set.univ) (t := fS ⁻¹' hImm.domChart.source)
        hx (by simpa [nhdsWithin_univ] using hsource_mem)
  have heq :
      ((hImm.domChart.extend J) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[𝓝[Set.range K] x']
          ((fun v ↦ (hImm.equiv.symm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq := writtenInCharts_codRestrict_eqOn (F := F) (hFS := hFS) (hImm := hImm)
    simpa [Function.comp] using hchartEq hz
  have hx'_target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

/-- **Math.** If `Subtype.val : S → M` is a smooth embedding and a smooth map `F : N → M` has image
in `S`, then `F` is smooth as a map to `S`. This restriction-to-subtype bridge is the canonical
input for the codomain-restriction corollary and its boundary-ambient variant. -/
theorem contMDiff_toSubtype
    (hS : IsSmoothEmbedding J I ⊤ (Subtype.val : S → M))
    {F : N → M} (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  intro x
  exact contMDiffAt_toSubtype hS hF hFS x

end IsSmoothEmbedding

/-- **Math.** Every smooth map `F : N → M` whose image is contained in an embedded submanifold
`S ⊆ M` is smooth as a map from `N` to `S`. -/
theorem contMDiff_toSubtype_of_isEmbeddedSubmanifold {F : N → M}
    [IsEmbeddedSubmanifold I J S]
    (hF : ContMDiff K I ⊤ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff K J ⊤ (Set.codRestrict F S hFS) := by
  simpa using
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val.contMDiff_toSubtype hF hFS

end RestrictingMapsToEmbeddedSubmanifolds

end Manifold
