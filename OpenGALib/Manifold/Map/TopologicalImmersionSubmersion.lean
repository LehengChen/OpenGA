import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Topological immersions and submersions

Point-set precursors of the smooth immersion/submersion theory: the two
local-shape conditions a continuous map can satisfy, stated purely on
`TopologicalSpace`. They isolate exactly the topological content that the
smooth versions later refine, so nothing here mentions charts or derivatives.

The development is layered by what each notion is built from:

1. **Local sections** — `IsLocalSection` is the shared building block: a
   continuous right inverse of `π` over an open subset of the base. It is the
   reusable payload behind submersions and the bridge to global sections
   (`Function.RightInverse`).
2. **Immersions** — `IsTopologicalImmersion` asks each point to have a
   neighborhood on which the map is a topological embedding. The defining data
   force continuity, and every embedding is an immersion.
3. **Submersions** — `IsTopologicalSubmersion` asks each source point to lie on
   a continuous local section through its image. This is strong enough to make
   the map open, hence a quotient map when surjective, and every local
   homeomorphism is a submersion.

## Main definitions

* `Manifold.IsLocalSection` — a continuous map `σ` over an open set `U` is a
  section of `π` when `π ∘ σ` is the inclusion `U → N`.
* `Manifold.IsTopologicalImmersion` — locally a topological embedding around
  every source point.
* `Manifold.IsTopologicalSubmersion` — continuous, with a continuous local
  section through every source point.

## Main results

* `Manifold.IsTopologicalImmersion.continuous` — an immersion is continuous.
* `Manifold.IsTopologicalImmersion.of_isEmbedding` — every embedding is an
  immersion.
* `Manifold.IsTopologicalSubmersion.isOpenMap` — a submersion is an open map.
* `Manifold.IsTopologicalSubmersion.isQuotientMap` — a surjective submersion is
  a quotient map.
* `Manifold.IsTopologicalSubmersion.of_isLocalHomeomorph` — every local
  homeomorphism is a submersion.

Provenance: SmoothManifoldsLee a5f308c — Definition_4_25_extra_1, Definition_4_24_extra_2, Definition_4_25_extra_2.
-/

universe u v

open TopologicalSpace Topology
open scoped Topology

namespace Manifold

section LocalSection

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-- **Math.** A *local section* of a continuous map `π : C(M, N)` over an open
subset `U` of the base is a continuous map `σ : C(U, M)` whose composite with
`π` is the inclusion `U → N`. A global section is the special case `U = ⊤`. -/
def IsLocalSection (π : C(M, N)) (U : Opens N) (σ : C(U, M)) : Prop :=
  ∀ x : U, π (σ x) = x

namespace IsLocalSection

/-- **Math.** A local section satisfies the section equation `π (σ x) = x` at
each point `x` of its open domain. -/
theorem apply_eq {π : C(M, N)} {U : Opens N} {σ : C(U, M)}
    (hσ : IsLocalSection π U σ) (x : U) : π (σ x) = x :=
  hσ x

end IsLocalSection

/-- **Math.** A global section `σ : C(N, M)` of `π`, i.e. a continuous right
inverse, restricts to a local section over the whole base `⊤`. -/
theorem isLocalSection_restrict_top_of_rightInverse {π : C(M, N)} {σ : C(N, M)}
    (hσ : Function.RightInverse σ π) :
    IsLocalSection π ⊤ (σ.restrict (⊤ : Set N)) := by
  intro x
  simpa using hσ.eq (x : N)

end LocalSection

section Immersion

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **Math.** A *topological immersion* is a map such that every point of the
source has a neighborhood on which the restricted map is a topological
embedding. The continuity clause is omitted because it is forced by the local
embedding condition. -/
@[mk_iff]
structure IsTopologicalImmersion (f : X → Y) : Prop where
  /-- Every point admits a neighborhood on which the map is a topological embedding. -/
  local_embedding (x : X) : ∃ s : Set X, s ∈ 𝓝 x ∧ IsEmbedding (s.restrict f)

namespace IsTopologicalImmersion

/-- **Math.** A topological immersion is continuous. -/
theorem continuous (hf : IsTopologicalImmersion f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨s, hs, hs_emb⟩ := hf.local_embedding x
  have hcontOn : ContinuousOn f s := by
    rw [continuousOn_iff_continuous_restrict]
    simpa using hs_emb.continuous
  exact hcontOn.continuousAt hs

instance (hf : IsTopologicalImmersion f) : Continuous f := hf.continuous

/-- **Math.** Every topological embedding is, in particular, a topological
immersion: at each point the neighborhood `univ` already restricts to the
embedding. -/
theorem of_isEmbedding (hf : IsEmbedding f) : IsTopologicalImmersion f := by
  refine ⟨fun _ ↦ ?_⟩
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  simpa [Set.restrict_eq] using hf.comp IsEmbedding.subtypeVal

end IsTopologicalImmersion

end Immersion

section Submersion

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Math.** A *topological submersion* is a continuous map such that every
point of the source lies on a continuous local section through its image. -/
@[mk_iff]
structure IsTopologicalSubmersion (π : X → Y) : Prop where
  /-- A topological submersion is continuous. -/
  continuous : Continuous π
  /-- Every source point lies on a continuous local section defined near its image. -/
  local_section (x : X) :
    ∃ U : Opens Y, ∃ hxU : π x ∈ U, ∃ σ : C(U, X),
      IsLocalSection (⟨π, continuous⟩ : C(X, Y)) U σ ∧ σ ⟨π x, hxU⟩ = x

namespace IsTopologicalSubmersion

variable {π : X → Y}

instance (hπ : IsTopologicalSubmersion π) : Continuous π := hπ.continuous

/-- **Math.** A topological submersion is an open map: the local section through
each preimage point pushes an open neighborhood into the image. -/
theorem isOpenMap (hπ : IsTopologicalSubmersion π) : IsOpenMap π := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨x, hxW, rfl⟩
  rcases hπ.local_section x with ⟨U, hxU, σ, hσ, hσx⟩
  let V : Set U := σ ⁻¹' W
  have hV : IsOpen V := hW.preimage σ.continuous
  have hV_image : IsOpen (((↑) : U → Y) '' V) := U.2.isOpenMap_subtype_val V hV
  have hV_subset : ((↑) : U → Y) '' V ⊆ π '' W := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨σ u, hu, IsLocalSection.apply_eq hσ u⟩
  have hy_image : π x ∈ ((↑) : U → Y) '' V := by
    refine ⟨⟨π x, hxU⟩, ?_, rfl⟩
    simpa [V, hσx] using hxW
  exact Filter.mem_of_superset (hV_image.mem_nhds hy_image) hV_subset

/-- **Math.** A surjective topological submersion is a quotient map. -/
theorem isQuotientMap (hπ : IsTopologicalSubmersion π) (h_surj : Function.Surjective π) :
    IsQuotientMap π :=
  hπ.isOpenMap.isQuotientMap hπ.continuous h_surj

/-- **Math.** Every local homeomorphism is a topological submersion: a partial
homeomorphism agreeing with `π` near `x` has an open target containing `π x`,
and its inverse is a continuous local section sending `π x` back to `x`. -/
theorem of_isLocalHomeomorph (hπ : IsLocalHomeomorph π) :
    IsTopologicalSubmersion π := by
  refine { continuous := hπ.continuous, local_section := ?_ }
  intro x
  obtain ⟨e, hxe, hfe⟩ := hπ x
  let U : Opens Y := ⟨e.target, e.open_target⟩
  let σ : C(U, X) :=
    ⟨Set.restrict e.target e.symm,
      continuousOn_iff_continuous_restrict.mp e.continuousOn_symm⟩
  have hxU : π x ∈ U := by
    show π x ∈ e.target
    rw [hfe]
    exact e.map_source hxe
  refine ⟨U, hxU, σ, ?_, ?_⟩
  · intro y
    show π (e.symm y) = y
    rw [hfe]
    exact e.right_inv y.2
  · show e.symm (π x) = x
    rw [hfe]
    exact e.left_inv hxe

end IsTopologicalSubmersion

end Submersion

end Manifold
