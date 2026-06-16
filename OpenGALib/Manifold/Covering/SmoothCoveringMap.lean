import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic

/-!
# Smooth covering maps

Anchor definitions for the smooth-covering theory: Mathlib supplies only the
topological notion `IsCoveringMap`, so this is where the smooth refinement
enters the library. The module is layered so downstream covering files import
only the generality they need:

1. **Core predicate** — `IsSmoothCoveringMap` packages a surjective topological
   covering map that is simultaneously a smooth local diffeomorphism. It fixes
   the canonical smoothness exponent at `∞`, the value every later covering
   file aligns to. The projection accessors (`surjective`, `isCoveringMap`,
   `isLocalDiffeomorph`) expose its three components.
2. **Identity cover** — the identity map is the globally trivial one-sheet
   cover and the identity diffeomorphism, so it is the basic example feeding
   `isSmoothCoveringMap_id`. The trivialization is built once and reused.
3. **Universal cover** — `IsUniversalSmoothCoveringMap` strengthens the core
   predicate by asking the total space to be simply connected; on a simply
   connected manifold the identity already witnesses it.

## Main definitions

* `Manifold.IsSmoothCoveringMap` — a surjective smooth local diffeomorphism that
  is a topological covering map.
* `Manifold.IsUniversalSmoothCoveringMap` — a smooth covering map with simply
  connected total space.

## Main results

* `Manifold.isSmoothCoveringMap_id` — the identity map is a smooth covering map.
* `Manifold.isUniversalSmoothCoveringMap_id` — on a simply connected manifold the
  identity is a universal smooth covering map.

Provenance: SmoothManifoldsLee a5f308c — Definition_4_26_extra_1.
-/

open scoped Manifold ContDiff

universe u𝕜 uE uE' uH uH' uM uM'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type uM'} [TopologicalSpace M'] [ChartedSpace H' M']

namespace Manifold

/-- **Math.** A *smooth covering map* `π` between smooth manifolds is a surjective
topological covering map that is also a smooth local diffeomorphism: every sheet
over an evenly covered neighborhood is carried diffeomorphically onto the base
neighborhood. The smoothness exponent is fixed at `∞`. -/
def IsSmoothCoveringMap
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (π : M → M') : Prop :=
  IsCoveringMap π ∧ Function.Surjective π ∧ IsLocalDiffeomorph I I' ∞ π

namespace IsSmoothCoveringMap

/-- **Math.** A smooth covering map is surjective. -/
theorem surjective {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : Function.Surjective π :=
  hπ.2.1

/-- **Math.** A smooth covering map is a topological covering map. -/
theorem isCoveringMap {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsCoveringMap π :=
  hπ.1

/-- **Math.** A smooth covering map is a smooth local diffeomorphism with exponent `∞`. -/
theorem isLocalDiffeomorph
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsSmoothCoveringMap I I' π) : IsLocalDiffeomorph I I' ∞ π :=
  hπ.2.2

end IsSmoothCoveringMap

/-- **Math.** For the identity map, the source of its global one-sheet trivialization
is all of `M`. -/
theorem id_covering_trivialization_source_eq :
    ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).source =
      (id : M → M) ⁻¹' (Set.univ : Set M) := by
  ext x
  simp

/-- **Math.** For the identity map, the target of its global one-sheet trivialization
is the full product `M × PUnit`. -/
theorem id_covering_trivialization_target_eq :
    ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).target =
      (Set.univ : Set M) ×ˢ (Set.univ : Set PUnit.{1}) := by
  ext x
  simp

/-- **Math.** The global trivialization for the identity map projects back to the
identity on the base. -/
theorem id_covering_trivialization_proj_toFun
    (x : M) (_hx : x ∈ ((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph).source) :
    (((Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph x).1) = (id : M → M) x := by
  change (((Equiv.prodPUnit M).symm x).1) = x
  simp [Equiv.prodPUnit_symm_apply]

/-- **Math.** The global one-sheet trivialization of the identity map, exhibiting it
as a trivial cover with fiber `PUnit`. -/
noncomputable def idCoveringTrivialization : Bundle.Trivialization PUnit.{1} (id : M → M) :=
  { toOpenPartialHomeomorph := (Homeomorph.prodPUnit M).symm.toOpenPartialHomeomorph
    baseSet := Set.univ
    open_baseSet := isOpen_univ
    source_eq := id_covering_trivialization_source_eq
    target_eq := id_covering_trivialization_target_eq
    proj_toFun := id_covering_trivialization_proj_toFun }

/-- **Math.** The identity map is a topological covering map: the globally trivial
one-sheet cover. -/
theorem id_isCoveringMap : IsCoveringMap (id : M → M) := by
  refine IsCoveringMap.mk (f := (id : M → M)) (fun _ : M ↦ PUnit.{1})
    (fun _ ↦ idCoveringTrivialization) ?_
  intro x
  simp [idCoveringTrivialization]

/-- **Math.** The identity map is a smooth local diffeomorphism with exponent `∞`. -/
theorem refl_isLocalDiffeomorph_id (I : ModelWithCorners 𝕜 E H) :
    IsLocalDiffeomorph I I ∞ (id : M → M) := by
  simpa using (Diffeomorph.refl I M ∞).isLocalDiffeomorph

/-- **Math.** The identity map is a smooth covering map. -/
theorem isSmoothCoveringMap_id (I : ModelWithCorners 𝕜 E H) :
    IsSmoothCoveringMap I I (id : M → M) :=
  ⟨id_isCoveringMap, Function.surjective_id, refl_isLocalDiffeomorph_id I⟩

/-- **Math.** A *universal smooth covering map* is a smooth covering map whose total
space is simply connected. -/
def IsUniversalSmoothCoveringMap
    (I : ModelWithCorners 𝕜 E H) (I' : ModelWithCorners 𝕜 E' H') (π : M → M') : Prop :=
  IsSmoothCoveringMap I I' π ∧ SimplyConnectedSpace M

namespace IsUniversalSmoothCoveringMap

/-- **Math.** A universal smooth covering map is a smooth covering map. -/
theorem isSmoothCoveringMap
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsUniversalSmoothCoveringMap I I' π) : IsSmoothCoveringMap I I' π :=
  hπ.1

/-- **Math.** The total space of a universal smooth covering map is simply connected. -/
theorem simplyConnectedSpace
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'} {π : M → M'}
    (hπ : IsUniversalSmoothCoveringMap I I' π) : SimplyConnectedSpace M :=
  hπ.2

end IsUniversalSmoothCoveringMap

/-- **Math.** On a simply connected manifold, the identity map is a universal smooth
covering map. -/
theorem isUniversalSmoothCoveringMap_id (I : ModelWithCorners 𝕜 E H) [SimplyConnectedSpace M] :
    IsUniversalSmoothCoveringMap I I (id : M → M) :=
  ⟨isSmoothCoveringMap_id I, inferInstance⟩

end Manifold
