import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic
import OpenGALib.Manifold.Covering.SmoothCoveringMap

/-!
# Proper local diffeomorphisms are covering maps

A criterion promoting a smooth local diffeomorphism to a smooth covering map
under a properness assumption, built up from point-set facts about fibers:

1. **Fiber discreteness** — a local diffeomorphism is a local homeomorphism, so
   each of its fibers is discrete. This needs only the local-homeomorphism API
   and is stated on the bare topological spaces.
2. **Fiber finiteness** — properness makes fibers compact, and a compact
   discrete set is finite; this is what lets the covering criterion build evenly
   covered neighborhoods.
3. **Surjectivity** — the range of a proper local diffeomorphism is clopen and
   nonempty, hence all of a preconnected target.
4. **Covering conclusion** — the closed-map covering criterion assembles finite
   fibers and local branches into a smooth covering map, reusing the core
   `Manifold.IsSmoothCoveringMap` predicate.

## Main results

* `Manifold.isSmoothCoveringMap_of_proper_localDiffeomorph` — a proper smooth
  local diffeomorphism from a nonempty Hausdorff source to a preconnected target
  is a smooth covering map.

Provenance: SmoothManifoldsLee a5f308c — Proposition_4_46.
-/

open scoped Manifold ContDiff

universe uK uVE uVM uHE uHM uE uM

section

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable (IE : ModelWithCorners K VE HE) (IM : ModelWithCorners K VM HM)
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E] [T2Space E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable [Nonempty E] [PreconnectedSpace M]

namespace Manifold

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- **Math.** A local diffeomorphism provides an open partial homeomorphism agreeing
with `π` through each source point. -/
lemma exists_openPartialHomeomorph_eq_of_localDiffeomorph {π : E → M}
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (e : E) :
    ∃ φ : OpenPartialHomeomorph E M, e ∈ φ.source ∧ φ = π := by
  obtain ⟨φ, hφ, hπφ⟩ := hlocal.isLocalHomeomorph e
  exact ⟨φ, hφ, hπφ.symm⟩

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- **Math.** Every fiber of a local diffeomorphism is a discrete subset. -/
lemma fiber_is_discrete_of_local_diffeomorph {π : E → M}
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : M) : IsDiscrete (π ⁻¹' {x}) := by
  refine IsDiscrete.of_openPartialHomeomorph π subset_rfl ?_
  intro e he
  exact exists_openPartialHomeomorph_eq_of_localDiffeomorph (IE := IE) (IM := IM) hlocal e

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- **Math.** Properness upgrades the discrete fibers of a local diffeomorphism to
finite fibers. -/
lemma fiber_finite_of_proper_local_diffeomorph {π : E → M} (hproper : IsProperMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : M) : (π ⁻¹' {x}).Finite := by
  refine (hproper.isCompact_preimage isCompact_singleton).finite ?_
  exact fiber_is_discrete_of_local_diffeomorph (IE := IE) (IM := IM) hlocal x

omit [T2Space E] in
/-- **Math.** The range of a proper local diffeomorphism is nonempty, open, and
closed, hence equals the whole preconnected target. -/
lemma surjective_of_nonempty_preconnected_open_closed_range {π : E → M} (hproper : IsProperMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) : Function.Surjective π := by
  have hrange : (Set.univ : Set M) ⊆ Set.range π := by
    refine isPreconnected_univ.subset_left_of_subset_union hlocal.isOpen_range
      hproper.isClosed_range.isOpen_compl disjoint_compl_right ?_ ?_
    · intro x
      simp
    · rcases Set.range_nonempty π with ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
  rw [← Set.range_eq_univ]
  exact Set.eq_univ_of_univ_subset hrange

/-- **Math.** A proper smooth local diffeomorphism from a nonempty Hausdorff source
to a preconnected target is a smooth covering map; the source-connectedness
hypothesis is not needed for this conclusion. -/
theorem isSmoothCoveringMap_of_proper_localDiffeomorph {π : E → M}
    (hproper : IsProperMap π) (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    Manifold.IsSmoothCoveringMap IE IM π := by
  refine ⟨?_, ⟨?_, hlocal⟩⟩
  · rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph ?_ ?_
    · intro x _
      exact fiber_finite_of_proper_local_diffeomorph (IE := IE) (IM := IM) hproper hlocal x
    · intro e _
      exact exists_openPartialHomeomorph_eq_of_localDiffeomorph
        (IE := IE) (IM := IM) hlocal e
  · exact surjective_of_nonempty_preconnected_open_closed_range
      (IE := IE) (IM := IM) hproper hlocal

end Manifold

end
