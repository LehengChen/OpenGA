import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Exhaustion functions and local smoothness

Cutoff- and exhaustion-style machinery for non-compact manifolds, layered by
how much structure each piece needs so downstream code imports only the
generality it uses:

1. **Topological base** — `IsExhaustionFunction` is stated on any topological
   space: a continuous real function with compact closed sublevel sets. Its
   consequences (`tendsto_atTop`, `isProperMap`) are purely topological and are
   the reusable interface for proving properness and cocompact decay.
2. **Manifold-local smoothness** — `IsSmoothOn` packages local smooth
   extendability of a map on a subset of a charted space, with an unbundled
   restatement for downstream use.
3. **Existence on manifolds** — `exists_positive_smooth_exhaustion_function`
   builds a positive smooth exhaustion function on any Hausdorff
   `σ`-compact smooth manifold via partition-of-unity gluing; this is the
   payload that supports analysis on non-compact manifolds (L²/Bochner/GMT).
4. **Paracompactness criterion** — `paracompactSpace_of_hasSubordinatePartitionOfUnity`
   recovers paracompactness from the availability of subordinate partitions of
   unity, closing the loop with the existence layer.

## Main definitions

* `Manifold.IsSmoothOn` — a map on a subset is smooth when it locally extends to a smooth map.
* `Manifold.IsExhaustionFunction` — continuous function with compact closed sublevel sets.

## Main results

* `Manifold.isSmoothOn_iff_exists_local_extension` — bundled/unbundled equivalence of `IsSmoothOn`.
* `Manifold.IsExhaustionFunction.tendsto_atTop` — an exhaustion function tends to `+∞` off compact sets.
* `Manifold.IsExhaustionFunction.isProperMap` — an exhaustion function is a proper map.
* `Manifold.Continuous.isExhaustionFunction` — any continuous function on a compact space is an exhaustion function.
* `Manifold.exists_positive_smooth_exhaustion_function` — every Hausdorff `σ`-compact smooth manifold admits a positive smooth exhaustion function.
* `Manifold.paracompactSpace_of_hasSubordinatePartitionOfUnity` — subordinate partitions of unity for all open covers imply paracompactness.

Provenance: SmoothManifoldsLee a5f308c — Definition_2_11_extra_2, Definition_2_11_extra_3, Proposition_2_28, Problem_2_13.
-/

open scoped Manifold ContDiff
open TopologicalSpace Filter Set

universe uK uE uH uM uE2 uH2 uN u

namespace Manifold

/-! ## Local smoothness on a subset -/

section IsSmoothOn

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE2} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH2} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}

/-- **Math.** A map defined on a subset `A` of a smooth manifold is *smooth* if
every point of `A` has an open neighborhood on which the map extends to a smooth
map. -/
def IsSmoothOn {A : Set M} (f : A → N) (I : ModelWithCorners 𝕜 E H)
    (I' : ModelWithCorners 𝕜 E' H') : Prop :=
  ∀ p : A,
    ∃ U : Opens M,
      (p : M) ∈ U ∧
        ∃ Fext : C^∞⟮I, U; I', N⟯,
          ∀ q : A, (hq : (q : M) ∈ U) → Fext ⟨q, hq⟩ = f q

/-- **Math.** `IsSmoothOn` is equivalent to the unbundled local-extension
formulation: each point has an open set on which a globally-defined `ContMDiffOn`
map agrees with `f`. -/
theorem isSmoothOn_iff_exists_local_extension {A : Set M} {f : A → N} :
    IsSmoothOn f I I' ↔
      ∀ p : A,
        ∃ U : Set M,
          IsOpen U ∧
            (p : M) ∈ U ∧
              ∃ Fext : M → N,
                ContMDiffOn I I' (∞ : ℕ∞ω) Fext U ∧
                  ∀ q : A, (q : M) ∈ U → Fext q = f q := by
  classical
  constructor
  · intro hf p
    rcases hf p with ⟨U, hpU, Fext, hFext⟩
    refine ⟨U, U.isOpen, hpU, ?_⟩
    let G : M → N := fun x ↦ if hx : x ∈ U then Fext ⟨x, hx⟩ else Fext ⟨p, hpU⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      have hG_subtype : ContMDiffAt I I' (∞ : ℕ∞ω) (fun y : U ↦ G y) ⟨x, hx⟩ := by
        have hEq : (fun y : U ↦ G y) = Fext := by
          funext y
          change G y = Fext y
          simp [G]
        rw [hEq]
        exact Fext.contMDiff ⟨x, hx⟩
      exact (contMDiffAt_subtype_iff.1 hG_subtype).contMDiffWithinAt
    · intro q hq
      unfold G
      split_ifs with h
      · simpa using hFext q h
      · exact (h hq).elim
  · intro hf p
    rcases hf p with ⟨U, hU, hpU, Fext, hFext, hEq⟩
    let Uo : Opens M := ⟨U, hU⟩
    refine ⟨Uo, hpU, ?_⟩
    refine ⟨⟨fun x : Uo ↦ Fext x, ?_⟩, ?_⟩
    · intro x
      exact contMDiffAt_subtype_iff.2 <|
        (hFext x x.property).contMDiffAt <|
          hU.mem_nhds x.property
    · intro q hq
      exact hEq q hq

end IsSmoothOn

/-! ## Exhaustion functions -/

section Exhaustion

variable {M : Type u} [TopologicalSpace M]

/-- **Math.** An *exhaustion function* on `M` is a continuous real-valued
function whose closed sublevel set `f ⁻¹' Iic c` is compact for every `c : ℝ`. -/
@[mk_iff isExhaustionFunction_iff]
class IsExhaustionFunction (f : M → ℝ) : Prop where
  continuous : Continuous f
  isCompact_sublevelSet (c : ℝ) : IsCompact (f ⁻¹' Iic c)

/-- **Math.** An exhaustion function tends to `+∞` away from compact sets. -/
theorem IsExhaustionFunction.tendsto_atTop {f : M → ℝ} (hf : IsExhaustionFunction f) :
    Tendsto f (cocompact M) atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  intro c _
  change f ⁻¹' Ioi c ∈ cocompact M
  convert (hf.isCompact_sublevelSet c).compl_mem_cocompact using 1
  ext x
  simp [not_le]

/-- **Math.** Every exhaustion function is a proper map. -/
theorem IsExhaustionFunction.isProperMap {f : M → ℝ} (hf : IsExhaustionFunction f) :
    IsProperMap f :=
  isProperMap_iff_tendsto_cocompact.2 ⟨hf.continuous, hf.tendsto_atTop.trans atTop_le_cocompact⟩

/-- **Math.** An exhaustion function canonically yields a proper map. -/
instance instIsProperMapOfIsExhaustionFunction {f : M → ℝ} [hf : IsExhaustionFunction f] :
    IsProperMap f :=
  hf.isProperMap

/-- **Math.** An exhaustion function canonically yields continuity of its
underlying function. -/
instance instContinuousOfIsExhaustionFunction {f : M → ℝ} [hf : IsExhaustionFunction f] :
    Continuous f :=
  hf.continuous

/-- **Math.** Any continuous real-valued function on a compact space is an
exhaustion function. -/
theorem Continuous.isExhaustionFunction {M : Type u} [TopologicalSpace M] [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f) : IsExhaustionFunction f := by
  refine ⟨hf, fun c ↦ ?_⟩
  exact isCompact_univ.of_isClosed_subset (isClosed_Iic.preimage hf) (Set.subset_univ _)

end Exhaustion

/-! ## Positive smooth exhaustion functions on a manifold -/

section SmoothExhaustion

/-- **Math.** Every smooth manifold (with or without boundary) that is Hausdorff
and $\sigma$-compact admits a smooth real-valued function that is everywhere
positive and has compact closed sublevel sets. -/
theorem exists_positive_smooth_exhaustion_function
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type uH} [TopologicalSpace H]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [IsManifold I (∞ : ℕ∞ω) M] [T2Space M] [SigmaCompactSpace M] :
    ∃ f : C^∞⟮I, M; ℝ⟯, (∀ x : M, 0 < f x) ∧ IsExhaustionFunction (f : M → ℝ) := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let K : CompactExhaustion M := default
  let t : M → Set ℝ := fun x ↦ Set.Ioi (K.find x : ℝ)
  -- The target set at each point is the open ray above the compact-exhaustion rank.
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    simp only [t]
    exact convex_Ioi (K.find x : ℝ)
  -- Near `x`, the constant `(K.find x : ℝ) + 2` stays above all nearby target thresholds.
  have hloc : ∀ x : M, ∃ c : ℝ, ∀ᶠ y in nhds x, c ∈ t y := by
    intro x
    refine ⟨(K.find x : ℝ) + 2, ?_⟩
    have hK : K (K.find x + 1) ∈ nhds x := by
      exact mem_interior_iff_mem_nhds.mp (K.subset_interior_succ _ (K.mem_find x))
    filter_upwards [hK] with y hy
    simp only [t, Set.mem_Ioi]
    have hy_find : K.find y ≤ K.find x + 1 := (K.mem_iff_find_le).1 hy
    exact_mod_cast lt_of_le_of_lt hy_find (Nat.lt_succ_self (K.find x + 1))
  -- A smooth partition-of-unity gluing theorem produces a smooth function in all targets.
  obtain ⟨f, hf⟩ : ∃ f : C^∞⟮I, M; ℝ⟯, ∀ x : M, f x ∈ t x := by
    simpa only [t] using exists_contMDiffMap_forall_mem_convex_of_local_const I ht hloc
  refine ⟨f, ?_⟩
  constructor
  · -- Positivity follows because the compact-exhaustion rank is nonnegative everywhere.
    intro x
    have h_find_nonneg : 0 ≤ (K.find x : ℝ) := by
      exact_mod_cast Nat.zero_le (K.find x)
    have h_find_lt : (K.find x : ℝ) < f x := by
      simpa [t, Set.mem_Ioi] using hf x
    exact lt_of_le_of_lt h_find_nonneg h_find_lt
  · -- Each closed sublevel set is contained in a compact stage of the compact exhaustion.
    refine ⟨f.contMDiff.continuous, ?_⟩
    intro c
    refine
      (K.isCompact ⌈c⌉₊).of_isClosed_subset (isClosed_Iic.preimage f.contMDiff.continuous) ?_
    intro x hx
    have h_find_lt : (K.find x : ℝ) < f x := by
      simpa [t, Set.mem_Ioi] using hf x
    have h_find_lt_c : (K.find x : ℝ) < c := h_find_lt.trans_le hx
    apply (K.mem_iff_find_le).2
    exact (Nat.lt_ceil.2 h_find_lt_c).le

end SmoothExhaustion

/-! ## Paracompactness from subordinate partitions of unity -/

section Paracompact

/-- **Math.** If every indexed open cover of `M` admits a partition of unity
subordinate to that cover, then `M` is paracompact. -/
theorem paracompactSpace_of_hasSubordinatePartitionOfUnity
    {M : Type u} [TopologicalSpace M]
    (hM : ∀ {ι : Type u} (U : ι → Set M), (∀ i, IsOpen (U i)) → (⋃ i, U i = Set.univ) →
      ∃ f : PartitionOfUnity ι M Set.univ, f.IsSubordinate U) :
    ParacompactSpace M := by
  refine ⟨fun ι U hU_open hU_cover ↦ ?_⟩
  obtain ⟨f, hf⟩ := hM U hU_open hU_cover
  let V : ι → Set M := fun i ↦ (f i : M → ℝ) ⁻¹' Set.Ioi 0
  refine ⟨ι, V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact isOpen_Ioi.preimage (f i).continuous
  · ext x
    constructor
    · intro _
      simp
    · intro _
      rcases f.exists_pos (by simp : x ∈ Set.univ) with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, by simpa [V] using hi⟩
  · refine f.locallyFinite.subset fun i x hx ↦ ?_
    change 0 < (f i : M → ℝ) x at hx
    simpa [Function.mem_support] using (ne_of_gt hx)
  · intro i
    refine ⟨i, fun x hx ↦ hf i <| subset_tsupport (f i : M → ℝ) ?_⟩
    change 0 < (f i : M → ℝ) x at hx
    simpa [Function.mem_support] using (ne_of_gt hx)

end Paracompact

end Manifold
