import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.FiberBundle.Trivialization
import OpenGALib.Manifold.Map.LocalDiffeomorph
import OpenGALib.Manifold.Map.TopologicalImmersionSubmersion
import OpenGALib.Manifold.Covering.SmoothCoveringMap

/-!
# Local sections of smooth covering maps

Existence and rigidity of local sections, built in two layers so each result
is stated at the weakest structure it needs:

1. **Topological core** — over an evenly covered open set a covering map carries
   a continuous local section through any prescribed point of the fiber, and on
   a preconnected open set two continuous sections agreeing at one point agree
   everywhere. These need only `IsCoveringMap` and live on the base–total-space
   pair as topological spaces.
2. **Smooth upgrade** — a smooth covering map is in particular a smooth local
   diffeomorphism, so its continuous local sections are automatically smooth.
   Composition with the covering projection detects this smoothness, turning the
   topological sections into `IsSmoothLocalSection`s and upgrading both the
   existence and the rigidity statements to the smooth setting.

The smoothness predicate `IsSmoothLocalSection` is the clean payload of the
Local Section Theorem; it is carried here as a standalone definition (with its
section equation `apply_eq`) so this file does not depend on the still-open
submersion characterization that introduces it upstream.

## Main definitions

* `Manifold.IsSmoothLocalSection` — a smooth right inverse of `π` over an open
  subset of the base.

## Main results

* `Manifold.IsSmoothLocalSection.apply_eq` — a smooth local section satisfies the
  section equation at each point of its domain.
* `Manifold.exists_continuousLocalSection_of_isCoveringMap` — an evenly covered
  open set carries a continuous local section through any chosen fiber point.
* `Manifold.continuousLocalSection_eq_of_isCoveringMap` — preconnected rigidity
  of continuous local sections of a covering map.
* `Manifold.IsSmoothCoveringMap.contMDiffOn_of_continuous_rightInvOn` — a
  continuous local section of a smooth covering map is smooth on its open domain.
* `Manifold.IsSmoothCoveringMap.exists_localSectionOn` — a smooth covering map has
  a smooth local section through any chosen point of any fiber.
* `Manifold.IsSmoothCoveringMap.localSection_eq` — preconnected rigidity of smooth
  local sections of a smooth covering map.

Provenance: SmoothManifoldsLee a5f308c — Exercise_4_37, Proposition_4_36
(`IsSmoothLocalSection` and its `apply_eq` carried from Theorem_4_26).
-/

open Bundle
open scoped Manifold ContDiff Topology

namespace Manifold

section Smoothness

universe u𝕜 uE uE' uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}

/-- **Math.** A *smooth local section* of `pi : M → N` over an open subset `U ⊆ N`
is a smooth map `σ : U → M` whose composite with `pi` is the identity on `U`. -/
def IsSmoothLocalSection (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (pi : M → N) (U : TopologicalSpace.Opens N) (σ : U → M) : Prop :=
  ContMDiff J I ∞ σ ∧ ∀ x : U, pi (σ x) = x

namespace IsSmoothLocalSection

/-- **Math.** A smooth local section satisfies the section equation `pi (σ x) = x`
at each point `x` of its open domain. -/
theorem apply_eq {pi : M → N} {U : TopologicalSpace.Opens N} {σ : U → M}
    (hσ : IsSmoothLocalSection I J pi U σ) (x : U) :
    pi (σ x) = x :=
  hσ.2 x

end IsSmoothLocalSection

end Smoothness

section Topological

universe uE uM

variable {E : Type uE} [TopologicalSpace E]
variable {M : Type uM} [TopologicalSpace M]

/-- **Math.** On a preconnected open subset `U` of the base of a covering map, two
continuous local sections that agree at one point agree everywhere on `U`. -/
theorem continuousLocalSection_eq_of_isCoveringMap {pi : E → M} (hpi : IsCoveringMap pi)
    {U : TopologicalSpace.Opens M} (hU : IsPreconnected (U : Set M)) {q : U} {σ σ' : U → E}
    (hσ : Continuous σ) (hσ' : Continuous σ') (hsec : ∀ x : U, pi (σ x) = x)
    (hsec' : ∀ x : U, pi (σ' x) = x) (hqq : σ q = σ' q) :
    σ = σ' := by
  let _ : PreconnectedSpace U := Subtype.preconnectedSpace hU
  refine hpi.eq_of_comp_eq hσ hσ' ?_ q hqq
  funext x
  exact (hsec x).trans (hsec' x).symm

/-- **Math.** An evenly covered open subset of the base of a covering map carries a
continuous local section through any prescribed point of the chosen fiber. -/
theorem exists_continuousLocalSection_of_isCoveringMap {pi : E → M} (hpi : IsCoveringMap pi)
    {q : M} (t : Trivialization (pi ⁻¹' {q}) pi) (hq : q ∈ t.baseSet) {p : E}
    (hp : p ∈ pi ⁻¹' {q}) :
    let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
    ∃ σ : C(U, E), Manifold.IsLocalSection (⟨pi, hpi.continuous⟩ : C(E, M)) U σ ∧ σ ⟨q, hq⟩ = p := by
  let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
  have hp_eq : pi p = q := by
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hp
  have hp_base : pi p ∈ t.baseSet := by
    simpa [hp_eq] using hq
  have hmain :
      ∃ σ : C(U, E), Manifold.IsLocalSection (⟨pi, hpi.continuous⟩ : C(E, M)) U σ ∧
        σ ⟨q, hq⟩ = p := by
    -- Fix the sheet of `p` inside the trivialization and lift each base point along that sheet.
    have hσ_cont : Continuous fun x : U => t.lift p x := by
      have hgraph : Continuous fun x : U => ((x : M), (t p).2) :=
        continuous_subtype_val.prodMk continuous_const
      have htarget : ∀ x : U, ((x : M), (t p).2) ∈ t.target := fun x => t.mem_target.2 x.2
      -- Continuity comes from composing the inverse trivialization with the fixed-sheet graph.
      simpa [Bundle.Trivialization.lift] using
        t.continuousOn_invFun.comp_continuous hgraph htarget
    let σ : C(U, E) := ⟨fun x => t.lift p x, hσ_cont⟩
    have hσ_sec : Manifold.IsLocalSection (⟨pi, hpi.continuous⟩ : C(E, M)) U σ := by
      -- The fixed-sheet lift is a right inverse to `pi` on the evenly covered base set.
      intro x
      simpa [σ] using t.proj_lift (z := p) (b := (x : M)) x.2
    have hσq : σ ⟨q, hq⟩ = p := by
      -- Over the point `q = pi p`, lifting along the sheet of `p` returns `p` itself.
      simpa [σ, hp_eq] using t.lift_self (z := p) hp_base
    exact ⟨σ, hσ_sec, hσq⟩
  simpa [U] using hmain

end Topological

section SmoothCovering

universe uK uVE uVM uHE uHM uE uM

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable (IE : ModelWithCorners K VE HE) (IM : ModelWithCorners K VM HM)
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]

namespace IsSmoothCoveringMap

/-- **Math.** Every continuous local section of a smooth covering map is smooth on
its open domain: smoothness is detected after composing with the covering
projection, which is a smooth local diffeomorphism. -/
theorem contMDiffOn_of_continuous_rightInvOn {pi : E → M}
    (hpi : Manifold.IsSmoothCoveringMap IE IM pi) {U : Set M} (hU : IsOpen U) {σ : M → E}
    (hσ : ContinuousOn σ U) (hsec : Set.RightInvOn σ pi U) :
    ContMDiffOn IM IE ∞ σ U := by
  let U' : TopologicalSpace.Opens M := ⟨U, hU⟩
  let σ' : C(U', E) := ⟨U.restrict σ, hσ.restrict⟩
  have hσ' : Manifold.IsLocalSection (⟨pi, hpi.isCoveringMap.continuous⟩ : C(E, M)) U' σ' :=
    fun x => hsec x.2
  have hcomp : pi ∘ σ' = Subtype.val := by
    funext x
    exact hσ' x
  have hsmooth : ContMDiff IM IE ∞ σ' := by
    -- Smoothness is detected after composing with the smooth local diffeomorphism `pi`.
    refine
      (Manifold.smooth_iff_comp_left_of_isLocalDiffeomorph hpi.isLocalDiffeomorph
        σ'.continuous).mpr ?_
    simpa [hcomp] using
      (contMDiff_subtype_val : ContMDiff IM IM ∞ (Subtype.val : U' → M))
  intro x hx
  have hsub : ContMDiffAt IM IE ∞ (fun y : U' ↦ σ y) ⟨x, hx⟩ := by
    simpa [σ'] using hsmooth ⟨x, hx⟩
  exact (contMDiffAt_subtype_iff.mp hsub).contMDiffWithinAt

/-- **Math.** On an evenly covered open subset `U`, a smooth covering map has a
smooth local section through any chosen point `p` of the fiber over `q`. -/
theorem exists_localSectionOn {pi : E → M} (hpi : Manifold.IsSmoothCoveringMap IE IM pi)
    {q : M} (t : Trivialization (pi ⁻¹' {q}) pi) (hq : q ∈ t.baseSet) {p : E}
    (hp : p ∈ pi ⁻¹' {q}) :
    let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
    ∃ σ : U → E, Manifold.IsSmoothLocalSection IE IM pi U σ ∧ σ ⟨q, hq⟩ = p := by
  let U : TopologicalSpace.Opens M := ⟨t.baseSet, t.open_baseSet⟩
  have htop :
      ∃ σ : C(U, E), Manifold.IsLocalSection (⟨pi, hpi.isCoveringMap.continuous⟩ : C(E, M)) U σ ∧
        σ ⟨q, hq⟩ = p := by
    simpa [U] using
      Manifold.exists_continuousLocalSection_of_isCoveringMap hpi.isCoveringMap (q := q) t hq hp
  rcases htop with ⟨σ, hσ, hσq⟩
  have hcomp : pi ∘ σ = Subtype.val := by
    funext x
    exact hσ x
  have hsmooth : ContMDiff IM IE ∞ σ := by
    -- Smoothness is detected after composing with the smooth local diffeomorphism `pi`.
    refine
      (Manifold.smooth_iff_comp_left_of_isLocalDiffeomorph hpi.isLocalDiffeomorph σ.continuous).mpr ?_
    simpa [hcomp] using
      (contMDiff_subtype_val : ContMDiff IM IM ∞ (Subtype.val : U → M))
  exact ⟨σ, ⟨hsmooth, hσ⟩, hσq⟩

/-- **Math.** On a preconnected open subset `U` of the base of a smooth covering
map, any two smooth local sections that agree at one point agree on all of `U`. -/
theorem localSection_eq {pi : E → M} (hpi : Manifold.IsSmoothCoveringMap IE IM pi)
    {U : TopologicalSpace.Opens M} (hU : IsPreconnected (U : Set M)) {q : U} {σ σ' : U → E}
    (hσ : Manifold.IsSmoothLocalSection IE IM pi U σ)
    (hσ' : Manifold.IsSmoothLocalSection IE IM pi U σ') (hqq : σ q = σ' q) :
    σ = σ' :=
  Manifold.continuousLocalSection_eq_of_isCoveringMap hpi.isCoveringMap hU
    hσ.1.continuous hσ'.1.continuous hσ.apply_eq hσ'.apply_eq hqq

end IsSmoothCoveringMap

end SmoothCovering

end Manifold
