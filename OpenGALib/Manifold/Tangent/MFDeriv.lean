import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Functoriality of the manifold differential

The manifold derivative `mfderiv` packaged as the differential of smooth maps,
stated on Mathlib's `ContMDiff` / `Diffeomorph` API and layered by how the
differential interacts with structure:

1. **Composition** — the differential is functorial: `mfderiv_comp_of_smooth`
   is the chain rule `d(G ∘ F)_p = dG_{F p} ∘ dF_p`, the base fact the rest
   builds on.
2. **Diffeomorphisms** — for a `C^n` diffeomorphism the differential is a linear
   isomorphism; `diffeomorph_mfderiv_symm_eq_symm` identifies its inverse with
   the differential of the inverse map.
3. **Open submanifolds** — the inclusion of an open subset is a local
   diffeomorphism, so `mfderiv_open_subset_inclusion_isInvertible` records that
   its differential is invertible at every point, the interface used when
   localizing the tangent bundle to an open chart domain.

## Main results

* `Manifold.mfderiv_comp_of_smooth` — chain rule: the differential of a
  composite of smooth maps is the composite of the differentials.
* `Manifold.diffeomorph_mfderiv_symm_eq_symm` — for a `C^n` diffeomorphism
  (`n ≠ 0`), the inverse of the differential is the differential of the inverse.
* `Manifold.mfderiv_open_subset_inclusion_isInvertible` — the differential of
  the inclusion of an open subset is invertible at each point.

Provenance: SmoothManifoldsLee a5f308c — Proposition_3_9, Proposition_3_6.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Manifold

section CompositionAndIdentity

universe u𝕜 uE uE' uE'' uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {I'' : ModelWithCorners 𝕜 E'' H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]
variable {F : M → N} {G : N → P} {p : M}

omit [IsManifold I ∞ M] [IsManifold I' ∞ N] [IsManifold I'' ∞ P] in
/-- **Math.** The differential of a composite of smooth maps is the composite of
the differentials, `d(G ∘ F)_p = dG_{F p} ∘ dF_p`. -/
theorem mfderiv_comp_of_smooth (hF : ContMDiff I I' ∞ F) (hG : ContMDiff I' I'' ∞ G) :
    mfderiv I I'' (G ∘ F) p = (mfderiv I' I'' G (F p)).comp (mfderiv I I' F p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  exact mfderiv_comp p (hG.contMDiffAt.mdifferentiableAt hn) (hF.contMDiffAt.mdifferentiableAt hn)

end CompositionAndIdentity

section Diffeomorphisms

universe u𝕜 uE uE' uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : ℕ∞ω}

/-- **Math.** For a `C^n` diffeomorphism `Φ` with `n ≠ 0`, the inverse of the
differential `dΦ_p` is the differential of the inverse diffeomorphism,
`d(Φ⁻¹)_{Φ p} = (dΦ_p)⁻¹`. -/
theorem diffeomorph_mfderiv_symm_eq_symm
    (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (p : M) :
    mfderiv I' I Φ.symm (Φ p) =
      ((Φ.mfderivToContinuousLinearEquiv hn p).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := by
  have hΦ : IsLocalDiffeomorphAt I I' n Φ p := Φ.isLocalDiffeomorph p
  have hlocalInverse : hΦ.localInverse =ᶠ[nhds (Φ p)] Φ.symm := by
    refine Filter.eventuallyEq_of_mem
      (hΦ.localInverse_open_source.mem_nhds hΦ.localInverse_mem_source) ?_
    intro y hy
    apply Φ.injective
    simpa using hΦ.localInverse_right_inv hy
  have h₁ : mfderiv I' I Φ.symm (Φ p) = mfderiv I' I hΦ.localInverse (Φ p) := by
    symm
    exact hlocalInverse.mfderiv_eq
  have h₂ : mfderiv I' I hΦ.localInverse (Φ p) =
      ((hΦ.mfderivToContinuousLinearEquiv hn).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := rfl
  have h₃ : ((hΦ.mfderivToContinuousLinearEquiv hn).symm :
      TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) =
      ((Φ.mfderivToContinuousLinearEquiv hn p).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := rfl
  exact h₁.trans (h₂.trans h₃)

end Diffeomorphisms

section OpenSubsetInclusion

universe u𝕜 uE uH uM

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]

/-- **Math.** If `U` is an open subset of `M`, then for every `p : U` the
differential of the inclusion `Subtype.val : U → M` at `p` is an isomorphism of
tangent spaces. -/
theorem mfderiv_open_subset_inclusion_isInvertible (U : TopologicalSpace.Opens M) (p : U) :
    (mfderiv I I (Subtype.val : U → M) p).IsInvertible := by
  let e := U.openPartialHomeomorphSubtypeCoe ⟨p⟩
  have hsymm : ContMDiffOn I I 1 e.symm (U : Set M) := by
    intro x hx
    have hcomp : ContMDiffWithinAt I I 1 (Subtype.val ∘ e.symm) (U : Set M) x := by
      refine contMDiffWithinAt_id.congr_of_mem ?_ hx
      intro y hy
      simpa [e] using e.right_inv (by simpa [e] using hy)
    have hiff :
        ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) (Subtype.val ∘ e.symm)
            (U : Set M) x ↔
          ChartedSpace.LiftPropWithinAt (ContDiffWithinAtProp I I 1) e.symm (U : Set M) x :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff e.symm (U : Set M) x
    simpa [ContMDiffWithinAt] using
      hiff.mp (by simpa [ContMDiffWithinAt] using hcomp)
  let Φ : PartialDiffeomorph I I U M 1 := {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := by
      simpa [e] using
        ((contMDiff_subtype_val : ContMDiff I I 1 (Subtype.val : U → M)).contMDiffOn :
          ContMDiffOn I I 1 (Subtype.val : U → M) Set.univ)
    contMDiffOn_invFun := by
      simpa [e] using hsymm }
  have hp : p ∈ Φ.source := by
    simp [Φ, e]
  have hlocal : IsLocalDiffeomorphAt I I 1 (Φ : U → M) p := by
    exact ⟨Φ, hp, fun x _ ↦ rfl⟩
  have hinv : (mfderiv I I (Φ : U → M) p).IsInvertible := by
    rw [← hlocal.mfderivToContinuousLinearEquiv_coe one_ne_zero]
    exact ContinuousLinearMap.isInvertible_equiv
  simpa [Φ, e] using hinv

end OpenSubsetInclusion

end Manifold
