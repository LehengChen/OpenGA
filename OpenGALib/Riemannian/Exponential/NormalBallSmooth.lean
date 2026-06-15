import OpenGALib.Riemannian.Exponential.LocalDiffeomorphism

/-!
# Smoothness and differentiability of `expMap` on a normal ball

OpenGALib's exponential-map layer establishes that `expMap g p` is a `C^1` local
diffeomorphism *at the zero vector* (`expMap_isLocalDiffeomorphAt_zero`,
`exists_open_nhds_expMap_diffeoOn`). For Bishop–Gromov's geometric legs (the
Gauss lemma / eikonal and the volume Jacobian) we need `expMap g p` smooth and
differentiable at *general* points `v ≠ 0` of a normal ball, not just at `0`.

This is supplied for free by the partial diffeomorphism witnessing the local
diffeomorphism: it equals `expMap g p` on its *whole open source* (a normal ball
around `0`), so on that source `expMap g p` is `C^1` (`ContMDiffOn`) and is a
local diffeomorphism at every point — hence differentiable with an invertible
manifold derivative there.

These are the entry points the downstream Gauss-lemma / volume-Jacobian
constructions consume.
-/

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff

set_option linter.unusedSectionVars false

namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section NormalBall

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** There is an open normal ball `V ∋ 0` in `T_p M` on which `expMap g p`
is `C^1` (`ContMDiffOn`) and is a `C^1` local diffeomorphism at every point. The
ball is the source of the partial diffeomorphism realising `expMap g p` near `0`;
since that diffeomorphism agrees with `expMap g p` on its whole (open) source,
both properties hold at general `v ∈ V`, not just at `0`. -/
theorem exists_expMap_diffeoOn_nhds_zero (g : RiemannianMetric I M) (p : M) :
    ∃ V : Set E, IsOpen V ∧ (0 : E) ∈ V ∧
      ContMDiffOn 𝓘(ℝ, E) I 1
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) V ∧
      ∀ v ∈ V, IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) v := by
  obtain ⟨Φ, h0, hΦeq⟩ := exists_open_nhds_expMap_diffeoOn (I := I) g p
  have heqon : Set.EqOn
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) Φ Φ.source :=
    fun v hv => (hΦeq v hv).symm
  exact ⟨Φ.source, Φ.open_source, h0,
    Φ.contMDiffOn_toFun.congr heqon,
    fun v hv => ⟨Φ, hv, heqon⟩⟩

/-- **Math.** On the normal ball, `expMap g p` is differentiable at every point:
its manifold derivative `d(expMap g p)|_v` exists for `v ≠ 0` too, not only at the
base point. This is the differentiability input the Gauss lemma and the volume
Jacobian consume. -/
theorem expMap_mdifferentiableAt_of_isLocalDiffeomorphAt
    {g : RiemannianMetric I M} {p : M} {v : E}
    (hv : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) v) :
    MDifferentiableAt 𝓘(ℝ, E) I
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) v :=
  hv.mdifferentiableAt (by norm_num)

/-- **Math.** On the normal ball, `d(expMap g p)|_v` is a continuous linear
equivalence `T_v(T_pM) ≃L T_{exp v} M`. In particular it is invertible — the
source of nondegeneracy of the volume Jacobian `det d exp_p(v) ≠ 0` that the
geodesic-polar volume formula needs. Its forward map is exactly the manifold
derivative `mfderiv ... (expMap g p) v`. -/
noncomputable def expMap_mfderivContinuousLinearEquiv
    {g : RiemannianMetric I M} {p : M} {v : E}
    (hv : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) v) :
    TangentSpace 𝓘(ℝ, E) v ≃L[ℝ]
      TangentSpace I (expMap (I := I) g p (show TangentSpace I p from v) : M) :=
  hv.mfderivToContinuousLinearEquiv (by norm_num)

end NormalBall

end Exponential
end Riemannian
