import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.MetricGeometry.LengthSpace

/-!
# ① `dist = ⨅ pathLength` bridge — analytic core

The key lemma behind `Bridges/RiemannianToLength.lean`'s remaining `sorry`
(`⨅ γ, pathLength γ ≤ edist x y`): for a `C¹` path the metric `eVariationOn`
(OpenGA `pathLength`) is bounded by the tangent integral (`Manifold.pathELength`).

Proof map (do Carmo Ch. 7 §2 / Burago–Burago–Ivanov §2.7.1):
```
eVariationOn (↑γ) univ = ⨆_partitions  Σ edist (γ tᵢ₊₁) (γ tᵢ)
  ≤ ⨆_partitions Σ pathELength I γ.extend tᵢ tᵢ₊₁   -- edist = riemannianEDist ≤ pathELength
  = pathELength I γ.extend 0 1                        -- pathELength_add telescoping
```

Once proved, replace the bridge `sorry` with
`le_iInf₂ fun γ hγ ↦ iInf_le_of_le γ (pathLength_le_pathELength γ hγ)`
(after `rw [IsRiemannianManifold.out, riemannianEDist]`).
-/

open Bundle Set Topology
open scoped Manifold ContDiff

namespace OpenGA.HopfRinow

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- **Math.** Per-segment bound: on a `C¹` path, the metric distance between two
parameter values is bounded by the tangent-integral length over that subinterval.
`edist (γ a) (γ b) = riemannianEDist ≤ pathELength I γ a b`. -/
theorem edist_le_pathELength_of_cmdiff {γ : ℝ → M} {a b : ℝ}
    (hγ : CMDiff[Icc a b] 1 γ) (hab : a ≤ b) :
    edist (γ a) (γ b) ≤ Manifold.pathELength I γ a b := by
  -- `edist = riemannianEDist` (`IsRiemannianManifold.out`) `≤ pathELength`
  -- (`Manifold.riemannianEDist_le_pathELength`). MICRO-BLOCKER: the lemma needs
  -- `[∀ x, ENormSMulClass ℝ (TangentSpace I x)]`, which the canonical Mathlib
  -- RiemannianBundle block does NOT auto-provide and which clashes with the
  -- bundle's own `ENorm` when added explicitly. Needs a targeted instance fix.
  sorry

/-- **Math.** **Key lemma (①).** For a `C¹` path `γ : ℝ → M` smooth on `[0,1]`, the
metric `eVariationOn` of `γ` over `[0,1]` is bounded by the tangent-integral length
`pathELength I γ 0 1`. This is the sole remaining content of the metric=length
bridge `Bridges/RiemannianToLength.lean`. -/
theorem eVariationOn_le_pathELength {γ : ℝ → M}
    (hγ : CMDiff[Icc 0 1] 1 γ) :
    eVariationOn γ (Icc 0 1) ≤ Manifold.pathELength I γ 0 1 := by
  -- eVariationOn = ⨆ over monotone partitions of `Σ edist (γ tᵢ₊₁) (γ tᵢ)`;
  -- each term ≤ pathELength over its segment (`edist_le_pathELength_of_cmdiff`);
  -- the telescoped sum collapses to `pathELength I γ 0 1` (`pathELength_add`).
  sorry

end OpenGA.HopfRinow
