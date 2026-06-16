import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Velocity of a parametrized curve

Tangent-vector data attached to a smooth curve `γ : ℝ → M`, stated directly on
Mathlib's manifold-derivative API so it sits at the bottom of the tangent-bundle
layer with no extra packaging:

1. **Global velocity** — `curveVelocity` pushes the standard unit tangent vector
   `∂/∂t` through `mfderiv 𝓘(ℝ) I γ t`, the reusable notion of `γ'(t)` consumed
   wherever a curve's tangent direction is needed.
2. **Within-set velocity** — `curveVelocityWithin` is the one-sided variant built
   on `mfderivWithin`, the form used by boundary arguments on a parameter subset
   `s ⊆ ℝ`. It collapses onto the global velocity exactly where the parameter set
   is uniquely differentiable and the curve is differentiable, the bridge lemma
   downstream code relies on to move between the two.

## Main definitions

* `Manifold.curveVelocity` — velocity `γ'(t) ∈ T_{γ t} M` of a curve at `t`.
* `Manifold.curveVelocityWithin` — within-set velocity relative to a domain
  subset `s ⊆ ℝ`.

## Main results

* `Manifold.curveVelocityWithin_eq_curveVelocity` — the within-set velocity
  agrees with the ordinary velocity at a differentiability point of a uniquely
  differentiable parameter set.

Provenance: SmoothManifoldsLee a5f308c — Definition_3_17_extra_1.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Manifold

universe uM uH uE

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The standard unit tangent vector $\partial/\partial t$ at a
parameter value $t \in \mathbb{R}$, i.e. the number `1` viewed as an element of
`TangentSpace 𝓘(ℝ) t`. -/
private abbrev unitTangentVector (t : ℝ) : TangentSpace 𝓘(ℝ) t := (1 : ℝ)

/-- **Math.** The *velocity* of a parametrized curve `γ` at parameter `t` is the
manifold derivative of `γ` applied to the unit tangent vector `d/dt`, a tangent
vector in `T_{γ t} M`. -/
abbrev curveVelocity (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (t : ℝ) :
    TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ) I γ t (unitTangentVector t)

/-- **Math.** The velocity of a parametrized curve at a parameter value computed
relative to a domain subset `s` of the parameter line — the one-sided/within-set
variant used for boundary arguments. -/
abbrev curveVelocityWithin (I : ModelWithCorners ℝ E H) (γ : ℝ → M) (s : Set ℝ) (t : ℝ) :
    TangentSpace I (γ t) :=
  mfderivWithin 𝓘(ℝ) I γ s t (unitTangentVector t)

omit [IsManifold I ∞ M] in
/-- **Math.** On a parameter subset with a unique differential, and at a point
where the curve is manifold-differentiable, the within-set velocity agrees with
the ordinary velocity. -/
theorem curveVelocityWithin_eq_curveVelocity {γ : ℝ → M} {s : Set ℝ} {t : ℝ}
    (hs : UniqueMDiffWithinAt 𝓘(ℝ) s t) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    curveVelocityWithin I γ s t = curveVelocity I γ t := by
  simpa [curveVelocityWithin, curveVelocity] using
    DFunLike.congr_fun (mfderivWithin_eq_mfderiv hs hγ) (unitTangentVector t)

end Manifold
