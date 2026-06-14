import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Basic

/-!
# Coordinate balls

Coordinate-ball predicates for charts on a topological or smooth manifold. A
chart is a *coordinate ball* when its image is an open metric ball, a
*coordinate box* when its image is a product of open intervals, and *centered*
at a point when it sends that point to the origin. On a smooth manifold these
combine into the notions of a *smooth coordinate ball* (the source of a chart in
the maximal atlas whose image is an open ball) and a *regular coordinate ball*
(one whose closure sits inside a larger concentric chart).

## Main definitions

* `OpenPartialHomeomorph.IsCoordinateBall` — the chart's image is an open metric ball.
* `OpenPartialHomeomorph.IsCenteredAt` — the chart sends the point to `0`.
* `OpenPartialHomeomorph.IsCoordinateBox` — the chart's image is a product of open intervals.
* `OpenPartialHomeomorph.centerAt` — translate a chart so a source point maps to `0`.
* `Manifold.IsSmoothCoordinateBall` — source of a maximal-atlas chart whose image is an open ball.
* `Manifold.IsRegularCoordinateBall` — a coordinate ball whose closure sits in a larger chart.

## Main results

* `OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball` — a chart with ball image is a coordinate ball.
* `OpenPartialHomeomorph.isCoordinateBox_of_target_eq` — a chart with box image is a coordinate box.
* `OpenPartialHomeomorph.centerAt_isCenteredAt` — the centered chart is centered at its point.
* `Manifold.IsRegularCoordinateBall.exists_smoothCoordinateBall_superset` — a regular
  coordinate ball lies in a surrounding smooth coordinate ball.

Reference: Lee, *Introduction to Smooth Manifolds*, §1.

Ported from SmoothManifoldsLee Chap01/Sec01/Definition_1_extra_2.lean (a5f308c)
Ported from SmoothManifoldsLee Chap01/Sec01_03/Definition_1_3_extra_1.lean (a5f308c)
-/

noncomputable section

open Set
open scoped Manifold Topology

universe u v

section Charts

variable {H : Type*} [PseudoMetricSpace H]
variable {n : ℕ} {M : Type u} [TopologicalSpace M]

/-- **Math.** The chart `e` is a *coordinate ball*: its image is some open metric
ball `Metric.ball c r` of positive radius. **Eng.** Predicate on
`OpenPartialHomeomorph M H`; existentially quantifies over a center `c` and radius
`r` with `e.target = Metric.ball c r`. Stated on Mathlib's metric-space chart so it
applies to any model space, not just `EuclideanSpace`. -/
def OpenPartialHomeomorph.IsCoordinateBall (e : OpenPartialHomeomorph M H) : Prop :=
  ∃ c : H, ∃ r : ℝ, 0 < r ∧ e.target = Metric.ball c r

/-- **Math.** A chart whose image is the open ball `Metric.ball c r` is a coordinate
ball. **Eng.** Introduction rule for `IsCoordinateBall`: feed the witnessing center,
radius, positivity and target equality straight into the existential. -/
theorem OpenPartialHomeomorph.isCoordinateBall_of_target_eq_ball
    (e : OpenPartialHomeomorph M H) (c : H) (r : ℝ) (hr : 0 < r)
    (h : e.target = Metric.ball c r) : e.IsCoordinateBall :=
  ⟨c, r, hr, h⟩

variable (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

/-- **Math.** The chart `e` is *centered at* `p`: the point `p` lies in the chart's
source and `e` sends it to the origin `0`. **Eng.** Predicate packaging
`p ∈ e.source` with the coordinate condition `e p = 0`; the codomain is the
Euclidean model space so `0` is the literal zero vector. -/
def OpenPartialHomeomorph.IsCenteredAt (p : M) : Prop :=
  p ∈ e.source ∧ e p = 0

/-- **Math.** The chart `e` is a *coordinate box*: its image is a product of open
intervals `∏ᵢ (aᵢ, bᵢ)`. **Eng.** Existential over endpoint vectors `a b` with
`a i < b i` coordinatewise and `e.target` equal to the set of points whose every
coordinate lies in the corresponding `Set.Ioo`. -/
def OpenPartialHomeomorph.IsCoordinateBox : Prop :=
  ∃ a b : EuclideanSpace ℝ (Fin n),
    (∀ i, a i < b i) ∧ e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }

/-- **Math.** A chart whose image is the open box `∏ᵢ (aᵢ, bᵢ)` is a coordinate box.
**Eng.** Introduction rule for `IsCoordinateBox`: supply the endpoint vectors, the
coordinatewise strict-order hypothesis and the target equality to the existential. -/
theorem OpenPartialHomeomorph.isCoordinateBox_of_target_eq
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (a b : EuclideanSpace ℝ (Fin n))
    (hab : ∀ i, a i < b i)
    (h : e.target = { x | ∀ i : Fin n, x i ∈ Set.Ioo (a i) (b i) }) : e.IsCoordinateBox :=
  ⟨a, b, hab, h⟩

/-- **Math.** *Center* the chart `e` at a source point `p`, producing a chart with
the same source that sends `p` to the origin. **Eng.** Postcompose `e` with the
translation homeomorphism `Homeomorph.addRight (-e p)` via `transHomeomorph`; this
shifts coordinates so the image of `p` becomes `0` while leaving the source set
unchanged. -/
def OpenPartialHomeomorph.centerAt (p : e.source) :
    OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
  e.transHomeomorph (Homeomorph.addRight (-e p))

/-- **Math.** Centering a chart leaves its domain of definition unchanged. **Eng.**
The translation only affects the codomain, so `(e.centerAt p).source = e.source`
holds definitionally; `@[simp]` so downstream goals reduce automatically. -/
@[simp] theorem OpenPartialHomeomorph.centerAt_source (p : e.source) :
    (e.centerAt p).source = e.source :=
  rfl

/-- **Math.** The chart obtained by centering `e` at `p` is indeed centered at `p`.
**Eng.** Membership of `p` in the source is unchanged; the coordinate condition
`(e.centerAt p) p = 0` follows from unfolding `centerAt` and simplifying the
translation by `-e p`. -/
theorem OpenPartialHomeomorph.centerAt_isCenteredAt (p : e.source) :
    (e.centerAt p).IsCenteredAt p := by
  exact ⟨p.2, by simp [OpenPartialHomeomorph.centerAt]⟩

end Charts

namespace Manifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M]

/-- **Math.** A *smooth coordinate ball* is a subset `B ⊆ M` that is the source of a
chart in the maximal smooth atlas whose image is an open metric ball in the model
space `E`. **Eng.** Existential over a chart `φ` lying in
`IsManifold.maximalAtlas` with `φ.source = B` and `φ.IsCoordinateBall`. Stated on
Mathlib's `ChartedSpace`/`IsManifold` over `modelWithCornersSelf ℝ E`, with no
OpenGA packaging class. -/
def IsSmoothCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ φ : OpenPartialHomeomorph M E,
    φ ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      φ.source = B ∧ φ.IsCoordinateBall

/-- **Math.** A *regular coordinate ball* is a subset `B` whose closure lies inside a
larger maximal-atlas chart that sends `B` and its closure to concentric open and
closed balls of radius `r`, while the chart's whole image is a strictly larger ball
of radius `r' > r`. **Eng.** Existential over a chart and radii `r < r'` recording
`chart '' B = Metric.ball 0 r`, `chart '' closure B = Metric.closedBall 0 r`, and
`chart.target = Metric.ball 0 r'`, all in the model space `E`. -/
def IsRegularCoordinateBall (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M] (B : Set M) : Prop :=
  ∃ chart : OpenPartialHomeomorph M E,
    chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M ∧
      closure B ⊆ chart.source ∧
      ∃ r r' : ℝ,
        0 < r ∧
          r < r' ∧
          chart '' B = Metric.ball (0 : E) r ∧
          chart '' closure B = Metric.closedBall (0 : E) r ∧
          chart.target = Metric.ball (0 : E) r'

/-- **Math.** Every regular coordinate ball is contained in a surrounding smooth
coordinate ball: namely the source of its defining larger chart, which itself is a
smooth coordinate ball, and which contains the closure of `B`. **Eng.** Destructure
the regular-ball witness, take `B' := chart.source`, and rebuild the smooth-ball
data from the same chart using `isCoordinateBall_of_target_eq_ball` with radius `r'`
(positive since `0 < r < r'`). -/
theorem IsRegularCoordinateBall.exists_smoothCoordinateBall_superset {B : Set M}
    (hB : IsRegularCoordinateBall E B) :
    ∃ B' : Set M, IsSmoothCoordinateBall E B' ∧ closure B ⊆ B' := by
  rcases hB with ⟨chart, hchart, hclosure, r, r', hr, hr', -, -, htarget⟩
  refine ⟨chart.source, ⟨chart, hchart, rfl, ?_⟩, hclosure⟩
  exact chart.isCoordinateBall_of_target_eq_ball (0 : E) r' (lt_trans hr hr') htarget

end Manifold
