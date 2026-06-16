import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Slice charts

The definition layer of the slice-chart machine, layered by how much ambient
machinery each predicate needs so downstream code imports only the generality
it uses:

1. **Model-generic core** — `Manifold.euclideanSlice` and
   `Manifold.IsEuclideanSlice` live purely in the model space `ℝ^n`: a slice is
   the locus where the last `n - k` coordinates are held fixed. This is the
   reusable base every chart-level layer is phrased against.
2. **Chart transport** — `Manifold.IsSliceInChart` pushes a subset of `M`
   through a chart and asks that its coordinate image be a Euclidean slice;
   `OpenPartialHomeomorph.IsSliceChart` adds membership in the smooth maximal
   atlas, so a slice chart is genuine slice coordinates and not merely a
   homeomorphism.
3. **Local condition** — `Manifold.SatisfiesLocalSliceCondition` is the
   `Prop`-valued interface: every point of `S` sits in the source of some smooth
   slice chart for `S`. It is the hypothesis consumed by the slice-implies-
   submanifold theorem (which lives downstream).

## Main definitions

* `Manifold.euclideanSlice` — the Euclidean `k`-slice of `U ⊆ ℝ^n` fixing the last `n - k` coordinates.
* `Manifold.IsEuclideanSlice` — predicate: a subset is such a slice for some constants.
* `Manifold.IsSliceInChart` — a subset of `M` has Euclidean-slice image in a given chart.
* `OpenPartialHomeomorph.IsSliceChart` — a maximal-atlas chart in which `S` appears as a slice.
* `Manifold.SatisfiesLocalSliceCondition` — every point of `S` lies in the source of a slice chart.

## Main results

* `OpenPartialHomeomorph.IsSliceChart.mem_maximalAtlas` — a slice chart lies in the smooth maximal atlas.
* `Manifold.satisfiesLocalSliceCondition_empty` — the empty subset satisfies the condition vacuously.

Provenance: SmoothManifoldsLee a5f308c — Definition_5_29_extra_1.
-/

open Set ChartedSpace
open scoped Manifold

universe u

namespace Manifold

/-- **Math.** The index in `Fin n` obtained by shifting `i : Fin (n - k)` past the
first `k` coordinates; it selects the last `n - k` coordinates that a `k`-slice
holds fixed. -/
private def tailCoordinate {n k : ℕ} (hk : k ≤ n) (i : Fin (n - k)) : Fin n :=
  Fin.cast (Nat.add_sub_of_le hk) (i.natAdd k)

/-- **Math.** The standard Euclidean `k`-slice of `U ⊆ ℝ^n`: the points of `U`
whose last `n - k` coordinates equal the constants `c`. -/
def euclideanSlice {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) (hk : k ≤ n)
    (c : Fin (n - k) → ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  { x ∈ U | ∀ i : Fin (n - k), x (tailCoordinate hk i) = c i }

/-- **Math.** A subset `S` of `U ⊆ ℝ^n` is a *`k`-slice* when it is `euclideanSlice U k`
for some choice of fixed last `n - k` coordinates. -/
def IsEuclideanSlice {n : ℕ} (S U : Set (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  ∃ hk : k ≤ n, ∃ c : Fin (n - k) → ℝ, S = euclideanSlice U k hk c

/-- **Math.** A subset `S ⊆ M` is a *`k`-slice in the chart `e`* when its image under
`e` (restricted to the chart source) is a Euclidean `k`-slice of the chart image
`e.target`. -/
def IsSliceInChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (S : Set M) (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (k : ℕ) : Prop :=
  IsEuclideanSlice (e '' (S ∩ e.source)) e.target k

end Manifold

namespace OpenPartialHomeomorph

/-- **Math.** A *slice chart* for `S` is a chart `e` in the smooth maximal atlas in
which `S` appears as a Euclidean `k`-slice, i.e. `e` provides slice coordinates
for `S`. -/
def IsSliceChart {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (S : Set M)
    (k : ℕ) : Prop :=
  e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M ∧
    Manifold.IsSliceInChart S e k

/-- **Math.** A slice chart lies in the smooth maximal atlas. -/
theorem IsSliceChart.mem_maximalAtlas
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]
    {e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {S : Set M} {k : ℕ}
    (he : e.IsSliceChart S k) :
    e ∈ IsManifold.maximalAtlas (𝓡 n) (⊤ : WithTop ℕ∞) M :=
  he.1

end OpenPartialHomeomorph

namespace Manifold

section

variable (n : ℕ) {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- **Math.** A subset `S` of an `n`-manifold satisfies the *local `k`-slice
condition* when each point of `S` lies in the source of some smooth slice chart
for `S`; any such chart then provides slice coordinates near that point. -/
class SatisfiesLocalSliceCondition (S : Set M) (k : ℕ) : Prop where
  /-- Every point of `S` lies in the source of some slice chart for `S`. -/
  exists_sliceChart (x : M) (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
      x ∈ e.source ∧ e.IsSliceChart S k

/-- **Math.** The empty subset satisfies the local `k`-slice condition vacuously. -/
instance satisfiesLocalSliceCondition_empty (k : ℕ) :
    SatisfiesLocalSliceCondition n (∅ : Set M) k := by
  refine ⟨?_⟩
  intro x hx
  cases hx

end

end Manifold
