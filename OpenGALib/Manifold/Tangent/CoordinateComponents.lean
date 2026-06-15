import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Coordinate components of tangent vectors

The coordinate-component picture of the tangent space, layered by how it is used
downstream:

1. **Chart-induced basis** — a maximal-atlas chart at `p` is a smooth coordinate
   diffeomorphism, so its differential transports the standard basis of the
   model space to a basis of `TangentSpace I p`. This is the reusable bridge from
   chart smoothness to linear-algebra structure on the fibre.
2. **Transformation law** — `tangentCoordChange` is the basis-free change of
   tangent coordinates between preferred charts; it is the rule every component
   family must obey on overlaps.
3. **Coordinate-family realization** — `IsCoordinateTangentVector` /
   `CoordinateTangentVector` package a tangent vector as its compatible
   preferred-chart components. This is a *re-presentation* of `TangentSpace I p`,
   shown canonically equivalent to it (`equivTangentSpace`), not a second owner
   type for tangent vectors.

## Main definitions

* `Manifold.IsCoordinateTangentVector` — compatibility predicate: a choice of
  model component in every preferred chart at `p`, matched by the tangent
  coordinate-change maps on overlaps.
* `Manifold.CoordinateTangentVector` — bundled compatible family of
  preferred-chart components at `p`.
* `Manifold.coordinateComponent` — the component of a tangent vector in the
  preferred chart centered at `x`, in the model vector space.
* `Manifold.chartCoordinateVectorsBasis` — the coordinate basis of `T_p M`
  determined by a smooth chart containing `p`.

## Main results

* `Manifold.chart_mdifferentiable_of_mem_maximalAtlas` — a chart in the maximal
  atlas is manifold-differentiable with differentiable inverse.
* `Manifold.coordinateComponent_isCoordinateTangentVector` — the chart
  components of a tangent vector satisfy the coordinate transformation rule.
* `Manifold.CoordinateTangentVector.equivTangentSpace` — the coordinate-family
  realization is canonically equivalent to the tangent space.

Provenance: SmoothManifoldsLee a5f308c — Proposition_3_15, Definition_3_18_extra_4 (inlines Remark_3_15_extra_4).
-/

noncomputable section

open Set Bundle
open scoped Manifold

namespace Manifold

/-! ## Chart-induced coordinate basis (Proposition 3.15) -/

section ChartBasis

universe uH uM

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **Math.** A chart belonging to the maximal atlas of a smooth manifold is
manifold-differentiable, and so is its inverse: it is a smooth coordinate
diffeomorphism onto its image. -/
theorem chart_mdifferentiable_of_mem_maximalAtlas
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M) :
    OpenPartialHomeomorph.MDifferentiable I I e := by
  refine ⟨?_, ?_⟩
  · exact
      (show ContMDiffOn I I 1 e e.source from
        contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero
  · exact
      (show ContMDiffOn I I 1 e.symm e.target from
        contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn one_ne_zero

/-- **Math.** Proposition 3.15 (2): a smooth chart containing `p` determines the
coordinate-vector basis of `TangentSpace I p` by transporting the standard basis
of `EuclideanSpace ℝ (Fin n)` through the inverse chart differential. -/
noncomputable def chartCoordinateVectorsBasis
    (e : OpenPartialHomeomorph M H) (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (p : M) (hp : p ∈ e.source) :
    Module.Basis (Fin n) ℝ (TangentSpace I p) :=
  let de : TangentSpace I p ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    OpenPartialHomeomorph.MDifferentiable.mfderiv
      (chart_mdifferentiable_of_mem_maximalAtlas e he) hp
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map de.symm.toLinearEquiv

end ChartBasis

/-! ## Tangent coordinate change (Remark 3.15, inlined wrapper)

`tangent_coordinates_change` is the Mathlib-only thin wrapper from
`Remark_3_15_extra_4`: it identifies the trivialization coordinate change of the
tangent bundle with `tangentCoordChange`. It is inlined here (rather than
imported from a non-ported source module) so that the coordinate-component
transformation law below is available. -/

section CoordChange

universe u𝕜 uE uH uM

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- **Math.** Remark 3.15-extra-4: changing tangent coordinates from the chart
centered at `x` to the chart centered at `y` is given by the tangent
coordinate-change linear map `tangentCoordChange I x y z`, the basis-free form of
the component transformation law (3.12). -/
theorem tangent_coordinates_change
    {x y z : M} (hxy : z ∈ (chartAt H x).source ∩ (chartAt H y).source) :
    (trivializationAt E (TangentSpace I) x).coordChangeL 𝕜
        (trivializationAt E (TangentSpace I) y) z =
      tangentCoordChange I x y z := by
  ext v
  simpa [tangentCoordChange] using
    (tangentBundleCore I M).trivializationAt_coordChange_eq hxy v

end CoordChange

/-! ## Coordinate tangent vectors (Definition 3.18-extra-4) -/

section Coordinate

universe u𝕜 uE uH uM

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (I)

/-- **Math.** Definition 3.18-extra-4: a coordinate tangent vector at `p` is a
choice of model-space component in every preferred chart containing `p`,
compatible under the tangent-coordinate change maps on overlaps. This is the
coordinate-family view of the canonical tangent space `TangentSpace I p`, not a
second owner type. -/
def IsCoordinateTangentVector (p : M)
    (component : {x : M // p ∈ (chartAt H x).source} → E) : Prop :=
  ∀ x y : {x : M // p ∈ (chartAt H x).source},
    tangentCoordChange I x.1 y.1 p (component x) = component y

/-- **Math.** The coordinate-family realization of `TangentSpace I p` as
compatible preferred-chart components. -/
structure CoordinateTangentVector (p : M) where
  /-- The model-space component in each preferred chart containing `p`. -/
  component : {x : M // p ∈ (chartAt H x).source} → E
  /-- The components are compatible under tangent coordinate changes. -/
  compatible : IsCoordinateTangentVector I p component

/-- **Math.** A coordinate tangent vector acts as its component family: applying
it to a preferred chart yields that chart's model-space component. -/
instance {p : M} : CoeFun (CoordinateTangentVector I p)
    (fun _ ↦ {x : M // p ∈ (chartAt H x).source} → E) := ⟨CoordinateTangentVector.component⟩

/-- **Math.** A coordinate tangent vector applied to a preferred chart returns
that chart's component. -/
@[simp] theorem CoordinateTangentVector.component_apply {p : M} (v : CoordinateTangentVector I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : v.component x = v x := rfl

/-- **Math.** The components of a coordinate tangent vector obey the coordinate
transformation rule on overlapping charts. -/
theorem CoordinateTangentVector.compatible_apply {p : M} (v : CoordinateTangentVector I p)
    (x y : {x : M // p ∈ (chartAt H x).source}) :
    tangentCoordChange I x.1 y.1 p (v x) = v y :=
  v.compatible x y

/-- **Math.** Two coordinate tangent vectors are equal when their components
agree in every preferred chart. -/
@[ext] theorem CoordinateTangentVector.ext {p : M} {v w : CoordinateTangentVector I p}
    (h : ∀ x, v x = w x) : v = w := by
  cases v with
  | mk componentv hv =>
      cases w with
      | mk componentw hw =>
          have hcomponent : componentv = componentw := funext h
          cases hcomponent
          have hproof : hv = hw := Subsingleton.elim _ _
          cases hproof
          rfl

variable {I}

/-- **Math.** The component of a tangent vector in the preferred chart centered
at `x`, written in the model vector space. -/
def coordinateComponent {p : M} (v : TangentSpace I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : E :=
  (trivializationAt E (TangentSpace I) x.1).linearEquivAt 𝕜 p x.2 v

/-- **Math.** The chart components of a tangent vector satisfy the usual
coordinate transformation rule on overlapping charts. -/
theorem coordinateComponent_isCoordinateTangentVector {p : M} (v : TangentSpace I p) :
    IsCoordinateTangentVector I p (coordinateComponent v) := by
  intro x y
  let ex := trivializationAt E (TangentSpace I) x.1
  let ey := trivializationAt E (TangentSpace I) y.1
  have hp : p ∈ ex.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H x.1).source ∩ (chartAt H y.1).source
    exact ⟨x.2, y.2⟩
  have hchange : ex.coordChangeL 𝕜 ey p = tangentCoordChange I x.1 y.1 p := by
    simpa [ex, ey] using tangent_coordinates_change hp
  calc
    tangentCoordChange I x.1 y.1 p (coordinateComponent v x)
      = ex.coordChangeL 𝕜 ey p (coordinateComponent v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (coordinateComponent v x)) hchange.symm
    _ = coordinateComponent v y := by
          rw [Bundle.Trivialization.coordChangeL_apply ex ey hp]
          have hx : ex.symm p (coordinateComponent v x) = v := by
            simpa [coordinateComponent, ex] using
              (ex.symm_apply_apply_mk x.2 v : ex.symm p (ex ⟨p, v⟩).2 = v)
          simpa [coordinateComponent, ey] using
            congrArg (fun w : TangentSpace I p ↦ (ey ⟨p, w⟩).2) hx

/-- **Math.** The compatible preferred-chart components of a tangent vector,
viewed as a `CoordinateTangentVector`. -/
def toCoordinateTangentVector {p : M} (v : TangentSpace I p) : CoordinateTangentVector I p :=
  ⟨coordinateComponent v, coordinateComponent_isCoordinateTangentVector v⟩

/-- **Math.** Reconstruct a tangent vector from a compatible family of
preferred-chart components by reading the family in the preferred chart centered
at the base point. -/
def CoordinateTangentVector.toTangentSpace {p : M} (v : CoordinateTangentVector I p) :
    TangentSpace I p :=
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  (trivializationAt E (TangentSpace I) p).symm p (v x)

/-- **Math.** Reconstructing a tangent vector from a compatible family and then
reading its component in any preferred chart returns the original family. -/
@[simp] theorem CoordinateTangentVector.coordinateComponent_toTangentSpace {p : M}
    (v : CoordinateTangentVector I p)
    (y : {x : M // p ∈ (chartAt H x).source}) :
    coordinateComponent v.toTangentSpace y = v y := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  let ey := trivializationAt E (TangentSpace I) y.1
  have hpy : p ∈ ep.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H p).source ∩ (chartAt H y.1).source
    exact ⟨mem_chart_source H p, y.2⟩
  have hchange : ep.coordChangeL 𝕜 ey p = tangentCoordChange I p y.1 p := by
    simpa [ep, ey] using tangent_coordinates_change hpy
  calc
    coordinateComponent v.toTangentSpace y
      = (ey ⟨p, ep.symm p (v x)⟩).2 := by
          simp [coordinateComponent, CoordinateTangentVector.toTangentSpace, ep, ey, x]
    _ = ep.coordChangeL 𝕜 ey p (v x) := by
          symm
          exact Bundle.Trivialization.coordChangeL_apply ep ey hpy (v x)
    _ = tangentCoordChange I p y.1 p (v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (v x)) hchange
    _ = v y := v.compatible x y

/-- **Math.** Reading the components of a tangent vector and reconstructing
returns the original tangent vector. -/
@[simp] theorem CoordinateTangentVector.toTangentSpace_toCoordinateTangentVector {p : M}
    (v : TangentSpace I p) :
    (toCoordinateTangentVector v).toTangentSpace = v := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  change ep.symm p ((ep ⟨p, v⟩).2) = v
  exact ep.symm_apply_apply_mk x.2 v

/-- **Math.** Reconstructing a tangent vector from a compatible family and then
taking its components returns the original family. -/
@[simp] theorem CoordinateTangentVector.toCoordinateTangentVector_toTangentSpace {p : M}
    (v : CoordinateTangentVector I p) :
    toCoordinateTangentVector v.toTangentSpace = v := by
  ext y
  exact CoordinateTangentVector.coordinateComponent_toTangentSpace v y

/-- **Math.** The coordinate-family realization of tangent vectors is canonically
equivalent to the tangent space itself: the two are the same object in different
presentations. -/
noncomputable def CoordinateTangentVector.equivTangentSpace (p : M) :
    CoordinateTangentVector I p ≃ TangentSpace I p where
  toFun := CoordinateTangentVector.toTangentSpace
  invFun := toCoordinateTangentVector
  left_inv := CoordinateTangentVector.toCoordinateTangentVector_toTangentSpace
  right_inv := CoordinateTangentVector.toTangentSpace_toCoordinateTangentVector

end Coordinate

end Manifold
