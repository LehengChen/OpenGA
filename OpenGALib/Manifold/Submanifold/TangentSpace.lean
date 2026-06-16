import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Tangent space of a submanifold

The tangent space of a submanifold, viewed inside the ambient tangent space.
Once a smooth manifold structure on the subtype `S ⊆ M` is fixed, its tangent
space at a point is recorded as the image of the differential of the inclusion
`S ↪ M`: a submodule of the ambient tangent space, packaged with the notation
`T[J; p]`. This is the model-independent interface used wherever a submanifold's
tangent directions are needed inside the ambient manifold.

## Main definitions

* `Manifold.submanifoldTangentSpace` — the range of the inclusion's differential, as a submodule of
  the ambient tangent space.

Provenance: SmoothManifoldsLee a5f308c — Notation_5_35_extra_1.
-/

open scoped ContDiff Manifold

universe u𝕜 uE uH uM uE' uH'

namespace Manifold

section TangentSpaceToSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ⊤ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ⊤ S]

/-- **Math.** With the smooth manifold structure on the subtype `S` fixed, its tangent space at `p`,
viewed inside the ambient tangent space, is the range of the differential of the subtype inclusion
`S ↪ M`. -/
noncomputable abbrev submanifoldTangentSpace
    (J : ModelWithCorners 𝕜 E' H') (p : S) : Submodule 𝕜 (TangentSpace I (p : M)) :=
  (mfderiv J I (Subtype.val : S → M) p).range

@[inherit_doc]
scoped notation "T[" J "; " p "]" => submanifoldTangentSpace J p

end TangentSpaceToSubmanifold

end Manifold
