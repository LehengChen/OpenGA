import OpenGALib.Riemannian.TensorBundle.MusicalIso

/-!
# Chart-coordinate Christoffel symbols

The Levi-Civita Christoffel symbols `Γᵏ_{ij}` expressed in a chart at `α`,
computed directly from the metric Gram matrix in coordinates via the textbook
formula `Γᵏ_{ij} = ½ Gᵏˡ (∂ᵢG_{lj} + ∂ⱼG_{li} − ∂_lG_{ij})`. These coordinate
symbols are what the geodesic equation `γ'' = −Γ(γ', γ')` is written against.

Built on OpenGALib's existing chart-Gram foundation (`TensorBundle/MusicalIso`:
`chartGramMatrix`, `chartInvGramMatrix` and their smoothness, in the
`Module.finBasis ℝ E` chart frame). Migrated from `external/differential-geometry`
(reference only) and **rebased onto the existing Gram infrastructure** rather
than duplicating it.

Reference: do Carmo Ch.2; Lee, *Riemannian Manifolds* Ch.5.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The partial derivative of `u : E → ℝ` at `y` along the `i`-th
chart-frame basis vector `(Module.finBasis ℝ E) i` (the same basis underlying
`chartGramMatrix`). -/
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

/-- **Math.** The chart Gram entry `G_{ij}(α, ·)` pulled back to the chart target
via the chart inverse. -/
def chartGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

@[simp] lemma chartGramOnE_def
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

/-- **Math.** Symmetry of the chart Gram entries pulled back to `E`. -/
lemma chartGramOnE_symm
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y = chartGramOnE (I := I) g α j i y := by
  unfold chartGramOnE
  rw [chartGramMatrix_apply, chartGramMatrix_apply]
  exact g.symm _ _ _

/-- **Math.** The chart-coordinate **Christoffel symbol** of the second kind at
`α`: `Γᵏ_{ij}(g, α)(y) = ½ Σ_l Gᵏˡ(α, x_y) (∂ᵢG_{lj} + ∂ⱼG_{li} − ∂_lG_{ij})(y)`,
with `x_y := (extChartAt I α).symm y`, using the existing `chartGramMatrix` /
`chartInvGramMatrix`. -/
def chartChristoffel (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

@[simp] lemma chartChristoffel_def
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

/-- **Math.** **Symmetry of the Christoffel symbol** in the lower indices — the
torsion-free property of the Levi-Civita connection, read off the coordinate
formula. -/
theorem chartChristoffel_symm
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

end Riemannian

end
