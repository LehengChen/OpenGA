import OpenGALib.Riemannian.Connection.ChartChristoffel

/-!
# Smoothness of the chart Christoffel symbols

`chartChristoffel g α i j k` is `C^∞` on the interior of the chart target. The
proof runs the standard chain: the chart Gram entries are smooth (pulled back
through the chart inverse), hence so is the inverse Gram (det ≠ 0 ⟹ entries are
smooth rational functions of the adjugate), and the Christoffel symbol is a
finite sum of products of inverse-Gram entries with first partial derivatives of
Gram entries.

Migrated from `external/differential-geometry` onto our `RiemannianMetric`;
builds on `Connection/ChartChristoffel` + `Metric/ChartGram`.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart helpers -/

lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source :=
  rfl

lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

/-! ## Gram / inverse-Gram entry smoothness -/

/-- The adjugate entries of the chart Gram matrix are `C^∞` (polynomial in the
Gram entries). -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp : (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ))).det) =
      (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
        (Equiv.Perm.sign σ : ℝ) *
          ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
              (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ) i
          (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
        (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-- The inverse Gram matrix entries are `C^∞` on the chart base set. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth : ContMDiffOn I 𝓘(ℝ) ∞
        (fun x : M => (chartGramMatrix (I := I) g α x).det)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

/-- The chart Gram entry pulled back to `E` is `C^∞` on the chart target. -/
lemma chartGramOnE_contDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- The pulled-back inverse Gram matrix entry on the chart target. -/
def chartInvGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

@[simp] lemma chartInvGramOnE_def
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y =
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

/-- The pulled-back inverse Gram entry is `C^∞` on the chart target. -/
lemma chartInvGramOnE_contDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartInvGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-! ## Christoffel smoothness -/

/-- **Smoothness of `chartChristoffel`.** The chart Christoffel symbol is `C^∞`
on the interior of the chart target. -/
theorem chartChristoffel_contDiffOn_interior
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : (chartChristoffel (I := I) g α i j k) =
      fun y : E =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    funext y
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hsum_smooth :
      ContDiffOn ℝ ∞
        (fun y : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y))
        (interior (extChartAt I α).target) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset
    · have hpartial : ∀ a p q : Fin (Module.finrank ℝ E),
          ContDiffOn ℝ ∞
            (partialDeriv (E := E) a (chartGramOnE (I := I) g α p q))
            (interior (extChartAt I α).target) := by
        intro a p q
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α p q)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α p q).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α p q))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      exact ((hpartial i l j).add (hpartial j l i)).sub (hpartial l i j)
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul hsum_smooth

end Riemannian

end
