import OpenGALib.Riemannian.Geodesic.Equation
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option linter.unusedSectionVars false

/-!
# Parallel transport in chart coordinates — the linear ODE

For a Riemannian metric `g`, a basepoint `α : M`, a chart-velocity datum `u : ℝ → E`, and a
chart-coordinate curve `c : ℝ → E`, the parallel-transport equation `D_t V = 0` reads, in the
fixed chart at `α`, as the chart-coordinate **linear** ODE

`V' t = - Γ(g, α)(u t, V t)(c t)`,

where `Γ` is `Geodesic.chartChristoffelContraction g α`. Because that contraction is *bilinear*
in its two vector slots (see `chartChristoffelContraction_add_right`/`_smul_right` for the slot
we differentiate), the right-hand side is, for each fixed `t`, a continuous linear map
`E →L[ℝ] E` applied to `V t`. So the equation is a continuous time-dependent linear ODE on the
Banach (here finite-dimensional) space `E`.

This file is a self-contained Banach-space ODE result. It does **not** bridge to the genuine
`D_t V = 0` / `covDerivAlongCurve` equation (that is a separate, later piece).

## Main definitions

* `Geodesic.chartChristoffelContractionLinear g α a y` — the linear map
  `E →ₗ[ℝ] E`, `w ↦ chartChristoffelContraction g α a w y`.
* `Geodesic.chartChristoffelContractionContinuousLinear g α a y` — its continuous-linear-map
  packaging `E →L[ℝ] E` (continuity is automatic since `E` is finite-dimensional).

## Main results

* `Geodesic.continuousOn_chartChristoffelContractionContinuousLinear` — the time-dependent operator
  `t ↦ - chartChristoffelContractionContinuousLinear g α (u t) (c t)` is continuous (in operator norm) on
  any set on which `t ↦ chartChristoffelContraction g α (u t) w (c t)` is continuous for every
  fixed `w` — in particular when `u`, `c` are continuous and `c` lands in the chart interior.
* `Riemannian.exists_hasDerivAt_linear_ode_Ioo` — generic existence: for a continuous
  `A : ℝ → (E →L[ℝ] E)`, an initial time `t₀` and vector `v₀`, there is a small open interval
  about `t₀` and a curve `V` with `V t₀ = v₀` and `HasDerivAt V (A t (V t)) t` on the interval.
* `Riemannian.exists_parallelTransport_coord` — the chart-coordinate parallel-transport ODE
  existence, obtained by feeding the contraction operator into the generic result.
-/

noncomputable section

open Bundle Manifold Set Function Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The Christoffel contraction, as a *linear map* in the slot we differentiate.
For fixed `a y : E` the map `w ↦ Γ(g, α)(a, w)(y)` is `ℝ`-linear, by
`chartChristoffelContraction_add_right` and `chartChristoffelContraction_smul_right`. -/
def chartChristoffelContractionLinear (g : RiemannianMetric I M) (α : M) (a y : E) :
    E →ₗ[ℝ] E where
  toFun w := chartChristoffelContraction (I := I) g α a w y
  map_add' w₁ w₂ := chartChristoffelContraction_add_right (I := I) g α a w₁ w₂ y
  map_smul' s w := chartChristoffelContraction_smul_right (I := I) g α a s w y

@[simp] lemma chartChristoffelContractionLinear_apply
    (g : RiemannianMetric I M) (α : M) (a y w : E) :
    chartChristoffelContractionLinear (I := I) g α a y w =
      chartChristoffelContraction (I := I) g α a w y := rfl

/-- **Math.** The Christoffel contraction as a *continuous* linear map in the differentiated
slot. Since `E` is finite-dimensional, the linear map of
`chartChristoffelContractionLinear` is automatically continuous. -/
def chartChristoffelContractionContinuousLinear (g : RiemannianMetric I M) (α : M) (a y : E) :
    E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap (chartChristoffelContractionLinear (I := I) g α a y)

@[simp] lemma chartChristoffelContractionContinuousLinear_apply
    (g : RiemannianMetric I M) (α : M) (a y w : E) :
    chartChristoffelContractionContinuousLinear (I := I) g α a y w =
      chartChristoffelContraction (I := I) g α a w y := rfl

/-- **Math.** Continuity in time of the contraction operator
`t ↦ - chartChristoffelContractionContinuousLinear g α (u t) (c t)`, in operator norm, given pointwise
continuity of the underlying contraction. Because `E` is finite-dimensional, operator-norm
continuity is equivalent to continuity after applying to each fixed vector `w`, which is the
hypothesis `hcont`. -/
lemma continuousOn_chartChristoffelContractionContinuousLinear
    (g : RiemannianMetric I M) (α : M) (u c : ℝ → E) {s : Set ℝ}
    (hcont : ∀ w : E,
      ContinuousOn (fun t => chartChristoffelContraction (I := I) g α (u t) w (c t)) s) :
    ContinuousOn
      (fun t => - chartChristoffelContractionContinuousLinear (I := I) g α (u t) (c t)) s := by
  rw [continuousOn_clm_apply]
  intro w
  simp only [ContinuousLinearMap.neg_apply, chartChristoffelContractionContinuousLinear_apply]
  exact (hcont w).neg

end Geodesic

section GenericLinearODE

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Math.** Generic existence for a continuous time-dependent **linear** ODE on a Banach
space. Given a continuous operator `A : ℝ → (E →L[ℝ] E)`, an initial time `t₀` and initial
vector `v₀ : E`, there is a small open interval `(t₀ - ε, t₀ + ε)` and a curve `V : ℝ → E`
with `V t₀ = v₀` and `HasDerivAt V (A t (V t)) t` for every `t` in that interval.

The proof assembles Picard–Lindelöf: a linear vector field `(t, y) ↦ A t y` is globally
Lipschitz in `y` with constant `‖A t‖`, and continuous in `t` because `A` is. The construction
mirrors `Analysis.ODE.exists_isVariationalSolutionOn_Ioo_local` but for an *arbitrary*
continuous `A` rather than the linearization of a flow. -/
theorem exists_hasDerivAt_linear_ode_Ioo
    (A : ℝ → (E →L[ℝ] E)) (hA : Continuous A) (t₀ : ℝ) (v₀ : E) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : ℝ → E,
      V t₀ = v₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt V (A t (V t)) t := by
  classical
  -- A norm bound on `A` over the compact reference interval `Icc (t₀ - 1) (t₀ + 1)`.
  have hA_norm_cont : ContinuousOn (fun t => ‖A t‖) (Icc (t₀ - 1) (t₀ + 1)) :=
    (continuous_norm.comp hA).continuousOn
  obtain ⟨tM, _, htM_max⟩ :=
    isCompact_Icc.exists_isMaxOn
      (⟨t₀, ⟨by linarith, by linarith⟩⟩ : (Icc (t₀ - 1) (t₀ + 1)).Nonempty) hA_norm_cont
  set M : ℝ := ‖A tM‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hMbd : ∀ t ∈ Icc (t₀ - 1) (t₀ + 1), ‖A t‖ ≤ M := fun t ht => htM_max ht
  -- The vector field and the radii data for Picard–Lindelöf.
  set v : ℝ → E → E := fun t y => (A t) y with hv_def
  set r : ℝ := ‖v₀‖ with hr_def
  have hr_nn : 0 ≤ r := norm_nonneg _
  set a : ℝ := r + 1 with ha_def
  have ha_pos : 0 < a := by linarith
  set ε : ℝ := min 1 (1 / (M * a + 1)) with hε_def
  have hε : 0 < ε := by
    apply lt_min one_pos
    apply div_pos one_pos
    have : 0 ≤ M * a := mul_nonneg hM_nn (le_of_lt ha_pos)
    linarith
  have hε_le_one : ε ≤ 1 := min_le_left _ _
  have hMa_eps : M * a * ε ≤ 1 := by
    have h1 : ε ≤ 1 / (M * a + 1) := min_le_right _ _
    have hMa_nn : 0 ≤ M * a := mul_nonneg hM_nn (le_of_lt ha_pos)
    have hMa1_pos : 0 < M * a + 1 := by linarith
    have h2 : M * a * ε ≤ M * a * (1 / (M * a + 1)) :=
      mul_le_mul_of_nonneg_left h1 hMa_nn
    have h3 : M * a * (1 / (M * a + 1)) = M * a / (M * a + 1) := by ring
    have h4 : M * a / (M * a + 1) ≤ 1 := by
      rw [div_le_one hMa1_pos]; linarith
    linarith
  let tmin : ℝ := t₀ - ε
  let tmax : ℝ := t₀ + ε
  have htmin_le_tmax : tmin ≤ tmax := by change t₀ - ε ≤ t₀ + ε; linarith
  let t₀Icc : Icc tmin tmax :=
    ⟨t₀, ⟨by change t₀ - ε ≤ t₀; linarith, by change t₀ ≤ t₀ + ε; linarith⟩⟩
  have hIcc_sub : Icc tmin tmax ⊆ Icc (t₀ - 1) (t₀ + 1) := by
    intro τ hτ
    refine ⟨le_trans (by change t₀ - 1 ≤ t₀ - ε; linarith) hτ.1,
      le_trans hτ.2 (by change t₀ + ε ≤ t₀ + 1; linarith)⟩
  let aN : ℝ≥0 := ⟨a, le_of_lt ha_pos⟩
  let rN : ℝ≥0 := ⟨r, hr_nn⟩
  let LN : ℝ≥0 := ⟨M * a, mul_nonneg hM_nn (le_of_lt ha_pos)⟩
  let KN : ℝ≥0 := ⟨M, hM_nn⟩
  have hpl : IsPicardLindelof v t₀Icc (0 : E) aN rN LN KN := by
    refine
    { lipschitzOnWith := ?_,
      continuousOn := ?_,
      norm_le := ?_,
      mul_max_le := ?_ }
    · intro τ hτ
      have hτ_ref : τ ∈ Icc (t₀ - 1) (t₀ + 1) := hIcc_sub hτ
      have hlip : LipschitzWith KN (A τ) :=
        (A τ).lipschitzWith_of_opNorm_le (hMbd τ hτ_ref)
      exact LipschitzWith.lipschitzOnWith (s := closedBall (0 : E) aN) hlip
    · intro y _
      have happly : Continuous (fun B : E →L[ℝ] E => B y) :=
        (ContinuousLinearMap.apply ℝ E y).continuous
      exact (happly.comp hA).continuousOn
    · intro τ hτ y hy
      have hτ_ref : τ ∈ Icc (t₀ - 1) (t₀ + 1) := hIcc_sub hτ
      have hA_norm : ‖A τ‖ ≤ M := hMbd τ hτ_ref
      have hy_norm : ‖y‖ ≤ a := by
        simpa [mem_closedBall_zero_iff] using hy
      change ‖v τ y‖ ≤ (LN : ℝ)
      calc ‖v τ y‖ = ‖(A τ) y‖ := rfl
        _ ≤ ‖A τ‖ * ‖y‖ := (A τ).le_opNorm y
        _ ≤ M * a := mul_le_mul hA_norm hy_norm (norm_nonneg _) hM_nn
    · change (LN : ℝ) * max (tmax - t₀) (t₀ - tmin) ≤ (aN : ℝ) - (rN : ℝ)
      have hmax_eq : max (tmax - t₀) (t₀ - tmin) = ε := by
        have h1 : tmax - t₀ = ε := by change (t₀ + ε) - t₀ = ε; ring
        have h2 : t₀ - tmin = ε := by change t₀ - (t₀ - ε) = ε; ring
        rw [h1, h2]; exact max_self _
      rw [hmax_eq]
      have hLrhs : (aN : ℝ) - (rN : ℝ) = 1 := by change a - r = 1; rw [ha_def]; ring
      rw [hLrhs]
      change M * a * ε ≤ 1
      exact hMa_eps
  have hv₀_mem : v₀ ∈ closedBall (0 : E) rN := by
    rw [mem_closedBall_zero_iff]; change ‖v₀‖ ≤ r; rfl
  obtain ⟨V, hV_init, hV_deriv⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt hv₀_mem
  refine ⟨ε, hε, V, hV_init, ?_⟩
  intro τ hτ
  have hτ_Icc : τ ∈ Icc tmin tmax := ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
  have hd := hV_deriv τ hτ_Icc
  have hd' := hd.mono (Ioo_subset_Icc_self (a := tmin) (b := tmax))
  exact hd'.hasDerivAt (isOpen_Ioo.mem_nhds hτ)

end GenericLinearODE

section ChartParallelTransport

open Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Chart-coordinate parallel-transport existence (linear ODE form).**
Given a Riemannian metric `g`, a basepoint `α : M`, chart data `u c : ℝ → E` such that the
contraction `t ↦ Γ(g, α)(u t, w)(c t)` is continuous for every fixed `w` (e.g. when `u`, `c`
are continuous and `c` stays in the chart interior), an initial time `t₀` and initial vector
`v₀ : E`, there exist `ε > 0` and `V : ℝ → E` with `V t₀ = v₀` solving the linear ODE

`HasDerivAt V (- chartChristoffelContraction g α (u t) (V t) (c t)) t`

on `(t₀ - ε, t₀ + ε)`. This is the chart-coordinate form of the parallel-transport equation
`D_t V = 0`; the bridge to the intrinsic `covDerivAlongCurve` form is a separate later piece. -/
theorem exists_parallelTransport_coord
    (g : RiemannianMetric I M) (α : M) (u c : ℝ → E)
    (hcont : ∀ w : E,
      Continuous (fun t => chartChristoffelContraction (I := I) g α (u t) w (c t)))
    (t₀ : ℝ) (v₀ : E) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ V : ℝ → E,
      V t₀ = v₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt V
          (- chartChristoffelContraction (I := I) g α (u t) (V t) (c t)) t := by
  -- Package the right-hand side as a continuous family of continuous linear maps.
  set A : ℝ → (E →L[ℝ] E) :=
    fun t => - chartChristoffelContractionContinuousLinear (I := I) g α (u t) (c t) with hA_def
  have hA : Continuous A := by
    rw [← continuousOn_univ]
    have := continuousOn_chartChristoffelContractionContinuousLinear (I := I) g α u c
      (s := (Set.univ : Set ℝ)) (fun w => (hcont w).continuousOn)
    simpa [hA_def] using this
  obtain ⟨ε, hε, V, hV_init, hV_deriv⟩ :=
    Riemannian.exists_hasDerivAt_linear_ode_Ioo A hA t₀ v₀
  refine ⟨ε, hε, V, hV_init, ?_⟩
  intro t ht
  have hd := hV_deriv t ht
  have hAeq : A t (V t)
      = - chartChristoffelContraction (I := I) g α (u t) (V t) (c t) := by
    simp [hA_def]
  rwa [hAeq] at hd

end ChartParallelTransport

end Riemannian

end
