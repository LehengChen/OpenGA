import OpenGALib.Riemannian.Volume.ChartPullbackFormula
import OpenGALib.Riemannian.Exponential.NormalBallSmooth

/-!
# Exponential-map volume bridge (change-of-variables core)

The [C] leg of Bishop–Gromov: expressing the Riemannian volume of an
exponential image in exponential-normal coordinates.

Combining the chart-coordinate volume integral
(`volumeMeasure_eq_setLIntegral_chartSqrtGramDet`, the keystone's consequence)
with the Lebesgue change-of-variables formula
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) along the chart-pushed
exponential `T = φ ∘ exp_p` turns the chart-coordinate density into the
exp-coordinate density: for a measurable `W ⊆ T_p M`,

  `vol_g(exp_p '' W) = ∫_W |det d(φ ∘ exp_p)(w)| · √det(g)(exp_p w) dLeb(w)`.

This file proves that change-of-variables core, parametrized by the
differentiability/injectivity of the chart-pushed exponential on `W` (which the
local-diffeomorphism witness `exists_open_nhds_expMap_diffeoOn` discharges — done
separately). The product `|det d(φ∘exp_p)| · √det(g)∘exp_p` is the volume
Jacobian of `exp_p`; identifying it with the geometric `|det d exp_p|` (metric in
normal coordinates) is the remaining geometric step.
-/

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff
open Riemannian.Tensor Riemannian.Exponential

namespace Riemannian

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

/-- **Math.** **Fréchet derivative of the chart-pushed exponential.** Where
`exp_p` is `C¹` (`ContMDiffOn`) into a single chart source, its chart
representation `T = extChartAt p ∘ exp_p : E → E` is Fréchet-differentiable: it
`HasFDerivWithinAt` its `fderivWithin`. This is the differentiability input the
exp-volume change of variables (`volumeMeasure_expImage_eq_setLIntegral_jacobian`)
consumes; combined with the chart smoothness `contMDiffOn_extChartAt` it converts
manifold smoothness of `exp_p` into a genuine `E`-level Fréchet derivative. -/
theorem chartExp_hasFDerivWithinAt
    {g : RiemannianMetric I M} {p : M} {W : Set E}
    (hexp : ContMDiffOn 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) W)
    (hsub : ∀ w ∈ W,
      (expMap (I := I) g p (show TangentSpace I p from w) : M) ∈ (chartAt H p).source)
    {w : E} (hw : w ∈ W) :
    HasFDerivWithinAt
      (fun w : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from w)))
      (fderivWithin ℝ
        (fun w : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from w)))
        W w) W w := by
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun w : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from w))) W :=
    (contMDiffOn_extChartAt (I := I) (n := 1) (x := p)).comp hexp hsub
  have hcd : ContDiffOn ℝ 1
      (fun w : E => extChartAt I p (expMap (I := I) g p (show TangentSpace I p from w))) W :=
    contMDiffOn_iff_contDiffOn.mp hcomp
  exact (hcd.differentiableOn_one w hw).hasFDerivWithinAt

/-- **Math.** `exp_p` is injective on the source of the local-diffeomorphism
witness — an open normal ball around `0`. This is the injectivity input the
exp-volume change of variables needs; it comes from the partial diffeomorphism
`Φ` (`exists_open_nhds_expMap_diffeoOn`), which is injective on its source and
agrees with `exp_p` there. -/
theorem exists_expMap_injOn_nhds_zero (g : RiemannianMetric I M) (p : M) :
    ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧
      Set.InjOn
        (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) W := by
  obtain ⟨Φ, h0, hΦeq⟩ := exists_open_nhds_expMap_diffeoOn (I := I) g p
  refine ⟨Φ.source, Φ.open_source, h0, ?_⟩
  have heqon : Set.EqOn (Φ : E → M)
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      Φ.source := fun v hv => hΦeq v hv
  exact (Φ.toPartialEquiv.injOn).congr heqon

/-- **Math.** **Exp-volume bridge (change-of-variables core).** For a measurable
`W ⊆ T_p M` whose exponential image is open and contained in a single chart
source, on which the chart-pushed exponential `T = φ ∘ exp_p` (`φ = extChartAt p`)
is differentiable with derivative `T'` and injective, the Riemannian volume of
`exp_p '' W` is the exp-coordinate integral of the volume Jacobian:
`vol_g(exp_p '' W) = ∫_W |det T'(w)| · √det(g)(exp_p w) dLeb(w)`. -/
theorem volumeMeasure_expImage_eq_setLIntegral_jacobian
    (g : RiemannianMetric I M) (p : M) {W : Set E} {T' : E → (E →L[ℝ] E)}
    (hWmeas : MeasurableSet W)
    (hexpOpen : IsOpen
      ((fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W))
    (hexpSub :
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W
        ⊆ (chartAt H p).source)
    (hT' : ∀ w ∈ W, HasFDerivWithinAt
      (fun w : E => extChartAt I p
        (expMap (I := I) g p (show TangentSpace I p from w))) (T' w) W w)
    (hTinj : InjOn
      (fun w : E => extChartAt I p
        (expMap (I := I) g p (show TangentSpace I p from w))) W) :
    volumeMeasure g
        ((fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W)
      = ∫⁻ w in W, ENNReal.ofReal |(T' w).det| *
          ENNReal.ofReal (chartSqrtGramDet (I := I) g p
            (expMap (I := I) g p (show TangentSpace I p from w)))
          ∂(modelHaar (E := E)) := by
  -- chart-coordinate volume integral (#1).
  rw [volumeMeasure_eq_setLIntegral_chartSqrtGramDet g p hexpOpen hexpSub]
  -- the chart image of the exp image is the image of the chart-pushed exp.
  rw [Set.image_image]
  -- Lebesgue change of variables along `T = φ ∘ exp_p`.
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (modelHaar (E := E)) hWmeas hT' hTinj]
  -- identify `φ.symm (T w) = exp_p w` on `W` (since `exp_p w ∈ source`).
  refine setLIntegral_congr_fun hWmeas (fun w hw => ?_)
  have hmem : (expMap (I := I) g p (show TangentSpace I p from w) : M)
      ∈ (extChartAt I p).source := by
    rw [extChartAt_source]; exact hexpSub ⟨w, hw, rfl⟩
  rw [(extChartAt I p).left_inv hmem]

end Riemannian
