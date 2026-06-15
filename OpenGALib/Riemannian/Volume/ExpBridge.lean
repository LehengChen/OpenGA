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

/-- **Math.** **Exp-volume bridge (unconditional, on a normal ball).** There is an
open neighborhood `W` of `0 ∈ T_p M` on which the exp-volume change of variables
holds with no side hypotheses: the Riemannian volume of `exp_p '' W` equals the
exp-coordinate integral of the volume Jacobian
`|det d(φ ∘ exp_p)| · √det(g) ∘ exp_p`. This discharges the three side conditions
of `volumeMeasure_expImage_eq_setLIntegral_jacobian` — image openness, containment
in a single chart source, and injectivity of the chart-pushed exponential — from
the single local-diffeomorphism witness `Φ = exists_open_nhds_expMap_diffeoOn`,
taking `W = Φ.source ∩ exp_p⁻¹(chart source p)`. The chart-pushed exponential
`T = extChartAt p ∘ exp_p` is realized as the open map `Φ.toOpenPartialHomeomorph`
on `W ⊆ Φ.source`, so `IsOpen (exp_p '' W)` comes from
`OpenPartialHomeomorph.isOpen_image_of_subset_source` rather than the
local-homeomorphism layer (which lacks an open-map API). -/
theorem exists_volumeMeasure_expImage_eq_setLIntegral_jacobian
    (g : RiemannianMetric I M) (p : M) :
    ∃ W : Set E, IsOpen W ∧ (0 : E) ∈ W ∧
      volumeMeasure g
          ((fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W)
        = ∫⁻ w in W, ENNReal.ofReal
            |(fderivWithin ℝ
                (fun w : E => extChartAt I p
                  (expMap (I := I) g p (show TangentSpace I p from w))) W w).det| *
            ENNReal.ofReal (chartSqrtGramDet (I := I) g p
              (expMap (I := I) g p (show TangentSpace I p from w)))
            ∂(modelHaar (E := E)) := by
  obtain ⟨Φ, h0, hΦeq⟩ := exists_open_nhds_expMap_diffeoOn (I := I) g p
  -- `exp_p` agrees with the diffeomorphism `Φ` on `Φ.source`, hence is `C¹` there.
  have hexpcont : ContMDiffOn 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) Φ.source :=
    Φ.contMDiffOn_toFun.congr (fun w hw => (hΦeq w hw).symm)
  -- `W = Φ.source ∩ exp_p⁻¹(chart source p)` is open and contains `0`.
  set W : Set E := Φ.source ∩
    (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) ⁻¹'
      (chartAt H p).source with hWdef
  have hWopen : IsOpen W :=
    hexpcont.continuousOn.isOpen_inter_preimage Φ.open_source (chartAt H p).open_source
  have hW0 : (0 : E) ∈ W := by
    refine ⟨h0, ?_⟩
    show (expMap (I := I) g p (show TangentSpace I p from (0 : E)) : M) ∈ (chartAt H p).source
    have hp0 : (expMap (I := I) g p (show TangentSpace I p from (0 : E)) : M) = p :=
      expMap_zero (I := I) g p
    rw [hp0]; exact mem_chart_source H p
  have hWsub : W ⊆ Φ.source := Set.inter_subset_left
  -- restrict the smoothness and the chart-containment to `W`.
  have hexpW : ContMDiffOn 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) W :=
    hexpcont.mono hWsub
  have hsubW : ∀ w ∈ W,
      (expMap (I := I) g p (show TangentSpace I p from w) : M) ∈ (chartAt H p).source :=
    fun w hw => hw.2
  -- image openness: `exp_p '' W = Φ '' W`, and `Φ` is an open map on its source.
  have heqonΦ : Set.EqOn (Φ.toOpenPartialHomeomorph : E → M)
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) W :=
    fun w hw => hΦeq w (hWsub hw)
  have hImgOpen : IsOpen
      ((fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W) :=
    heqonΦ.image_eq ▸ Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hWopen hWsub
  -- image-in-chart-source from the preimage cut.
  have hExpSub :
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) '' W
        ⊆ (chartAt H p).source :=
    Set.MapsTo.image_subset (fun w hw => hsubW w hw)
  -- Fréchet derivative of the chart-pushed exponential on `W`.
  have hT' : ∀ w ∈ W, HasFDerivWithinAt
      (fun w : E => extChartAt I p
        (expMap (I := I) g p (show TangentSpace I p from w)))
      (fderivWithin ℝ
        (fun w : E => extChartAt I p
          (expMap (I := I) g p (show TangentSpace I p from w))) W w) W w :=
    fun w hw => chartExp_hasFDerivWithinAt hexpW hsubW hw
  -- injectivity of `T = extChartAt p ∘ exp_p` on `W`.
  have hexpInj : Set.InjOn
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) W :=
    ((Φ.toPartialEquiv.injOn).congr (fun w hw => hΦeq w hw)).mono hWsub
  have hmapsExt : Set.MapsTo
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) W
      (extChartAt I p).source := by
    intro w hw; rw [extChartAt_source]; exact hsubW w hw
  have hTinj : Set.InjOn
      (fun w : E => extChartAt I p
        (expMap (I := I) g p (show TangentSpace I p from w))) W :=
    (extChartAt I p).injOn.comp hexpInj hmapsExt
  exact ⟨W, hWopen, hW0,
    volumeMeasure_expImage_eq_setLIntegral_jacobian g p hWopen.measurableSet
      hImgOpen hExpSub hT' hTinj⟩

/-- **Math.** **Chart-pushed exp derivative is the chart coordinate of `d exp_p`.**
On an open set `W` where `exp_p` is `MDifferentiableAt` into a single chart source,
the Fréchet derivative `T'(w) = d(extChartAt p ∘ exp_p)` of the chart-pushed
exponential factors through the manifold differential of `exp_p`:
`T'(w) = d(extChartAt p)_{exp_p w} ∘ d(exp_p)_w`. This is the bridge from the
`E`-level change-of-variables Jacobian `T'` to the intrinsic differential
`mfderiv (exp_p)`, the input to identifying the volume Jacobian
`|det T'| · √det(g)∘exp_p` with the metric volume of the pushed-forward frame
`{d exp_p(w) eᵢ}`. Proof: on the open `W`, `fderivWithin = fderiv`; on the model
space `fderiv = mfderiv`; then the manifold chain rule `mfderiv_comp`. -/
theorem chartExp_fderivWithin_eq_mfderiv_comp
    {g : RiemannianMetric I M} {p : M} {W : Set E} (hWopen : IsOpen W)
    (hexpDiff : ∀ w ∈ W, MDifferentiableAt 𝓘(ℝ, E) I
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) w)
    (hsub : ∀ w ∈ W,
      (expMap (I := I) g p (show TangentSpace I p from w) : M) ∈ (chartAt H p).source)
    {w : E} (hw : w ∈ W) :
    fderivWithin ℝ
      (fun w : E => extChartAt I p
        (expMap (I := I) g p (show TangentSpace I p from w))) W w
      = (mfderiv I 𝓘(ℝ, E) (extChartAt I p)
          (expMap (I := I) g p (show TangentSpace I p from w))).comp
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) w) := by
  rw [fderivWithin_of_isOpen hWopen hw, ← mfderiv_eq_fderiv]
  exact mfderiv_comp w (mdifferentiableAt_extChartAt (hsub w hw)) (hexpDiff w hw)

/-- **Math.** The determinant of (the underlying continuous linear map of) a
continuous linear self-equivalence is nonzero: it is the coercion of the unit
`LinearEquiv.det`. -/
theorem continuousLinearEquiv_coe_det_ne_zero (Ξ : E ≃L[ℝ] E) :
    (Ξ : E →L[ℝ] E).det ≠ 0 := by
  have hval : (Ξ : E →L[ℝ] E).det = ((Ξ.toLinearEquiv.det : ℝˣ) : ℝ) := by
    have e1 : (Ξ : E →L[ℝ] E).det = LinearMap.det (Ξ.toLinearEquiv : E →ₗ[ℝ] E) := rfl
    rw [e1, ← LinearEquiv.coe_det]
  rw [hval]
  exact Units.ne_zero _

/-- **Math.** **Positivity of the exp-volume Jacobian.** On the normal ball `W`
(open, exp `MDifferentiableAt` and a local diffeomorphism into one chart source),
the change-of-variables density `|det T'(w)| · √det(g)(exp_p w)` of
`volumeMeasure_expImage_eq_setLIntegral_jacobian` is strictly positive: the chart
factor `chartSqrtGramDet` is positive on the chart source, and the Jacobian
`T'(w) = d(extChartAt p ∘ exp_p)` is invertible — it is the composition of the
chart-trivialization equivalence with the local-diffeomorphism differential
`d exp_p`, so `det T'(w) ≠ 0`. This is the nondegeneracy the geodesic-polar volume
formula and the `∂_t log J = Δr` step consume. -/
theorem chartExp_volumeJacobian_pos
    {g : RiemannianMetric I M} {p : M} {W : Set E} (hWopen : IsOpen W)
    (hexpDiff : ∀ w ∈ W, MDifferentiableAt 𝓘(ℝ, E) I
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) w)
    (hsub : ∀ w ∈ W,
      (expMap (I := I) g p (show TangentSpace I p from w) : M) ∈ (chartAt H p).source)
    (hloc : ∀ w ∈ W, IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1
      (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) w)
    {w : E} (hw : w ∈ W) :
    0 < |(fderivWithin ℝ
            (fun w : E => extChartAt I p
              (expMap (I := I) g p (show TangentSpace I p from w))) W w).det|
        * chartSqrtGramDet (I := I) g p
            (expMap (I := I) g p (show TangentSpace I p from w)) := by
  have hq : (expMap (I := I) g p (show TangentSpace I p from w) : M) ∈ (chartAt H p).source :=
    hsub w hw
  have hqbase : (expMap (I := I) g p (show TangentSpace I p from w) : M)
      ∈ (trivializationAt E (TangentSpace I) p).baseSet := hq
  -- the chart volume factor is positive on the chart source.
  have hgram : 0 < chartSqrtGramDet (I := I) g p
      (expMap (I := I) g p (show TangentSpace I p from w)) :=
    chartSqrtGramDet_pos g p hqbase
  -- the Jacobian `T'(w)` factors as chart-trivialization ∘ `d exp_p`, both invertible.
  have hbridge := chartExp_fderivWithin_eq_mfderiv_comp hWopen hexpDiff hsub hw
  -- `d exp_p w` and `d(extChartAt p)_{exp_p w}` as continuous linear equivalences.
  let A_e := (trivializationAt E (TangentSpace I) p).continuousLinearEquivAt ℝ
    (expMap (I := I) g p (show TangentSpace I p from w)) hqbase
  let B_e := expMap_mfderivContinuousLinearEquiv (hloc w hw)
  have hAcoe : (A_e : TangentSpace I (expMap (I := I) g p (show TangentSpace I p from w))
      →L[ℝ] E) = mfderiv I 𝓘(ℝ, E) (extChartAt I p)
        (expMap (I := I) g p (show TangentSpace I p from w)) := by
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt hq]
    exact (trivializationAt E (TangentSpace I) p).coe_continuousLinearEquivAt_eq' hqbase
  -- the composite is the coercion of the continuous linear equivalence `B_e.trans A_e`.
  have hcomp : (mfderiv I 𝓘(ℝ, E) (extChartAt I p)
        (expMap (I := I) g p (show TangentSpace I p from w))).comp
        (mfderiv 𝓘(ℝ, E) I
          (fun w : E => (expMap (I := I) g p (show TangentSpace I p from w) : M)) w)
      = ((show E ≃L[ℝ] E from B_e.trans A_e) : E →L[ℝ] E) := by
    rw [← hAcoe]
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rfl
  rw [hbridge]
  refine mul_pos (abs_pos.mpr ?_) hgram
  rw [hcomp]
  exact continuousLinearEquiv_coe_det_ne_zero _

end Riemannian
