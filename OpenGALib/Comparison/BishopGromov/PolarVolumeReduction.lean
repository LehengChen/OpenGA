import OpenGALib.Comparison.BishopGromov.VolumeMonotone
import OpenGALib.Comparison.Util.SnakeCalculus

/-!
# Polar volume reduction

The analytic glue between the volume-ratio monotonicity engine
(`ratio_intervalIntegral_le`) and the space-form ball volume
`spaceFormBallVolume` that appears in the headline
`bishopGromov_volume_comparison`.

The model ball volume unfolds, by definition, to a positive constant times the
radial integral of the model area density,
`V_K^n(R) = (n · ωₙ) · ∫₀ᴿ max(0, s_K(t))^(n-1) dt`. So the model ball volume is
exactly the integrated model area density `B_K(t) = max(0, s_K(t))^(n-1)` scaled
by the constant `n · ωₙ`. Feeding `B_K` into `ratio_intervalIntegral_le` — with
`B_K > 0` on the admissible window via `snakeFunction_pos`, and `B_K` continuous
hence interval-integrable — turns a pointwise "geodesic-sphere area over model
area" antitonicity hypothesis into the integrated ratio comparison
`(∫₀ᴿ A) / V_K^n(R) ↓`, which is the shape of Bishop–Gromov.

This step is pure real analysis: it carries no geometry, only the bookkeeping
that splits off the dimensional constant `n · ωₙ` and verifies the model density
is positive and integrable on the admissible window.

Reference: comparison-geometry notes CH21; do Carmo Ch.10 §2; Petersen Ch.9.
-/

open MeasureTheory Set
open scoped Real

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** Dividing by a fixed nonnegative scalar is monotone:
`a ≤ b` and `0 ≤ X` give `a / X ≤ b / X`. -/
private theorem div_le_div_of_le_const {a b X : ℝ} (h : a ≤ b) (hX : 0 ≤ X) :
    a / X ≤ b / X := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hX)

/-- **Math.** Scaling both denominators by a common nonnegative constant `C`
preserves a ratio inequality: `a/G ≤ b/H` and `0 ≤ C` give
`a/(C·G) ≤ b/(C·H)`. (`C` is an opaque parameter, so the division-rearranging
rewrites do not re-split it.) -/
private theorem div_mul_const_le {a b G H C : ℝ}
    (h : a / G ≤ b / H) (hC : 0 ≤ C) :
    a / (C * G) ≤ b / (C * H) := by
  rw [div_mul_eq_div_div_swap, div_mul_eq_div_div_swap]
  exact div_le_div_of_le_const h hC

/-- **Math.** **Polar volume reduction.** If the pointwise ratio of a radial
density `A` to the model area density `B_K(t) = max(0, s_K(t))^(n-1)` is
non-increasing on `Ioc 0 R`, then the ratio of the radial integral of `A` to the
space-form ball volume `V_K^n` is non-increasing on the admissible window:
`r ≤ R ⟹ (∫₀ᴿ A) / V_K^n(R) ≤ (∫₀ʳ A) / V_K^n(r)`.

This adapts the purely analytic volume-ratio monotonicity engine
`ratio_intervalIntegral_le` to the model ball volume `spaceFormBallVolume`, which
unfolds to `(n · ωₙ) · ∫₀ᴿ B_K`. The constant `n · ωₙ ≥ 0` divides out of the
ratio; positivity of `B_K` on the window comes from `snakeFunction_pos`, and
continuity of `B_K` gives interval integrability. -/
theorem ratio_spaceFormBallVolume_le
    {n : ℕ} {K : ℝ} {A : ℝ → ℝ} {r R : ℝ}
    (hr : r ∈ spaceFormAdmissibleRadii K) (hR : R ∈ spaceFormAdmissibleRadii K)
    (hrR : r ≤ R)
    (hAi : IntervalIntegrable A volume 0 R)
    (hq : AntitoneOn (fun t => A t / max 0 (snakeFunction K t) ^ (n - 1))
      (Set.Ioc 0 R)) :
    (∫ t in (0)..R, A t) / spaceFormBallVolume n K R
      ≤ (∫ t in (0)..r, A t) / spaceFormBallVolume n K r := by
  -- `r > 0` from admissibility.
  have hr0 : 0 < r := by
    unfold spaceFormAdmissibleRadii at hr; split_ifs at hr with hK
    · exact hr.1
    · exact hr
  -- `B_K > 0` on `Ioc 0 R`: every such `s` is admissible, so `s_K(s) > 0`.
  have hBpos : ∀ s ∈ Set.Ioc 0 R, 0 < max 0 (snakeFunction K s) ^ (n - 1) := by
    intro s hs
    have hsadm : s ∈ spaceFormAdmissibleRadii K :=
      mem_spaceFormAdmissibleRadii_of_le hs.1 hs.2 hR
    have hpos := snakeFunction_pos hsadm
    rw [max_eq_right hpos.le]
    exact pow_pos hpos _
  -- `B_K` is continuous, hence interval-integrable.
  have hBi : IntervalIntegrable (fun t => max 0 (snakeFunction K t) ^ (n - 1))
      volume 0 R := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.max (continuous_snakeFunction K)).pow (n - 1)
  -- The monotone-average engine on the pointwise ratio `A / B_K`.
  have Qmono : (∫ t in (0)..R, A t) / (∫ t in (0)..R, max 0 (snakeFunction K t) ^ (n - 1))
      ≤ (∫ t in (0)..r, A t) / (∫ t in (0)..r, max 0 (snakeFunction K t) ^ (n - 1)) :=
    ratio_intervalIntegral_le hr0 hrR hBpos hAi hBi hq
  -- The model ball volume is `V_K^n = (n · ωₙ) · ∫₀ B_K` by definition.
  have hdefR : spaceFormBallVolume n K R
      = ((n : ℝ) * (MeasureTheory.volume
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)
        * (∫ t in (0:ℝ)..R, max 0 (snakeFunction K t) ^ (n - 1)) := rfl
  have hdefr : spaceFormBallVolume n K r
      = ((n : ℝ) * (MeasureTheory.volume
          (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)
        * (∫ t in (0:ℝ)..r, max 0 (snakeFunction K t) ^ (n - 1)) := rfl
  rw [hdefR, hdefr]
  refine div_mul_const_le Qmono ?_
  positivity

end OpenGA.Comparison.BishopGromov
