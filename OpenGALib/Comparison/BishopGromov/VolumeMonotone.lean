import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Volume-ratio monotonicity engine

The final, purely real-analytic step of Bishop–Gromov: if the *pointwise* ratio
`A/B` of two radial densities is non-increasing, then the *integrated* ratio
`(∫₀ᴿ A)/(∫₀ᴿ B)` is non-increasing in `R`. In the geometric application
`A(t) = ∫_{Sⁿ⁻¹} j(v,t) dv` is the geodesic-sphere area, `B(t) = s_K(t)ⁿ⁻¹` the
model area, `A/B` is non-increasing by the Laplacian comparison, and the
conclusion is exactly the volume-ratio monotonicity
`vol B(p,R) / V_K(R) ↓`.

The proof is the weighted form of the monotone-average lemma
(comparison-geometry notes CH21, "monotone average integral"): split
`∫₀ᴿ = ∫₀ʳ + ∫ᵣᴿ` and pivot on the value `q(r)` to compare the tail average on
`[r,R]` with the head average on `[0,r]`, avoiding any double integral.

Reference: comparison-geometry notes CH21 (Lemma "monotone average integral");
do Carmo Ch.10 §2; Petersen Ch.9.
-/

open MeasureTheory Set
open scoped Real

namespace OpenGA.Comparison.BishopGromov

variable {A B : ℝ → ℝ} {r R : ℝ}

/-- **Math.** Pivoted tail/head comparison: if `A/B` is non-increasing on `Ioc 0 R`
and `B > 0` there, then the tail integral of `A` against the head mass of `B` is
dominated by the head integral of `A` against the tail mass of `B`:
`(∫₀ʳ B) · (∫ᵣᴿ A) ≤ (∫₀ʳ A) · (∫ᵣᴿ B)`. -/
theorem head_mass_mul_tail_le
    (hr : 0 < r) (hrR : r ≤ R)
    (hB : ∀ s ∈ Ioc 0 R, 0 < B s)
    (hAi : IntervalIntegrable A volume 0 R)
    (hBi : IntervalIntegrable B volume 0 R)
    (hq : AntitoneOn (fun t => A t / B t) (Ioc 0 R)) :
    (∫ t in (0)..r, B t) * (∫ t in r..R, A t)
      ≤ (∫ t in (0)..r, A t) * (∫ t in r..R, B t) := by
  -- `A s = (A s / B s) * B s` since `B s ≠ 0`.
  have hAeq : ∀ s ∈ Ioc 0 R, A s = (A s / B s) * B s := by
    intro s hs; field_simp [(hB s hs).ne']
  -- Integrability on the two sub-intervals.
  have h0R : (0 : ℝ) ≤ R := hr.le.trans hrR
  have hAi0r : IntervalIntegrable A volume 0 r := hAi.mono_set (by
    rw [Set.uIcc_of_le hr.le, Set.uIcc_of_le h0R]; exact Set.Icc_subset_Icc le_rfl hrR)
  have hAirR : IntervalIntegrable A volume r R := hAi.mono_set (by
    rw [Set.uIcc_of_le hrR, Set.uIcc_of_le h0R]; exact Set.Icc_subset_Icc hr.le le_rfl)
  have hBi0r : IntervalIntegrable B volume 0 r := hBi.mono_set (by
    rw [Set.uIcc_of_le hr.le, Set.uIcc_of_le h0R]; exact Set.Icc_subset_Icc le_rfl hrR)
  have hBirR : IntervalIntegrable B volume r R := hBi.mono_set (by
    rw [Set.uIcc_of_le hrR, Set.uIcc_of_le h0R]; exact Set.Icc_subset_Icc hr.le le_rfl)
  have hrIoc : r ∈ Ioc 0 R := ⟨hr, hrR⟩
  -- Tail: `∫ᵣᴿ A ≤ q(r) · ∫ᵣᴿ B`  (on `(r,R)`, `q ≤ q r` and `B ≥ 0`).
  have htail : (∫ t in r..R, A t) ≤ (A r / B r) * (∫ t in r..R, B t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hrR hAirR (hBirR.const_mul _)
    intro s hs
    have hsIoc : s ∈ Ioc 0 R := ⟨hr.trans hs.1, hs.2.le⟩
    rw [hAeq s hsIoc]
    exact mul_le_mul_of_nonneg_right (hq hrIoc hsIoc hs.1.le) (hB s hsIoc).le
  -- Head: `q(r) · ∫₀ʳ B ≤ ∫₀ʳ A`  (on `(0,r)`, `q ≥ q r` and `B ≥ 0`).
  have hhead : (A r / B r) * (∫ t in (0)..r, B t) ≤ (∫ t in (0)..r, A t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr.le (hBi0r.const_mul _) hAi0r
    intro s hs
    have hsIoc : s ∈ Ioc 0 R := ⟨hs.1, hs.2.le.trans hrR⟩
    rw [hAeq s hsIoc]
    exact mul_le_mul_of_nonneg_right (hq hsIoc hrIoc hs.2.le) (hB s hsIoc).le
  -- Tail/head masses of `B` are `≥ 0`.
  have hBtail_nonneg : 0 ≤ ∫ t in r..R, B t := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hrR
      (intervalIntegrable_const (c := (0 : ℝ))) hBirR
      (fun s hs => (hB s ⟨hr.trans hs.1, hs.2.le⟩).le)
    simpa using h
  have hBhead_nonneg : 0 ≤ ∫ t in (0)..r, B t := by
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hr.le
      (intervalIntegrable_const (c := (0 : ℝ))) hBi0r
      (fun s hs => (hB s ⟨hs.1, hs.2.le.trans hrR⟩).le)
    simpa using h
  calc (∫ t in (0)..r, B t) * (∫ t in r..R, A t)
      ≤ (∫ t in (0)..r, B t) * ((A r / B r) * (∫ t in r..R, B t)) :=
        mul_le_mul_of_nonneg_left htail hBhead_nonneg
    _ = ((A r / B r) * (∫ t in (0)..r, B t)) * (∫ t in r..R, B t) := by ring
    _ ≤ (∫ t in (0)..r, A t) * (∫ t in r..R, B t) :=
        mul_le_mul_of_nonneg_right hhead hBtail_nonneg

/-- **Math.** **Volume-ratio monotonicity engine.** If the pointwise density ratio
`A/B` is non-increasing and `B > 0` on `Ioc 0 R`, then the integrated ratio
`(∫₀ᴿ A)/(∫₀ᴿ B)` is non-increasing: `r ≤ R ⟹ (∫₀ᴿA)/(∫₀ᴿB) ≤ (∫₀ʳA)/(∫₀ʳB)`.
This is the final, purely analytic step of Bishop–Gromov: with
`A` = geodesic-sphere area and `B = s_K^{n-1}` the model area, it turns the
pointwise Laplacian/area comparison into the volume-ratio comparison. -/
theorem ratio_intervalIntegral_le
    (hr : 0 < r) (hrR : r ≤ R)
    (hB : ∀ s ∈ Ioc 0 R, 0 < B s)
    (hAi : IntervalIntegrable A volume 0 R)
    (hBi : IntervalIntegrable B volume 0 R)
    (hq : AntitoneOn (fun t => A t / B t) (Ioc 0 R)) :
    (∫ t in (0)..R, A t) / (∫ t in (0)..R, B t)
      ≤ (∫ t in (0)..r, A t) / (∫ t in (0)..r, B t) := by
  have h0R : (0 : ℝ) < R := hr.trans_le hrR
  have hAi0r : IntervalIntegrable A volume 0 r := hAi.mono_set (by
    rw [Set.uIcc_of_le hr.le, Set.uIcc_of_le h0R.le]; exact Set.Icc_subset_Icc le_rfl hrR)
  have hAirR : IntervalIntegrable A volume r R := hAi.mono_set (by
    rw [Set.uIcc_of_le hrR, Set.uIcc_of_le h0R.le]; exact Set.Icc_subset_Icc hr.le le_rfl)
  have hBi0r : IntervalIntegrable B volume 0 r := hBi.mono_set (by
    rw [Set.uIcc_of_le hr.le, Set.uIcc_of_le h0R.le]; exact Set.Icc_subset_Icc le_rfl hrR)
  have hBirR : IntervalIntegrable B volume r R := hBi.mono_set (by
    rw [Set.uIcc_of_le hrR, Set.uIcc_of_le h0R.le]; exact Set.Icc_subset_Icc hr.le le_rfl)
  -- The two `B`-masses are strictly positive.
  have hGr : 0 < ∫ t in (0)..r, B t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hBi0r
      (fun x hx => hB x ⟨hx.1, hx.2.le.trans hrR⟩) hr
  have hGR : 0 < ∫ t in (0)..R, B t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hBi
      (fun x hx => hB x ⟨hx.1, hx.2.le⟩) h0R
  rw [div_le_div_iff₀ hGR hGr]
  -- Split `∫₀ᴿ = ∫₀ʳ + ∫ᵣᴿ` and reduce to the pivoted inequality.
  have hFR : (∫ t in (0)..R, A t) = (∫ t in (0)..r, A t) + (∫ t in r..R, A t) :=
    (intervalIntegral.integral_add_adjacent_intervals hAi0r hAirR).symm
  have hGRsplit : (∫ t in (0)..R, B t) = (∫ t in (0)..r, B t) + (∫ t in r..R, B t) :=
    (intervalIntegral.integral_add_adjacent_intervals hBi0r hBirR).symm
  rw [hFR, hGRsplit]
  nlinarith [head_mass_mul_tail_le hr hrR hB hAi hBi hq]

end OpenGA.Comparison.BishopGromov
