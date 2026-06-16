import OpenGALib.Comparison.BishopGromov.RatioMonotone
import OpenGALib.Comparison.BishopGromov.RiccatiComparison

/-!
# Bishop–Gromov Jacobi route: the volume-density ratio is non-increasing (level-1 assembly)

This chains the scalar outputs of the Jacobi-route bricks into the per-direction
area-density monotonicity of CH21:

* the **shape-operator trace** `m = tr S` satisfies the Riccati sub-equation
  `m' + m²/(n-1) + (n-1)K ≤ 0` (the spine `meanCurvatureRiccati_of_jacobiMatrixODE`
  + RB5) and the singular asymptotics `m ~ (n-1)/r` (`S ~ I/t`);
* the **Jacobi density** `j = det A` satisfies `j'/j = m` (Liouville
  `hasDerivAt_det`) and `j > 0` before the first conjugate point.

From these the Riccati comparison `m ≤ m_K` (`riccati_le_model`) and the model
identity `j̄ = s_K^{n-1}`, `j̄'/j̄ = m_K`, feed the log-derivative monotonicity
`antitoneOn_ratio_of_logDeriv_le` to give `j / s_K^{n-1}` non-increasing — exactly
the per-direction reading of `BishopGromovVolumeData.ratio_antitone`.

These scalar inputs are produced by the (0-sorry) Jacobi bricks together with the
cited geometric facts (parallel frame, Jacobi-field existence, conjugate points,
`S~I/t`) tracked as level-2 work in issue #86; this file is the **level-1**
assembly — the notes' actual argument — with those facts as the interface.

## Main results

* `ratio_antitone_of_riccati_subsolution` — from the `m`-Riccati sub-solution
  (+asymptotics) and `j'/j = m` (+positivity), `j / s_K^{n-1}` is `AntitoneOn` the
  admissible window.
-/

open Set Filter

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** **Volume-density ratio monotonicity (level-1 assembly).** Let `m` be
a mean-curvature trace satisfying, on the admissible window, the Riccati
sub-equation `m' + m²/(n-1) + (n-1)K ≤ 0` and the singular asymptotics
`m - (n-1)/r → 0` as `r → 0⁺`; and let `j > 0` satisfy `j' = m · j` (i.e.
`j'/j = m`). Then the density ratio `j / s_K^{n-1}` is non-increasing on the window.

The Riccati comparison `riccati_le_model` gives `m ≤ m_K`; the model density
`j̄ = s_K^{n-1}` has `j̄' = m_K · j̄`; so `j' · j̄ = m·j·j̄ ≤ m_K·j·j̄ = j · j̄'`, and
`antitoneOn_ratio_of_logDeriv_le` concludes. This is the CH21 L216–233 conclusion
`j/j̄ non-increasing`, assembled from the Jacobi-route scalar bricks. -/
theorem ratio_antitone_of_riccati_subsolution
    (n : ℕ) (hn : 2 ≤ n) (K : ℝ) (m j : ℝ → ℝ)
    (hm_diff : ∀ r ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ m r)
    (hm_sub : ∀ r ∈ spaceFormAdmissibleRadii K,
      deriv m r + m r ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * K ≤ 0)
    (hm_asymp : Tendsto (fun r => m r - ((n : ℝ) - 1) / r) (nhdsWithin 0 (Ioi 0)) (nhds 0))
    (hj_diff : ∀ r ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ j r)
    (hj_pos : ∀ r ∈ spaceFormAdmissibleRadii K, 0 < j r)
    (hj_log : ∀ r ∈ spaceFormAdmissibleRadii K, deriv j r = m r * j r) :
    AntitoneOn (fun t => j t / snakeFunction K t ^ (n - 1)) (spaceFormAdmissibleRadii K) := by
  set jbar : ℝ → ℝ := fun r => snakeFunction K r ^ (n - 1) with hjbardef
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  -- The model density `j̄ = s_K^{n-1}` solves `j̄' = m_K · j̄`.
  have hbar_hasD : ∀ r ∈ spaceFormAdmissibleRadii K,
      HasDerivAt jbar (modelMeanCurvature n K r * jbar r) r := by
    intro r hr
    have hsK := hasDerivAt_snakeFunction K r
    have hsK_ne : snakeFunction K r ≠ 0 := ne_of_gt (snakeFunction_pos hr)
    have hpow : snakeFunction K r ^ (n - 1)
        = snakeFunction K r ^ (n - 1 - 1) * snakeFunction K r := by
      rw [← pow_succ]; congr 1; omega
    have hval : modelMeanCurvature n K r * jbar r
        = ((n - 1 : ℕ) : ℝ) * snakeFunction K r ^ (n - 1 - 1) * snakeDeriv K r := by
      simp only [hjbardef, modelMeanCurvature, hsK.deriv]
      rw [hcast, hpow]; field_simp
    rw [hval]
    exact hsK.pow (n - 1)
  have hbar_pos : ∀ r ∈ spaceFormAdmissibleRadii K, 0 < jbar r :=
    fun r hr => pow_pos (snakeFunction_pos hr) _
  have hbar_diff : ∀ r ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ jbar r :=
    fun r hr => (hbar_hasD r hr).differentiableAt
  -- Riccati comparison: `m ≤ m_K`.
  have hmle : ∀ r ∈ spaceFormAdmissibleRadii K, m r ≤ modelMeanCurvature n K r :=
    fun r hr => riccati_le_model n hn K m hm_diff hm_sub hm_asymp hr
  -- Log-derivative comparison ⟹ ratio non-increasing.
  refine antitoneOn_ratio_of_logDeriv_le (convex_spaceFormAdmissibleRadii K)
    hj_diff hbar_diff hbar_pos ?_
  intro r hr
  rw [hj_log r hr, (hbar_hasD r hr).deriv]
  have hjr := (hj_pos r hr).le
  have hbr := (hbar_pos r hr).le
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (hmle r hr)) hjr) hbr]

end OpenGA.Comparison.BishopGromov
