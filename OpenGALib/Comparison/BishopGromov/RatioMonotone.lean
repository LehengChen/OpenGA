import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Ratio monotonicity from a log-derivative comparison

The closing step of the Bishop–Gromov Jacobi route (CH21 L228–229):

> `ln(j/j̄)' = ln(j)' - ln(j̄)' = (a - ā)(n-1) ≤ 0 ⟹ j/j̄ is non-increasing`.

This file isolates that step as pure one-variable calculus: if two positive
differentiable functions satisfy the cross-multiplied log-derivative inequality
`j' · j̄ ≤ j · j̄'` on a convex set, then their ratio `j/j̄` is non-increasing
there. In the Jacobi route `j' / j = (n-1) a` (Liouville, `j = det A`) and
`j̄' / j̄ = (n-1) ā = (n-1) ct_κ`, so the hypothesis is exactly the Riccati
comparison `a ≤ ā` (`riccati_le_model`).

## Main results

* `antitoneOn_ratio_of_logDeriv_le` — `j'·j̄ ≤ j·j̄'` (and `j̄ > 0`) on a convex set
  ⟹ `t ↦ j t / j̄ t` is `AntitoneOn` there.
-/

namespace OpenGA.Comparison.BishopGromov

/-- **Math.** **Ratio is non-increasing from a log-derivative comparison.** For
real functions `j, jbar` differentiable on a convex set `s`, with `jbar > 0` on `s`
and the cross-multiplied log-derivative inequality `j' · jbar ≤ j · jbar'` on `s`,
the ratio `t ↦ j t / jbar t` is `AntitoneOn s`.

The quotient rule gives `(j/jbar)' = (j'·jbar - j·jbar') / jbar²`; the numerator is
`≤ 0` by hypothesis and the denominator is `≥ 0`, so the derivative is `≤ 0` on the
interior, whence `antitoneOn_of_deriv_nonpos`. This is the CH21 L228–229 step
`ln(j/j̄)' = (a - ā)(n-1) ≤ 0 ⟹ j/j̄ non-increasing`. -/
theorem antitoneOn_ratio_of_logDeriv_le {j jbar : ℝ → ℝ} {s : Set ℝ}
    (hs : Convex ℝ s)
    (hj : ∀ t ∈ s, DifferentiableAt ℝ j t)
    (hjbar : ∀ t ∈ s, DifferentiableAt ℝ jbar t)
    (hjbarpos : ∀ t ∈ s, 0 < jbar t)
    (hlog : ∀ t ∈ s, deriv j t * jbar t ≤ j t * deriv jbar t) :
    AntitoneOn (fun t => j t / jbar t) s := by
  have hcont : ContinuousOn (fun t => j t / jbar t) s := fun t ht =>
    ((hj t ht).continuousAt.div (hjbar t ht).continuousAt
      (ne_of_gt (hjbarpos t ht))).continuousWithinAt
  refine antitoneOn_of_deriv_nonpos hs hcont
    (fun t ht => ((hj t (interior_subset ht)).div (hjbar t (interior_subset ht))
      (ne_of_gt (hjbarpos t (interior_subset ht)))).differentiableWithinAt) ?_
  intro t ht
  have ht' : t ∈ s := interior_subset ht
  show deriv (j / jbar) t ≤ 0
  rw [(((hj t ht').hasDerivAt).div ((hjbar t ht').hasDerivAt)
    (ne_of_gt (hjbarpos t ht'))).deriv]
  apply div_nonpos_of_nonpos_of_nonneg
  · have := hlog t ht'; linarith
  · positivity

end OpenGA.Comparison.BishopGromov
