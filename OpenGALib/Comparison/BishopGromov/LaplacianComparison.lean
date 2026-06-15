import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Volume.ChartPullback
import OpenGALib.Riemannian.Operators.Laplacian
import OpenGALib.Riemannian.Exponential.NormalBallSmooth

/-!
# Laplacian comparison

Layer 3a of the Bishop–Gromov chain. Under a Ricci lower bound
`Ric_g ≥ (n - 1) K g`, the Laplacian of the distance function `r = d(p, ·)`
is bounded above by the model space-form value `(n-1) · s_K'(r) / s_K(r)`,
wherever `r` is smooth (away from `p` and the cut locus — abstracted here as
the differentiability hypothesis on the distance function).

This is the analytic bridge from the Ricci bound to the volume-element growth
that drives `bishopGromov_volume_comparison`; it is itself the integrated form
of the Riccati comparison (`RiccatiComparison`).

Ground truth: do Carmo Ch.10 §1 Thm 1.4; Petersen Ch.9 Lemma 27.2.
-/

open scoped Real Manifold InnerProductSpace ContDiff Riemannian
open Bundle Riemannian Riemannian.Operators Set OpenGA.Comparison.BishopGromov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [HasMetric I M] [CompleteSpace M] [IsRiemannianManifold I M]

local notation:max "n_M" => Module.finrank ℝ E

/-- **Math.** Laplacian comparison theorem.

Let `(M, g)` satisfy `Ric_g ≥ (n - 1) K g`, let `p : M`, and write
`r := fun x => dist p x` for the distance to `p`. At a point `x` where `r` is
smooth (encoded by `hx`), the Laplacian of `r` is bounded by the model
space-form mean curvature:
`Δ_g r (x) ≤ (n - 1) · s_K'(r(x)) / s_K(r(x))`,
where `s_K = snakeFunction K` is the space-form Jacobi function. -/
theorem laplacian_comparison
    (g : RiemannianMetric I M) {K : ℝ}
    (hRic : ∀ x : M, ∀ v : TangentSpace I x,
      ((n_M : ℝ) - 1) * K * g.metricInner x v v ≤ (ricciTensor g x v) v)
    (p : M) (x : M)
    (hx : MDifferentiableAt I 𝓘(ℝ) (fun y => dist p y) x) (hxp : x ≠ p) :
    scalarLaplacian g (fun y => dist p y) x
      ≤ ((n_M : ℝ) - 1) * deriv (snakeFunction K) (dist p x) / snakeFunction K (dist p x) := by
  sorry
