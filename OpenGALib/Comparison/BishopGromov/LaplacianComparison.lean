import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Comparison.BishopGromov.RiccatiComparison
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

/-- **Math.** **Radial Laplacian-profile interface** for the distance function
`r = dist p ·` toward the Laplacian comparison. This is the *geometric interface*
(the hybrid geometric-interface route):
the smooth-distance / radial structure that the exponential-map layer
(Gauss lemma + eikonal + radial-derivative identification + base-point asymptotic)
discharges, packaged so the Laplacian comparison is proved 0-sorry *modulo* it.

It bundles the radial Laplacian profile `m(s) = Δ_g r` along the unit geodesic at
radius `s`, together with the three facts the proved Riccati ODE core
(`riccati_le_model`) consumes:
* `eval` — the profile reproduces `Δ_g r` at the radius `dist p x`;
* `radius_mem` — that radius lies in the admissible window;
* `differentiableAt` — the profile is differentiable on the window;
* `riccati_sub` — the Riccati sub-equation `m' + m²/(n-1) + (n-1)K ≤ 0`
  (discharged later by `bochner_radial_riccati` from the eikonal equation and the
  Ricci lower bound);
* `asymptotic` — the base-point singular asymptotic `m(s) - (n-1)/s → 0`. -/
structure RadialLaplacianProfile (g : RiemannianMetric I M) (K : ℝ) (p x : M) where
  /-- The radial Laplacian profile `m(s) = Δ_g r` at radius `s`. -/
  profile : ℝ → ℝ
  /-- The profile reproduces the Laplacian of the distance at radius `dist p x`. -/
  eval : profile (dist p x) = scalarLaplacian g (fun y => dist p y) x
  /-- The radius `dist p x` lies in the admissible window. -/
  radius_mem : dist p x ∈ spaceFormAdmissibleRadii K
  /-- The profile is differentiable on the admissible window. -/
  differentiableAt : ∀ r ∈ spaceFormAdmissibleRadii K, DifferentiableAt ℝ profile r
  /-- The Riccati sub-equation (the geometric content discharged by
  `bochner_radial_riccati` from eikonal `|∇r|² = 1` and `Ric ≥ (n-1)K g`). -/
  riccati_sub : ∀ r ∈ spaceFormAdmissibleRadii K,
    deriv profile r + profile r ^ 2 / ((n_M : ℝ) - 1) + ((n_M : ℝ) - 1) * K ≤ 0
  /-- The base-point singular asymptotic `m(s) - (n-1)/s → 0` as `s → 0⁺`. -/
  asymptotic : Filter.Tendsto (fun r => profile r - ((n_M : ℝ) - 1) / r)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

omit [CompleteSpace M] [IsRiemannianManifold I M] in
/-- **Math.** Laplacian comparison theorem.

Let `(M, g)` satisfy `Ric_g ≥ (n - 1) K g`, let `p : M`, and write
`r := fun x => dist p x` for the distance to `p`. The Laplacian of `r` is bounded
by the model space-form mean curvature:
`Δ_g r (x) ≤ (n - 1) · s_K'(r(x)) / s_K(r(x))`,
where `s_K = snakeFunction K` is the space-form Jacobi function.

Proved **0-sorry modulo** the `RadialLaplacianProfile` interface (the hybrid
geometric-interface route): given the radial profile and its Riccati /
asymptotic data, the conclusion is exactly the proved ODE comparison
`riccati_le_model`. The interface itself is discharged by the exponential-map
layer (eikonal + radial-derivative identification, via `bochner_radial_riccati`)
once that geometry is built. The Ricci lower bound `Ric_g ≥ (n-1)K g` enters
through the discharge of `data.riccati_sub`, so it is not a hypothesis of this
modulo-interface form. -/
theorem laplacian_comparison
    (g : RiemannianMetric I M) {K : ℝ} (hn : 2 ≤ n_M)
    (p : M) (x : M) (data : RadialLaplacianProfile g K p x) :
    scalarLaplacian g (fun y => dist p y) x
      ≤ ((n_M : ℝ) - 1) * deriv (snakeFunction K) (dist p x) / snakeFunction K (dist p x) := by
  rw [← data.eval]
  exact riccati_le_model n_M hn K data.profile data.differentiableAt data.riccati_sub
    data.asymptotic data.radius_mem
