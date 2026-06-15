import Mathlib.Geometry.Manifold.Riemannian.Basic
import OpenGALib.Comparison.Util.SpaceForm
import OpenGALib.Comparison.BishopGromov.PolarVolumeReduction
import OpenGALib.Riemannian.Curvature.RicciTensorBundle
import OpenGALib.Riemannian.Volume.ChartPullback
import OpenGALib.Riemannian.Volume.ChartPullbackFormula
import OpenGALib.Riemannian.Volume.ExpBridge

/-!
# Bishop–Gromov volume comparison

North-star theorem of Layer 3b. Statement only; proof is the multi-stage
goal driving Layer 1 + Layer 3a + Layer 3b. Ground truth: do Carmo
Ch. 10 §2 Thm 2.2; Petersen Ch. 9 Thm 27; Cheeger–Ebin Thm 1.93;
Burago–Burago–Ivanov §6.5.
-/

open scoped Real Manifold InnerProductSpace ENNReal ContDiff Riemannian
open Bundle MeasureTheory Riemannian Set OpenGA.Comparison.BishopGromov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsLocallyConstantChartedSpace H M]
  [HasMetric I M] [CompleteSpace M] [IsRiemannianManifold I M]
  [MeasurableSpace M] [BorelSpace M] [SigmaCompactSpace M]

local notation:max "n_M" => Module.finrank ℝ E

scoped[OpenGA.Comparison.BishopGromov]
  notation:max "B(" p ", " r ")" => Metric.ball p r

section
variable {K : ℝ}

local notation:max "V_K^" n:max "(" r:max ")" => spaceFormBallVolume n K r
local notation:max "𝒟_K" => spaceFormAdmissibleRadii K

/-- **Math.** **Geodesic-polar volume interface** toward Bishop–Gromov. This is
the *volume-side* geometric interface of `docs/EXP_GEODESIC_MIGRATION.md` (the
hybrid route, "Note on alternatives"): the geodesic-polar volume structure that
the exponential-map layer discharges (via the exp-volume bridge `ExpBridge`, the
polar Jacobian `det d exp_p(tξ) = t^{n-1} J`, and `∂_t log J = Δ_g r ≤ m_K` from
the Laplacian comparison), packaged so Bishop–Gromov is proved 0-sorry *modulo*
it.

It bundles the geodesic-sphere **area profile** `A(t)` with the two facts the
proved volume-ratio engine (`ratio_spaceFormBallVolume_le`) consumes:
* `vol_eq` — the geodesic-polar volume formula `vol_g B(p,R) = ∫₀ᴿ A(t) dt`;
* `area_integrable` — integrability of `A` on each window radius;
* `ratio_antitone` — the area-density ratio `A(t) / s_K(t)^{n-1}` is non-increasing,
  the volume reading of the Laplacian comparison `Δ_g r ≤ m_K` (which forces
  `∂_t log A ≤ ∂_t log A_K`). The Ricci lower bound `Ric_g ≥ (n-1)K g` enters
  through the discharge of `ratio_antitone`. -/
structure BishopGromovVolumeData (g : RiemannianMetric I M) (K : ℝ) (p : M) where
  /-- The geodesic-sphere area profile `A(t)`. -/
  area : ℝ → ℝ
  /-- The geodesic-polar volume formula `vol_g B(p,R) = ∫₀ᴿ A`. -/
  vol_eq : ∀ R ∈ spaceFormAdmissibleRadii K,
    (Riemannian.volumeMeasure g).real (Metric.ball p R) = ∫ t in (0 : ℝ)..R, area t
  /-- Integrability of the area profile on each admissible window radius. -/
  area_integrable : ∀ R ∈ spaceFormAdmissibleRadii K,
    IntervalIntegrable area MeasureTheory.volume 0 R
  /-- The area-density ratio is non-increasing — the volume reading of
  `Δ_g r ≤ m_K`. -/
  ratio_antitone : ∀ R ∈ spaceFormAdmissibleRadii K,
    AntitoneOn (fun t => area t / max 0 (snakeFunction K t) ^ (n_M - 1)) (Set.Ioc 0 R)

omit [InnerProductSpace ℝ E] [CompleteSpace E] [NeZero n_M] [I.Boundaryless]
  [IsLocallyConstantChartedSpace H M] [HasMetric I M] [CompleteSpace M]
  [IsRiemannianManifold I M] [BorelSpace M] in
/-- **Math.** Bishop–Gromov volume comparison.

For a Riemannian manifold `(M, g)` with `Ric_g ≥ (n - 1) K g`, the ratio
`(volumeMeasure g)(B(p, R)) / V_K^n(R)` of the Riemannian-volume ball
to the model space-form ball is monotone non-increasing in `R` on the
admissible radius window `𝒟_K`.

Proved **0-sorry modulo** the `BishopGromovVolumeData` interface (the hybrid route
of `docs/EXP_GEODESIC_MIGRATION.md`): given the geodesic-polar volume formula and
the area-density monotonicity, the conclusion is exactly the proved analytic
volume-ratio engine `ratio_spaceFormBallVolume_le`. The interface is discharged by
the exponential-map / volume-Jacobian layer (the exp-volume bridge + polar
Jacobian + Laplacian comparison) once that geometry is built; the Ricci lower
bound enters through `data.ratio_antitone`.

Stated directly on the canonical Riemannian volume `Riemannian.volumeMeasure g`;
the generic-measure stopgap (`IsScalarMultipleOfHausdorff`) is retired
now that `volumeMeasure` is constructed in `Riemannian/Volume/`. -/
theorem bishopGromov_volume_comparison
    (g : RiemannianMetric I M) (p : M) (data : BishopGromovVolumeData g K p)
    {r R : ℝ} (hr : r ∈ 𝒟_K) (hR : R ∈ 𝒟_K) (hrR : r ≤ R) :
    (Riemannian.volumeMeasure g).real B(p, R) / V_K^n_M(R)
      ≤ (Riemannian.volumeMeasure g).real B(p, r) / V_K^n_M(r) := by
  rw [data.vol_eq R hR, data.vol_eq r hr]
  exact ratio_spaceFormBallVolume_le hr hR hrR (data.area_integrable R hR)
    (data.ratio_antitone R hR)

end
