import OpenGALib.Riemannian.Connection.ParallelTransport
import OpenGALib.Riemannian.Curvature.JacobiField

/-!
# Parallel frame: the covariant derivative is the component derivative

The Bishop–Gromov Jacobi route (CH21) writes Jacobi fields in a **parallel
orthonormal frame** `v₁(t), …, vₙ(t)` along the geodesic (CH21 L121) so that the
covariant derivative `D_t` becomes the ordinary componentwise time-derivative — the
device that turns the Jacobi equation into the matrix ODE `A'' + R̃ A = 0` and lets
`∂_t det A = Σᵢ det(… Jᵢ' …)` (CH21 L150–154).

This file records the analytic atom behind that device: for a field `E` that is
**parallel** at `t₀` (`D_t E = 0`), the time-derivative of the inner product
`⟨W, E⟩_g` is the inner product of the covariant derivative with `E`:
`d/dt ⟨W, E⟩_g = ⟨D_t W, E⟩_g`. It is the metric-compatibility identity
`covDerivAlongCurve_metricInner` (item ①) with the `D_t E` term killed by
parallelism. Stated in `HasDerivAt` form so it can be **iterated** (apply once to
`W = J` and once to `W = D_t J`) to read off the second covariant derivative of a
Jacobi field as the second component derivative.

The parallel orthonormal frame whose existence underlies this route is the
deliverable of issue #86 (parallel-transport existence); here `E` parallel is taken
as a hypothesis, faithful to CH21's use of the frame.

## Main results

* `hasDerivAt_metricInner_parallel_right` — `d/dt ⟨W, E⟩_g = ⟨D_t W, E⟩_g` (in
  `HasDerivAt` form) when `E` is parallel at `t₀`.
-/

open Bundle
open scoped Manifold ContDiff Topology
open Riemannian.Tensor

namespace OpenGA.Comparison.BishopGromov

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ModelWithCorners.Boundaryless I]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Covariant derivative = component derivative against a parallel field.**
For along-curve fields `W` and `E` with `E` parallel at `t₀` (`D_t E (t₀) = 0`), the
inner product `t ↦ ⟨W t, E t⟩_g` has derivative `⟨D_t W (t₀), E t₀⟩_g` at `t₀`.

This is the metric-compatibility identity `covDerivAlongCurve_metricInner`
`d/dt⟨W,E⟩ = ⟨D_tW,E⟩ + ⟨W,D_tE⟩` with the second term annihilated by `D_t E = 0`.
The conclusion is packaged as `HasDerivAt` (using the supplied differentiability of
the scalar inner product) so it can be iterated to extract second covariant
derivatives — the engine of the parallel-frame reduction of the Jacobi equation. -/
theorem hasDerivAt_metricInner_parallel_right
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (W Efield : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hE : covDerivAlongCurve (I := I) g γ Efield t₀ = 0)
    (hWc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (W t)) t₀)
    (hEc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (Efield t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ContinuousAt γ t₀)
    (hdiff : DifferentiableAt ℝ (fun t => g.metricInner (γ t) (W t) (Efield t)) t₀) :
    HasDerivAt (fun t => g.metricInner (γ t) (W t) (Efield t))
      (g.metricInner (γ t₀) (covDerivAlongCurve (I := I) g γ W t₀) (Efield t₀)) t₀ := by
  have hval := covDerivAlongCurve_metricInner g γ W Efield t₀ hWc hEc hγc hγcont
  rw [hE, g.metricInner_zero_right, add_zero] at hval
  exact hval ▸ hdiff.hasDerivAt

section JacobiRow

variable [CompleteSpace E] [IsManifold I 2 M] [T2Space M] [IsLocallyConstantChartedSpace H M]
  [HasMetric I M]

open Riemannian

/-- **Math.** **Self-adjointness of the Jacobi (directional curvature) operator.**
For tangent vectors `u, v, w : T_x M`, the operator `R_v : u ↦ R(u,v)v` is
self-adjoint: `⟨R(u,v)v, w⟩_g = ⟨R(w,v)v, u⟩_g`. This is the algebraic symmetry
behind the Wronskian-constancy of two Jacobi fields (hence the symmetry of the
shape operator `S`). Derived from the curvature symmetries — pair symmetry
`⟨R(u,v)v,w⟩ = ⟨R(v,w)u,v⟩`, the `(3,4)` metric-skew, and `(1,2)`-antisymmetry —
with the tangent vectors packaged as constant smooth fields. -/
theorem riemannCurvature_jacobi_self_adjoint_const
    (g : RiemannianMetric I M) (x : M) (u v w : TangentSpace I x) :
    g.metricInner x (riemannCurvature g (fun _ => u) (fun _ => v) (fun _ => v) x) w
      = g.metricInner x (riemannCurvature g (fun _ => w) (fun _ => v) (fun _ => v) x) u := by
  have hpair := riemannCurvature_pair_symm g
    (SmoothVectorField.const (I := I) (M := M) u) (SmoothVectorField.const (I := I) (M := M) v)
    (SmoothVectorField.const (I := I) (M := M) v) (SmoothVectorField.const (I := I) (M := M) w) x
  have hskew := riemannCurvature_metric_skew g
    (SmoothVectorField.const (I := I) (M := M) v) (SmoothVectorField.const (I := I) (M := M) w)
    (SmoothVectorField.const (I := I) (M := M) u) (SmoothVectorField.const (I := I) (M := M) v) x
  have hanti := riemannCurvature_antisymm g
    (fun _ => v) (fun _ => w) (fun _ => v) x
  have hc : ∀ a : TangentSpace I x,
      (SmoothVectorField.const (I := I) (M := M) a).toFun = fun _ => a := fun _ => rfl
  simp only [hc, SmoothVectorField.const_apply] at hpair hskew
  rw [hpair]
  have h1 : g.metricInner x (riemannCurvature g (fun _ => v) (fun _ => w) (fun _ => u) x) v
      = -(g.metricInner x (riemannCurvature g (fun _ => v) (fun _ => w) (fun _ => v) x) u) := by
    linarith [hskew]
  rw [h1, hanti, g.metricInner_neg_left, neg_neg]

/-- **Math.** **Second component derivative of a Jacobi field against a parallel
field = minus the curvature term.** For a Jacobi field `J` along `γ` and a field `E`
parallel at `t₀`, the first-component derivative `t ↦ ⟨D_t J, E⟩_g` has, at `t₀`,
derivative `-⟨R(J, γ') γ', E⟩_g`. Equivalently the parallel-frame component
`c(t) = ⟨J, E⟩` satisfies `c''(t₀) = -⟨R(J,γ')γ', E⟩` — exactly the row of the
Jacobi matrix ODE `A'' + R̃ A = 0` (CH21 L156–168) read against the frame.

Apply the parallel-frame atom `hasDerivAt_metricInner_parallel_right` to
`W = D_t J`: its derivative is `⟨D_t (D_t J), E⟩ = ⟨D_t² J, E⟩`; the Jacobi equation
`D_t² J = -R(J,γ')γ'` (`hJac`) turns this into `-⟨R(J,γ')γ', E⟩`. -/
theorem hasDerivAt_metricInner_covDeriv_jacobi
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (J Efield : (t : ℝ) → TangentSpace I (γ t)) (t₀ : ℝ)
    (hJac : Riemannian.IsJacobiFieldAlong (I := I) g γ J)
    (hE : covDerivAlongCurve (I := I) g γ Efield t₀ = 0)
    (hDJc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlongCurve (I := I) g γ J t)) t₀)
    (hEc : DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (Efield t)) t₀)
    (hγc : DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ContinuousAt γ t₀)
    (hdiff : DifferentiableAt ℝ (fun t =>
      g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J t) (Efield t)) t₀) :
    HasDerivAt (fun t => g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J t) (Efield t))
      (-(g.metricInner (γ t₀) (Riemannian.jacobiCurvatureTerm (I := I) g γ J t₀) (Efield t₀))) t₀ := by
  have hatom := hasDerivAt_metricInner_parallel_right g γ
    (fun s => covDerivAlongCurve (I := I) g γ J s) Efield t₀ hE hDJc hEc hγc hγcont hdiff
  -- The covariant derivative of `D_t J` is `D_t² J = -R(J,γ')γ'` by the Jacobi equation.
  have h2 : covDerivAlongCurve (I := I) g γ (fun s => covDerivAlongCurve (I := I) g γ J s) t₀
      = -(Riemannian.jacobiCurvatureTerm (I := I) g γ J t₀) := by
    have hj := hJac t₀
    rw [Riemannian.covDerivAlongCurve2_def] at hj
    exact eq_neg_of_add_eq_zero_left hj
  rw [h2, g.metricInner_neg_left] at hatom
  exact hatom

/-- **Math.** **Wronskian symmetry of two Jacobi fields ⟹ the shape operator is
symmetric.** For Jacobi fields `J₁, J₂` along `γ` both vanishing at `0`, the
"Wronskian" `⟨D_t J₁, J₂⟩_g - ⟨J₁, D_t J₂⟩_g` is identically `0`; equivalently
`⟨D_t J₁, J₂⟩_g = ⟨J₁, D_t J₂⟩_g` for all `t`.

Differentiating (metric-compatibility, item ①, applied to `(D_t J₁, J₂)` and to
`(J₁, D_t J₂)`) the two cross terms `⟨D_t J₁, D_t J₂⟩` cancel, leaving
`W' = ⟨D_t² J₁, J₂⟩ - ⟨J₁, D_t² J₂⟩`. The Jacobi equation turns the second
covariant derivatives into curvature terms, and self-adjointness of the Jacobi
operator (`riemannCurvature_jacobi_self_adjoint_const`) makes them cancel, so
`W' ≡ 0`. The initial conditions `J₁ 0 = J₂ 0 = 0` give `W 0 = 0`, hence `W ≡ 0`.
When `D_t Jᵢ = S Jᵢ` this is exactly `⟨S J₁, J₂⟩ = ⟨J₁, S J₂⟩` — the symmetry of
the shape operator consumed by the matrix Riccati trace reduction (RB5). -/
theorem jacobi_metricInner_covDeriv_symm
    (g : RiemannianMetric I M) (γ : ℝ → M)
    (J1 J2 : (t : ℝ) → TangentSpace I (γ t))
    (hJac1 : Riemannian.IsJacobiFieldAlong (I := I) g γ J1)
    (hJac2 : Riemannian.IsJacobiFieldAlong (I := I) g γ J2)
    (hJ1c : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (J1 t)) t₀)
    (hJ2c : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t) (J2 t)) t₀)
    (hDJ1c : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlongCurve (I := I) g γ J1 t)) t₀)
    (hDJ2c : ∀ t₀, DifferentiableAt ℝ (fun t =>
      (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t)
        (covDerivAlongCurve (I := I) g γ J2 t)) t₀)
    (hγc : ∀ t₀, DifferentiableAt ℝ (fun t => extChartAt I (γ t₀) (γ t)) t₀)
    (hγcont : ∀ t₀, ContinuousAt γ t₀)
    (hf : Differentiable ℝ (fun t =>
      g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J1 t) (J2 t)))
    (hg : Differentiable ℝ (fun t =>
      g.metricInner (γ t) (J1 t) (covDerivAlongCurve (I := I) g γ J2 t)))
    (hJ10 : J1 0 = 0) (hJ20 : J2 0 = 0) (t : ℝ) :
    g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J1 t) (J2 t)
      = g.metricInner (γ t) (J1 t) (covDerivAlongCurve (I := I) g γ J2 t) := by
  set F : ℝ → ℝ := fun t => g.metricInner (γ t) (covDerivAlongCurve (I := I) g γ J1 t) (J2 t)
    with hFdef
  set G : ℝ → ℝ := fun t => g.metricInner (γ t) (J1 t) (covDerivAlongCurve (I := I) g γ J2 t)
    with hGdef
  -- The Wronskian `W = F - G` has vanishing derivative everywhere.
  have hdW : ∀ s, deriv (fun r => F r - G r) s = 0 := by
    intro s
    -- `deriv F`, `deriv G` via metric-compatibility (item ①).
    have hFd : deriv F s
        = g.metricInner (γ s)
            (covDerivAlongCurve (I := I) g γ (fun r => covDerivAlongCurve (I := I) g γ J1 r) s) (J2 s)
          + g.metricInner (γ s) (covDerivAlongCurve (I := I) g γ J1 s)
              (covDerivAlongCurve (I := I) g γ J2 s) := by
      rw [hFdef]
      exact covDerivAlongCurve_metricInner g γ (fun r => covDerivAlongCurve (I := I) g γ J1 r) J2 s
        (hDJ1c s) (hJ2c s) (hγc s) (hγcont s)
    have hGd : deriv G s
        = g.metricInner (γ s) (covDerivAlongCurve (I := I) g γ J1 s)
              (covDerivAlongCurve (I := I) g γ J2 s)
          + g.metricInner (γ s) (J1 s)
              (covDerivAlongCurve (I := I) g γ (fun r => covDerivAlongCurve (I := I) g γ J2 r) s) := by
      rw [hGdef]
      exact covDerivAlongCurve_metricInner g γ J1 (fun r => covDerivAlongCurve (I := I) g γ J2 r) s
        (hJ1c s) (hDJ2c s) (hγc s) (hγcont s)
    have hF := hFd ▸ (hf s).hasDerivAt
    have hG := hGd ▸ (hg s).hasDerivAt
    show deriv (F - G) s = 0
    rw [(hF.sub hG).deriv]
    -- Jacobi equation: `D_t² Jᵢ = -R(Jᵢ,γ')γ'`.
    have hJ1eq : covDerivAlongCurve (I := I) g γ (fun r => covDerivAlongCurve (I := I) g γ J1 r) s
        = -(Riemannian.jacobiCurvatureTerm (I := I) g γ J1 s) := by
      have hj := hJac1 s; rw [Riemannian.covDerivAlongCurve2_def] at hj
      exact eq_neg_of_add_eq_zero_left hj
    have hJ2eq : covDerivAlongCurve (I := I) g γ (fun r => covDerivAlongCurve (I := I) g γ J2 r) s
        = -(Riemannian.jacobiCurvatureTerm (I := I) g γ J2 s) := by
      have hj := hJac2 s; rw [Riemannian.covDerivAlongCurve2_def] at hj
      exact eq_neg_of_add_eq_zero_left hj
    rw [hJ1eq, hJ2eq, g.metricInner_neg_left, g.metricInner_neg_right]
    -- self-adjointness + symmetry make the two curvature terms equal.
    have hsa : g.metricInner (γ s) (Riemannian.jacobiCurvatureTerm (I := I) g γ J1 s) (J2 s)
        = g.metricInner (γ s) (J1 s) (Riemannian.jacobiCurvatureTerm (I := I) g γ J2 s) := by
      rw [Riemannian.jacobiCurvatureTerm_def, Riemannian.jacobiCurvatureTerm_def,
        g.metricInner_comm (γ s) (J1 s)]
      exact riemannCurvature_jacobi_self_adjoint_const g (γ s) (J1 s)
        (Riemannian.curveVelocity (I := I) γ s) (J2 s)
    linarith [hsa]
  -- `W` is constant, equal to its value `0` at `0`.
  have hWconst : ∀ s, (F s - G s) = (F 0 - G 0) := fun s =>
    is_const_of_deriv_eq_zero (hf.sub hg) hdW s 0
  have hW0 : F 0 - G 0 = 0 := by
    rw [hFdef, hGdef]
    simp only [hJ10, hJ20, g.metricInner_zero_left, g.metricInner_zero_right, sub_self]
  have hWt : F t - G t = 0 := (hWconst t).trans hW0
  rw [sub_eq_zero] at hWt
  exact hWt

end JacobiRow

end OpenGA.Comparison.BishopGromov
