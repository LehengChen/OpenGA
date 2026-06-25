import OpenGALib.Riemannian.Exponential.Defs

/-!
# Hopf–Rinow theorem (statement)

Faithful to the lecture notes (arXiv-2404.09792v2, CH2 §"metric completeness"):

> **Theorem (Hopf–Rinow).** A connected Riemannian manifold is metrically complete
> iff it is geodesically complete (every maximal geodesic is defined for all `t ∈ ℝ`).

with its three corollaries. This file states the theorem and corollaries; proofs are
left as `sorry` (the classical proof — do Carmo Ch. 7 — is the upstream work this
file scopes). It is the Riemannian-side existence theorem that the metric-side
`GeodesicSpace` interface (`MetricGeometry/GeodesicSpace.lean`) and the Bishop–Gromov
volume side (`exp_p` total + minimizing-geodesic existence) consume.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Riemannian.Exponential

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** `(M, g)` is **geodesically complete**: every maximal geodesic is
defined for all `t ∈ ℝ` (its maximal interval is all of `ℝ`). -/
def IsGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p), maximalGeodesicInterval g p v = Set.univ

/-- **Math.** **Hopf–Rinow theorem** (CH2). A connected Riemannian manifold is
metrically complete iff it is geodesically complete. -/
theorem hopfRinow (g : RiemannianMetric I M) [ConnectedSpace M] :
    CompleteSpace M ↔ IsGeodesicallyComplete g := by
  -- do Carmo, *Riemannian Geometry*, Ch. 7, Thm 2.8. NO Morse / second variation.
  -- (⟸) geodesically complete ⟹ complete: `exp_p` total ⟹ (minimizing lemma
  --     `exists_minimizing_geodesic`) every `q` is reached by a minimizing geodesic ⟹
  --     closed bounded sets are compact (Heine–Borel) ⟹ Cauchy sequences converge.
  -- (⟹) complete ⟹ geodesically complete: a maximal geodesic on `[0,b)`, `b < ∞`, is
  --     Cauchy as `s → b⁻` (unit speed ⟹ `dist (γ s) (γ s') ≤ |s-s'|`); completeness
  --     gives `γ b`; local existence/`Existence` + `MaximalInterval` extends past `b`,
  --     contradicting maximality ⟹ `b = ∞` (and symmetrically `-∞`).
  sorry

/-- **Math.** Corollary (CH2). If `exp_p` is defined on all of `T_pM` at one point
`p` (i.e. geodesically complete at `p`), then `M` is metrically complete. -/
theorem complete_of_geodesicallyComplete_at (g : RiemannianMetric I M) [ConnectedSpace M]
    (p : M) (hp : ∀ v : TangentSpace I p, maximalGeodesicInterval g p v = Set.univ) :
    CompleteSpace M := by
  -- do Carmo Ch. 7: `exp_p` total at one `p` ⟹ (minimizing lemma) closed balls
  -- `closedBall p ρ = exp_p '' { v | g.metricInner p v v ≤ ρ²}` are compact ⟹ Heine–Borel
  -- ⟹ Cauchy sequences (bounded ⟹ in some closed ball) converge ⟹ `CompleteSpace M`.
  sorry

/-- **Math.** Corollary (CH2). In a complete connected Riemannian manifold any two
points are joined by a **minimizing geodesic segment**: `y = exp_x v` with the
initial velocity of length `dist x y` (so the geodesic `t ↦ exp_x(t v)`, `t ∈ [0,1]`,
realizes the distance). This feeds the `GeodesicSpace` interface. -/
theorem exists_minimizing_geodesic (g : RiemannianMetric I M) [ConnectedSpace M]
    [CompleteSpace M] (x y : M) :
    ∃ v : TangentSpace I x, expMap g x v = y ∧ g.metricInner x v v = dist x y ^ 2 := by
  -- do Carmo Ch. 7, the minimizing-geodesic lemma (heart of Hopf–Rinow). The whole
  -- argument is geodesic-sphere + connectedness — NO index form / second variation.
  -- Let `r := dist x y`. If `y = x` take `v = 0`. Otherwise:
  -- 1. Pick `δ ∈ (0, r]` with `B_δ(x)` a normal ball (`exp_x` a local diffeo at `0`).
  --    The geodesic sphere `S_δ := exp_x '' { w | g.metricInner x w w = δ²}` is compact
  --    (continuous image of the compact `δ`-sphere of `T_xM`).
  -- 2. `z ↦ dist z y` is continuous on `S_δ` ⟹ attains a minimum at `x₀ = exp_x(δ•v₀)`,
  --    with `g.metricInner x v₀ v₀ = 1`.
  -- 3. Let `γ s := exp_x (s • v₀)`. Set `A := { s ∈ [δ, r] | dist (γ s) y = r - s }`.
  --    • `δ ∈ A`:  `dist x₀ y = r - δ` from `dist x y ≤ δ + min_{S_δ} dist(·,y)` (triangle
  --      inequality through the sphere) and the reverse.
  --    • `A` closed: `s ↦ dist (γ s) y - (r - s)` continuous.
  --    • self-continuing: if `s₀ ∈ A`, `s₀ < r`, redo 1-2 around `γ s₀`; its closest
  --      sphere point lies on `γ`, giving `s₀ + δ' ∈ A`.
  --    ⟹ `A = [δ, r]` ⟹ `r ∈ A` ⟹ `dist (γ r) y = 0` ⟹ `exp_x (r • v₀) = y`.
  -- 4. `v := r • v₀`:  `g.metricInner x v v = r² = (dist x y)²`,  `exp_x v = y`.  ∎
  sorry

/-- **Math.** Corollary (CH2). If `M` is complete, every maximal geodesic is defined
on all of `ℝ`. (Forward direction of `hopfRinow`.) -/
theorem isGeodesicallyComplete_of_complete (g : RiemannianMetric I M) [ConnectedSpace M]
    [CompleteSpace M] : IsGeodesicallyComplete g :=
  (hopfRinow g).mp ‹CompleteSpace M›

end Riemannian.Geodesic
