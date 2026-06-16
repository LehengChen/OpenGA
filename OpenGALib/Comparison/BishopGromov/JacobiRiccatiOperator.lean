import OpenGALib.Comparison.BishopGromov.MatrixRiccati

/-!
# Operator-form matrix Riccati ⟶ scalar Riccati (closing the trace-derivative debt)

`matrixRiccati_trace_scalar_riccati` (`MatrixRiccati.lean`) deliberately takes the
covariant-derivative hypothesis in **traced scalar form** — a `HasDerivAt` for the
scalar `h t = trace (S t)` — to avoid threading an operator-valued `HasDerivAt`
through the (finite-dimensional) operator normed structure. That was the honest
fallback flagged in its design note.

This file discharges that debt. The genuine matrix Riccati is an **operator-valued**
equation `S' + S² + R = 0`. Operator-valued differentiation lives in
`V →L[ℝ] V` (which carries a norm), not `V →ₗ[ℝ] V` (which does not). We:

* push the scalar `trace` through an operator-valued `HasDerivAt` via the
  continuous-linear trace functional (`hasDerivAt_trace_continuousLinearMap`), and
* feed the resulting traced `HasDerivAt` into `matrixRiccati_trace_scalar_riccati`,
  obtaining the scalar Riccati directly from the operator Riccati
  (`operatorRiccati_scalar_riccati`).

The bridge `(T.toLinearMap)`-trace identifies the continuous-linear `V →L[ℝ] V`
operators with the linear `V →ₗ[ℝ] V` operators consumed by the trace machinery
(both are the same map; in finite dimension every linear map is continuous).

*No geometry, no manifolds* — pure operator calculus + the proved trace reduction.
-/

open scoped InnerProductSpace

namespace OpenGA.Comparison.BishopGromov

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Math.** The **trace functional on continuous linear operators**, as an
`ℝ`-linear map `(V →L[ℝ] V) →ₗ[ℝ] ℝ`: `T ↦ trace (T : V →ₗ[ℝ] V)`. It is the
ordinary `LinearMap.trace` precomposed with the linear coercion `V →L[ℝ] V` ↪
`V →ₗ[ℝ] V`. -/
noncomputable def traceCLM : (V →L[ℝ] V) →ₗ[ℝ] ℝ :=
  (LinearMap.trace ℝ V).comp (ContinuousLinearMap.coeLM ℝ)

omit [FiniteDimensional ℝ V] in
@[simp] lemma traceCLM_apply (T : V →L[ℝ] V) :
    traceCLM T = LinearMap.trace ℝ V (T : V →ₗ[ℝ] V) := rfl

/-- **Math.** **Trace pushed through an operator-valued derivative.** If a path of
continuous linear operators `S : ℝ → (V →L[ℝ] V)` has derivative `S'` at `t`, then
its trace `t ↦ trace (S t)` has derivative `trace S'` at `t`. The trace functional
is continuous-linear (finite dimension), so it commutes with `HasDerivAt`. -/
theorem hasDerivAt_trace_continuousLinearMap
    {S : ℝ → (V →L[ℝ] V)} {S' : V →L[ℝ] V} {t : ℝ} (hS : HasDerivAt S S' t) :
    HasDerivAt (fun s => LinearMap.trace ℝ V (S s : V →ₗ[ℝ] V))
      (LinearMap.trace ℝ V (S' : V →ₗ[ℝ] V)) t := by
  have h := (traceCLM (V := V)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hS
  simpa only [Function.comp_def, ContinuousLinearMap.coe_coe,
    LinearMap.coe_toContinuousLinearMap', traceCLM_apply] using h

/-- **Math.** **Operator Riccati ⟶ scalar Riccati.** Let `S R : ℝ → (V →L[ℝ] V)`
be paths of continuous linear operators on a finite-dimensional real inner product
space of dimension `n ≥ 2`. Suppose at time `t`:
* `S t` is symmetric and kills a fixed unit vector `u` (the radial direction);
* the Ricci-type trace bound `trace (R t) ≥ (n-1) κ`;
* the **operator matrix Riccati** `S' + S² + R = 0` holds as a genuine
  operator-valued derivative: `HasDerivAt S (-(R t) - S t ∘L S t) t`.

Then the scalar mean `a t := trace (S t) / (n-1)` satisfies the **scalar Riccati**
inequality `a'(t) + a(t)² + κ ≤ 0`.

This is `matrixRiccati_trace_scalar_riccati` fed from the genuine operator Riccati,
the trace being pushed through the operator derivative by
`hasDerivAt_trace_continuousLinearMap` — closing the trace-derivative debt of
`MatrixRiccati.lean`. -/
theorem operatorRiccati_scalar_riccati
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (S R : ℝ → (V →L[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hSsym : (S t : V →ₗ[ℝ] V).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (S t) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (R t : V →ₗ[ℝ] V))
    (hric : HasDerivAt S (-(R t) - S t ∘L S t) t)
    (a : ℝ → ℝ) (ha : ∀ s, a s = LinearMap.trace ℝ V (S s : V →ₗ[ℝ] V) / ((n : ℝ) - 1)) :
    deriv a t + a t ^ 2 + κ ≤ 0 := by
  -- Linear (LinearMap) views of the operators, consumed by the trace machinery.
  set Sₗ : ℝ → (V →ₗ[ℝ] V) := fun s => (S s : V →ₗ[ℝ] V) with hSₗ
  set Rₗ : ℝ → (V →ₗ[ℝ] V) := fun s => (R s : V →ₗ[ℝ] V) with hRₗ
  -- Push the trace through the operator derivative.
  have htr := hasDerivAt_trace_continuousLinearMap (V := V) hric
  -- Identify the derivative's trace with the traced Riccati right-hand side.
  have hrhs : LinearMap.trace ℝ V ((-(R t) - S t ∘L S t : V →L[ℝ] V) : V →ₗ[ℝ] V)
      = -(LinearMap.trace ℝ V (Sₗ t ∘ₗ Sₗ t)) - LinearMap.trace ℝ V (Rₗ t) := by
    rw [ContinuousLinearMap.coe_sub, ContinuousLinearMap.coe_neg,
      ContinuousLinearMap.coe_comp, map_sub, map_neg]
    ring
  rw [hrhs] at htr
  exact matrixRiccati_trace_scalar_riccati hn b Sₗ Rₗ κ t hSsym u hu hSu hR
    (fun s => LinearMap.trace ℝ V (Sₗ s)) (fun _ => rfl) htr a ha

/-- **Math.** **Operator Riccati ⟶ mean-curvature Riccati.** Same hypotheses as
`operatorRiccati_scalar_riccati`, but delivering the conclusion in the
**mean-curvature `m = trace S`-form** that `riccati_le_model` consumes directly:
`m'(t) + m(t)²/(n-1) + (n-1)κ ≤ 0`, where `m t = trace (S t)`. This is the operator
Riccati fed into the `m`-form trace reduction `matrixRiccati_trace_riccati`; it is
the exact `hsub` shape of the Riccati comparison engine. -/
theorem operatorRiccati_mean_riccati
    {n : ℕ} (hn : 2 ≤ n) (b : OrthonormalBasis (Fin n) ℝ V)
    (S R : ℝ → (V →L[ℝ] V)) (κ : ℝ) (t : ℝ)
    (hSsym : (S t : V →ₗ[ℝ] V).IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : (S t) u = 0)
    (hR : ((n : ℝ) - 1) * κ ≤ LinearMap.trace ℝ V (R t : V →ₗ[ℝ] V))
    (hric : HasDerivAt S (-(R t) - S t ∘L S t) t)
    (m : ℝ → ℝ) (hm : ∀ s, m s = LinearMap.trace ℝ V (S s : V →ₗ[ℝ] V)) :
    deriv m t + m t ^ 2 / ((n : ℝ) - 1) + ((n : ℝ) - 1) * κ ≤ 0 := by
  set Sₗ : ℝ → (V →ₗ[ℝ] V) := fun s => (S s : V →ₗ[ℝ] V) with hSₗ
  set Rₗ : ℝ → (V →ₗ[ℝ] V) := fun s => (R s : V →ₗ[ℝ] V) with hRₗ
  have htr := hasDerivAt_trace_continuousLinearMap (V := V) hric
  have hrhs : LinearMap.trace ℝ V ((-(R t) - S t ∘L S t : V →L[ℝ] V) : V →ₗ[ℝ] V)
      = -(LinearMap.trace ℝ V (Sₗ t ∘ₗ Sₗ t)) - LinearMap.trace ℝ V (Rₗ t) := by
    rw [ContinuousLinearMap.coe_sub, ContinuousLinearMap.coe_neg,
      ContinuousLinearMap.coe_comp, map_sub, map_neg]
    ring
  rw [hrhs] at htr
  -- Rephrase the supplied `m` as the trace function and transport its derivative.
  have hmfun : m = fun s => LinearMap.trace ℝ V (Sₗ s) := funext hm
  rw [hmfun]
  exact matrixRiccati_trace_riccati hn b Sₗ Rₗ κ t hSsym u hu hSu hR
    (fun s => LinearMap.trace ℝ V (Sₗ s)) (fun _ => rfl) htr

end OpenGA.Comparison.BishopGromov
