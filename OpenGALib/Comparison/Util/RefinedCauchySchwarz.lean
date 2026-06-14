import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Algebra.Order.Chebyshev

/-!
# Refined Cauchy–Schwarz for a symmetric operator with a unit kernel vector

Linear-algebra input to the Laplacian comparison theorem. A symmetric operator
`S` on an `n`-dimensional real inner product space with a *unit* vector `u` in
its kernel satisfies

  `(trace S)² ≤ (n - 1) · ‖S‖²_HS`,

where `‖S‖²_HS = ∑ᵢ ∑ⱼ ⟪S bᵢ, bⱼ⟫²` is the Hilbert–Schmidt / Frobenius norm
over any orthonormal basis `b`. The sharpening from the naive constant `n` to
`n - 1` is exactly the gain from `S u = 0`: the kernel direction contributes
nothing to the trace while removing one dimension from the Cauchy–Schwarz count.

In the geometric application `S = ∇(∇f)` is the shape operator (Hessian of a
distance function), `u = ∇f` its unit radial field on the eikonal locus, and the
inequality is the `(Δf)² / (n-1) ≤ |Hess f|²` step turning the Bochner identity
into the radial Riccati sub-equation.

Reference: comparison-geometry notes (CH21, trace of the shape operator).
-/

open scoped InnerProductSpace BigOperators

namespace OpenGA.Comparison.Util

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- Parseval: for an orthonormal basis, `∑ⱼ ⟪x, cⱼ⟫² = ‖x‖²` (real case). -/
private lemma parseval_sq {n : ℕ} (c : OrthonormalBasis (Fin n) ℝ V) (x : V) :
    ∑ j, (inner ℝ x (c j)) ^ 2 = ‖x‖ ^ 2 := by
  have h := c.sum_sq_norm_inner_left x
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.norm_eq_abs, sq_abs]

omit [FiniteDimensional ℝ V] in
/-- The double-sum Frobenius/HS quantity equals `∑ᵢ ‖S(cᵢ)‖²` for an orthonormal
basis `c`. -/
private lemma frobenius_eq_sum_norm_sq {n : ℕ} (c : OrthonormalBasis (Fin n) ℝ V)
    (S : V →ₗ[ℝ] V) :
    ∑ i, ∑ j, (inner ℝ (S (c i)) (c j)) ^ 2 = ∑ i, ‖S (c i)‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  exact parseval_sq c (S (c i))

omit [FiniteDimensional ℝ V] in
/-- The Hilbert–Schmidt sum `∑ᵢ ‖S cᵢ‖²` is independent of the orthonormal basis
(for a symmetric `S`). -/
private lemma hilbertSchmidt_indep {n : ℕ} (b c : OrthonormalBasis (Fin n) ℝ V)
    (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric) :
    ∑ i, ‖S (c i)‖ ^ 2 = ∑ i, ‖S (b i)‖ ^ 2 := by
  have step1 : ∑ i, ‖S (c i)‖ ^ 2 = ∑ i, ∑ j, (inner ℝ (S (c i)) (b j)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← parseval_sq b (S (c i))]
  rw [step1, Finset.sum_comm]
  have step2 : ∀ j, ∑ i, (inner ℝ (S (c i)) (b j)) ^ 2
      = ∑ i, (inner ℝ (S (b j)) (c i)) ^ 2 := by
    intro j
    apply Finset.sum_congr rfl
    intro i _
    rw [hS (c i) (b j), real_inner_comm (c i) (S (b j))]
  simp_rw [step2]
  apply Finset.sum_congr rfl
  intro j _
  exact parseval_sq c (S (b j))

/-- **Refined Cauchy–Schwarz.** A symmetric operator `S` on an `n`-dimensional
real inner product space with a unit kernel vector `u` (`‖u‖ = 1`, `S u = 0`)
satisfies `(trace S)² ≤ (n-1) · ‖S‖²_HS`, the trace and Hilbert–Schmidt norm
taken over an arbitrary orthonormal basis `b`. -/
theorem refined_cauchy_schwarz
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ V)
    (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric)
    (u : V) (hu : ‖u‖ = 1) (hSu : S u = 0) :
    (∑ i, (inner ℝ (S (b i)) (b i))) ^ 2
      ≤ ((n : ℝ) - 1) * ∑ i, ∑ j, (inner ℝ (S (b i)) (b j)) ^ 2 := by
  classical
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hcard : Module.finrank ℝ V = Fintype.card (Fin n) :=
    Module.finrank_eq_card_basis b.toBasis
  have hn1 : 1 ≤ n := by
    rw [Fintype.card_fin] at hcard
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso
      rw [h0] at hcard
      have : Subsingleton V := Module.finrank_zero_iff.mp hcard
      exact hu0 (Subsingleton.elim u 0)
    · exact hpos
  haveI : NeZero n := ⟨by omega⟩
  set v : Fin n → V := fun i => if i = (0 : Fin n) then u else 0 with hv
  have hu_orth : Orthonormal ℝ (({(0 : Fin n)} : Set (Fin n)).restrict v) := by
    rw [orthonormal_iff_ite]
    intro a c
    have ha : (a : Fin n) = 0 := a.2
    have hc : (c : Fin n) = 0 := c.2
    have hac : a = c := Subtype.ext (ha.trans hc.symm)
    simp only [Set.restrict_apply, hv, ha, hc, if_pos hac, if_true]
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  obtain ⟨e, he⟩ :=
    hu_orth.exists_orthonormalBasis_extension_of_card_eq hcard
  have he0 : e (0 : Fin n) = u := by
    have := he (0 : Fin n) (Set.mem_singleton _)
    rw [this, hv]; simp
  have htrace : ∀ (c : OrthonormalBasis (Fin n) ℝ V),
      ∑ i, (inner ℝ (S (c i)) (c i)) = LinearMap.trace ℝ V S := by
    intro c
    rw [LinearMap.trace_eq_sum_inner S c]
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm (c i) (S (c i))
  have hTbe : (∑ i, (inner ℝ (S (b i)) (b i))) = (∑ i, (inner ℝ (S (e i)) (e i))) := by
    rw [htrace b, htrace e]
  have hFbe : (∑ i, ∑ j, (inner ℝ (S (b i)) (b j)) ^ 2)
      = (∑ i, ∑ j, (inner ℝ (S (e i)) (e j)) ^ 2) := by
    rw [frobenius_eq_sum_norm_sq b S, frobenius_eq_sum_norm_sq e S]
    exact hilbertSchmidt_indep e b S hS
  rw [hTbe, hFbe, frobenius_eq_sum_norm_sq e S]
  have hSe0 : S (e (0 : Fin n)) = 0 := by rw [he0, hSu]
  set f : Fin n → ℝ := fun i => inner ℝ (S (e i)) (e i) with hf
  set g : Fin n → ℝ := fun i => ‖S (e i)‖ ^ 2 with hg
  have hf0 : f (0 : Fin n) = 0 := by simp [hf, hSe0]
  have hg0 : g (0 : Fin n) = 0 := by simp [hg, hSe0]
  have hsumT : (∑ i, f i) = ∑ i ∈ (Finset.univ.erase (0 : Fin n)), f i := by
    rw [Finset.sum_erase _ hf0]
  have hsumF : (∑ i, g i) = ∑ i ∈ (Finset.univ.erase (0 : Fin n)), g i := by
    rw [Finset.sum_erase _ hg0]
  rw [show (∑ i, (inner ℝ (S (e i)) (e i))) = ∑ i, f i from rfl, hsumT]
  rw [show (∑ i, ‖S (e i)‖ ^ 2) = ∑ i, g i from rfl, hsumF]
  set s : Finset (Fin n) := Finset.univ.erase (0 : Fin n) with hs
  have hterm : ∀ i ∈ s, (f i) ^ 2 ≤ g i := by
    intro i _
    have hcs : |inner ℝ (S (e i)) (e i)| ≤ ‖S (e i)‖ * ‖e i‖ :=
      abs_real_inner_le_norm (S (e i)) (e i)
    have hei : ‖e i‖ = 1 := e.orthonormal.1 i
    rw [hei, mul_one] at hcs
    have : (f i) ^ 2 ≤ (‖S (e i)‖) ^ 2 := by
      rw [hf]
      calc (inner ℝ (S (e i)) (e i)) ^ 2 = |inner ℝ (S (e i)) (e i)| ^ 2 := by rw [sq_abs]
        _ ≤ (‖S (e i)‖) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) hcs
    rwa [hg]
  have hcheb : (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
    exact_mod_cast this
  have hcard_s : s.card = n - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hncast : (s.card : ℝ) = (n : ℝ) - 1 := by
    rw [hcard_s, Nat.cast_sub hn1]; simp
  have hsum_le : ∑ i ∈ s, (f i) ^ 2 ≤ ∑ i ∈ s, g i :=
    Finset.sum_le_sum hterm
  have hnneg : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  calc (∑ i ∈ s, f i) ^ 2
      ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := hcheb
    _ = ((n : ℝ) - 1) * ∑ i ∈ s, (f i) ^ 2 := by rw [hncast]
    _ ≤ ((n : ℝ) - 1) * ∑ i ∈ s, g i := by
        apply mul_le_mul_of_nonneg_left hsum_le hnneg

end OpenGA.Comparison.Util
