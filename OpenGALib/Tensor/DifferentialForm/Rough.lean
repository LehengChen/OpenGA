import OpenGALib.Tensor.Alternating.Bundle
import OpenGALib.Tensor.Alternating.FDeriv
import OpenGALib.Tensor.Alternating.Wedge
import OpenGALib.Tensor.DifferentialForm.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Rough (point-eval) computations for differential forms

Pointwise evaluation, smoothness lemmas, and exterior derivative on
representatives. The "rough" name signals this is the computational layer
used to derive the polished `Basic` API.
-/

noncomputable section

open Filter ContinuousAlternatingMap Set
open scoped Topology

variable {E F F' F'' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [NormedAddCommGroup F''] [NormedSpace ℝ F'']
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n m k : ℕ}


section RoughDifferentialForm

variable {n m k : ℕ}
variable {v : E}
/- Generic (possibly non-smooth) differential n-form. -/
variable (ω τ : E → E [⋀^Fin n]→L[ℝ] F)
variable (f : E → F)

@[simp]
theorem add_apply : (ω + τ) v = ω v + τ v :=
  rfl

@[simp]
theorem sub_apply : (ω - τ) v = ω v - τ v :=
  rfl

@[simp]
theorem neg_apply : (-ω) v = -ω v :=
  rfl

@[simp]
theorem smul_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) : (c • ω) v = c • ω v :=
  rfl

@[simp]
theorem zero_apply : (0 : E → E [⋀^Fin n]→L[ℝ] F) v = 0 :=
  rfl

/- The natural equivalence between differential forms from `E` to `F`
and maps from `E` to continuous 1-multilinear alternating maps from `E` to `F`. -/
def ofSubsingleton :
    (E → E →L[ℝ] F) ≃ (E → E [⋀^Fin 1]→L[ℝ] F) where
  toFun f := fun e ↦ ContinuousAlternatingMap.ofSubsingleton ℝ E F 0 (f e)
  invFun f := fun e ↦ (ContinuousAlternatingMap.ofSubsingleton ℝ E F 0).symm (f e)
  left_inv _ := rfl
  right_inv _ := by simp

/- The constant map is a differential form when `Fin n` is empty -/
def constOfIsEmpty (x : F) : E → E [⋀^Fin 0]→L[ℝ] F :=
  fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) x

/-- Exterior derivative of a differential form.

Thin wrapper over Mathlib's `ContinuousAlternatingMap.extDeriv`: the two agree
(`extDeriv ω x = .alternatizeUncurryFin (fderiv ℝ ω x)`), so the whole `ederiv`
API below is re-derived from the corresponding `extDeriv` lemmas. -/
def ederiv (ω : E → E [⋀^Fin n]→L[ℝ] F) : E → E [⋀^Fin (n + 1)]→L[ℝ] F :=
  extDeriv ω

/-- Exterior derivative of a differential form within a set.
Thin wrapper over Mathlib's `ContinuousAlternatingMap.extDerivWithin`. -/
def ederivWithin (ω : E → E [⋀^Fin n]→L[ℝ] F) (s : Set E) : E → E [⋀^Fin (n + 1)]→L[ℝ] F :=
  extDerivWithin ω s

/-- Bridge between `ederiv` and the local `uncurryFin` packaging used by the
wedge/Leibniz API: `ederiv ω x = uncurryFin (fderiv ℝ ω x)`. Both sides have the
same underlying alternating map, so this holds unconditionally. -/
theorem ederiv_eq_uncurryFin (ω : E → E [⋀^Fin n]→L[ℝ] F) (x : E) :
    ederiv ω x = ContinuousAlternatingMap.uncurryFin (fderiv ℝ ω x) := by
  show extDeriv ω x = _
  ext v
  rw [ContinuousAlternatingMap.uncurryFin_apply, extDeriv,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]

@[simp]
theorem ederivWithin_univ (ω : E → E [⋀^Fin n]→L[ℝ] F) :
    ederivWithin ω univ = ederiv ω :=
  extDerivWithin_univ ω

theorem ederivWithin_add (ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F) (s : Set E) {x : E}
    (hsx : UniqueDiffWithinAt ℝ s x)
    (hω₁ : DifferentiableWithinAt ℝ ω₁ s x) (hω₂ : DifferentiableWithinAt ℝ ω₂ s x) :
    ederivWithin (ω₁ + ω₂) s x = ederivWithin ω₁ s x + ederivWithin ω₂ s x :=
  extDerivWithin_add hsx hω₁ hω₂

theorem ederivWithin_smul (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) (s : Set E) {x : E}
    (hsx : UniqueDiffWithinAt ℝ s x) :
      ederivWithin (c • ω) s x = c • ederivWithin ω s x :=
  extDerivWithin_smul c ω hsx

theorem Filter.EventuallyEq.ederivWithin_eq {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.extDerivWithin_eq hx

theorem Filter.EventuallyEq.ederivWithin_eq_of_mem {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.extDerivWithin_eq_of_mem hx

theorem Filter.EventuallyEq.ederivWithin_eq_of_insert {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[insert x s] x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  hs.extDerivWithin_eq_of_insert

theorem Filter.EventuallyEq.ederivWithin' {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s t : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) (ht : t ⊆ s) : ederivWithin ω₁ t =ᶠ[𝓝[s] x] ederivWithin ω₂ t :=
  hs.extDerivWithin' ht

protected theorem Filter.EverntuallyEq.ederivWithin {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : ω₁ =ᶠ[𝓝[s] x] ω₂) : ederivWithin ω₁ s =ᶠ[𝓝[s] x] ederivWithin ω₂ s :=
  hs.extDerivWithin

theorem Filter.EventuallyEq.ederivWithin_eq_nhds {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  h.extDerivWithin_eq_nhds

theorem ederivWithin_congr {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : ω₁ x = ω₂ x) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  extDerivWithin_congr hs hx

theorem ederivWithin_congr' {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {s : Set E} {x : E}
    (hs : EqOn ω₁ ω₂ s) (hx : x ∈ s) : ederivWithin ω₁ s x = ederivWithin ω₂ s x :=
  extDerivWithin_congr' hs hx

theorem ederivWithin_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} {x : E}
    (h : DifferentiableWithinAt ℝ ω s x) (hs : UniqueDiffWithinAt ℝ s x) (v : Fin (n + 1) → E) :
      ederivWithin ω s x v = ∑ i, (-1) ^ i.val • fderivWithin ℝ (ω · (i.removeNth v)) s x (v i) :=
  extDerivWithin_apply h hs v

theorem ederivWithin_ederivWithin_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} {x}
    (hxx : x ∈ closure (interior s)) (hx : x ∈ s) (h : ContDiffWithinAt ℝ 2 ω s x)
    (hs : UniqueDiffOn ℝ s) :
    ederivWithin (ederivWithin ω s) s x = 0 :=
  extDerivWithin_extDerivWithin_apply h (by simp [minSmoothness_of_isRCLikeNormedField]) hs hxx hx

theorem ederivWithin_ederivWithin (ω : E → E [⋀^Fin n]→L[ℝ] F) {s : Set E} (h : ContDiffOn ℝ 2 ω s)
    (hs : UniqueDiffOn ℝ s) :
    EqOn (ederivWithin (ederivWithin ω s) s) 0 (s ∩ (closure (interior s))) :=
  extDerivWithin_extDerivWithin_eqOn h (by simp [minSmoothness_of_isRCLikeNormedField]) hs

theorem ederiv_add (ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (hω₁ : DifferentiableAt ℝ ω₁ x)
    (hω₂ : DifferentiableAt ℝ ω₂ x) : ederiv (ω₁ + ω₂) x = ederiv ω₁ x + ederiv ω₂ x :=
  extDeriv_add hω₁ hω₂

theorem ederiv_smul (ω : E → E [⋀^Fin n]→L[ℝ] F) (c : ℝ) {x : E} :
    ederiv (c • ω) x = c • ederiv ω x :=
  extDeriv_smul c ω

theorem Filter.EventuallyEq.ederiv_eq {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ x = ederiv ω₂ x :=
  h.extDeriv_eq

protected theorem Filter.EventuallyEq.ederiv {ω₁ ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E}
    (h : ω₁ =ᶠ[𝓝 x] ω₂) : ederiv ω₁ =ᶠ[𝓝 x] ederiv ω₂ :=
  h.extDeriv

theorem ederiv_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (hx : DifferentiableAt ℝ ω x)
    (v : Fin (n + 1) → E) :
    ederiv ω x v = ∑ i, (-1) ^ i.val • fderiv ℝ (ω · (i.removeNth v)) x (v i) :=
  extDeriv_apply hx v

theorem ederiv_ederiv_apply (ω : E → E [⋀^Fin n]→L[ℝ] F) {x : E} (h : ContDiffAt ℝ 2 ω x) :
    ederiv (ederiv ω) x = 0 :=
  extDeriv_extDeriv_apply h (by simp [minSmoothness_of_isRCLikeNormedField])

theorem ederiv_ederiv (ω : E → E [⋀^Fin n]→L[ℝ] F) (h : ContDiff ℝ 2 ω) : ederiv (ederiv ω) = 0 :=
  extDeriv_extDeriv h (by simp [minSmoothness_of_isRCLikeNormedField])



end RoughDifferentialForm

/- Pullback of a form under a function -/
namespace RoughDifferentialForm

def domDomCongr (σ : Fin n ≃ Fin m) (ω : E → E [⋀^Fin n]→L[ℝ] F) : E → E [⋀^Fin m]→L[ℝ] F :=
  fun e => (ω e).domDomCongr σ

theorem domDomCongr_apply (σ : Fin n ≃ Fin m) (ω : E → E [⋀^Fin n]→L[ℝ] F) (e : E) (v : Fin m → E) :
    (domDomCongr σ ω) e v = (ω e) (v ∘ σ)  :=
  rfl

/- Pullback of a differential form -/
def pullback (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) : E → E [⋀^Fin k]→L[ℝ] G :=
    fun x ↦ (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)

theorem pullback_zero (f : E → F) :
    pullback f (0 : F → F [⋀^Fin k]→L[ℝ] G) = 0 :=
  rfl

theorem pullback_add (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (τ : F → F [⋀^Fin k]→L[ℝ] G) :
    pullback f (ω + τ) = pullback f ω + pullback f τ :=
  rfl

theorem pullback_sub (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (τ : F → F [⋀^Fin k]→L[ℝ] G) :
    pullback f (ω - τ) = pullback f ω - pullback f τ :=
  rfl

theorem pullback_neg (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) :
    - pullback f ω = pullback f (-ω) :=
  rfl

theorem pullback_smul (f : E → F) (ω : F → F [⋀^Fin k]→L[ℝ] G) (c : ℝ) :
    c • (pullback f ω) = pullback f (c • ω) :=
  rfl

theorem pullback_ofSubsingleton (f : E → F) (ω : F → F →L[ℝ] G) :
    pullback f (ofSubsingleton ω) = ofSubsingleton (fun e ↦ (ω (f e)).comp (fderiv ℝ f e)) :=
  rfl

theorem pullback_constOfIsEmpty (f : E → F) (g : G) :
    pullback f (constOfIsEmpty g) = fun _ ↦ (ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) g)
  := rfl

/- Interior product of differential forms -/
def iprod (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] F) (v : E → E) : E → E [⋀^Fin m]→L[ℝ] F :=
    fun e => ContinuousAlternatingMap.curryFin (ω e) (v e)

theorem iprod_apply (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] F) (v : E → E) (e : E) :
    iprod ω v e = ContinuousAlternatingMap.curryFin (ω e) (v e) :=
  rfl

/- Interior product is antisymmetric -/
theorem iprod_antisymm (ω : E → E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (v w : E → E) (e : E) (m' : Fin m → E) :
    iprod (iprod ω v) w e m' = - iprod (iprod ω w) v e m' := by
  repeat
    rw[iprod_apply, curryFin_apply]
  let h := AlternatingMap.map_swap (ω e).toAlternatingMap (Fin.cons (w e) (Fin.cons (v e) m'))
    Fin.zero_ne_one
  rw [@coe_toAlternatingMap] at h
  rw [← h]
  clear h
  congr 1
  ext i
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  obtain (rfl | ⟨ i , rfl ⟩) := i.eq_zero_or_eq_succ
  · simp
  · rw[Function.comp_apply, Equiv.swap_apply_of_ne_of_ne] <;>
    simp only [Fin.cons_succ, ← Fin.succ_zero_eq_one, ne_eq, Fin.succ_inj,
      Fin.succ_ne_zero, not_false_eq_true]

/- Interior product with twice the same vector field is zero -/
theorem iprod_iprod (ω : E → E [⋀^Fin (m + 2)]→L[ℝ] ℝ) (v : E → E) :
    iprod (iprod ω v) v = 0 := by
  ext e m'
  let h := iprod_antisymm ω v v e m'
  rw [eq_neg_iff_add_eq_zero, add_self_eq_zero] at h
  exact h

/- Wedge product of differential forms -/
def wedge_product (ω₁ : E → E [⋀^Fin m]→L[ℝ] F) (ω₂ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    E → E [⋀^Fin (m + n)]→L[ℝ] F'' := fun e => ContinuousAlternatingMap.wedge_product (ω₁ e) (ω₂ e) f

-- TODO: change notation
notation ω₁ "∧r["f"]" ω₂ => wedge_product ω₁ ω₂ f
notation ω₁ "∧r" ω₂ => wedge_product ω₁ ω₂ (ContinuousLinearMap.mul ℝ ℝ)

theorem wedge_product_def {ω₁ : E → E [⋀^Fin m]→L[ℝ] F} {ω₂ : E → E [⋀^Fin n]→L[ℝ] F'} {f : F →L[ℝ] F' →L[ℝ] F''}
    {x : E} : (ω₁ ∧r[f] ω₂) x = ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) f :=
  rfl

/- The wedge product wrt multiplication -/
theorem wedge_product_mul {ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ} {ω₂ : E → E [⋀^Fin n]→L[ℝ] ℝ} {x : E} :
    (ω₁ ∧r ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.mul ℝ ℝ) :=
  rfl

/- The wedge product wrt scalar multiplication -/
theorem wedge_product_lsmul {ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ} {ω₂ : E → E [⋀^Fin n]→L[ℝ] F} {x : E} :
    (ω₁ ∧r[ContinuousLinearMap.lsmul ℝ ℝ] ω₂) x =
    ContinuousAlternatingMap.wedge_product (ω₁ x) (ω₂ x) (ContinuousLinearMap.lsmul ℝ ℝ) :=
  rfl

/- Associativity of wedge product -/
theorem wedge_assoc [FiniteDimensional ℝ E]
    (ω₁ : E → E [⋀^Fin m]→L[ℝ] ℝ) (ω₂ : E → E [⋀^Fin n]→L[ℝ] ℝ) (ω₃ : E → E [⋀^Fin k]→L[ℝ] ℝ) :
    domDomCongr Fin.finAssoc.symm (ω₁ ∧r ω₂ ∧r ω₃) = (ω₁ ∧r ω₂) ∧r ω₃ := by
  ext x y
  rw[wedge_product_def, wedge_product_def, domDomCongr_apply, wedge_product_def, wedge_product_def,
    ← ContinuousAlternatingMap.domDomCongr_apply]
  exact ContinuousAlternatingMap.wedge_mul_assoc (ω₁ x) (ω₂ x) (ω₃ x) y

/- Left distributivity of wedge product -/
theorem add_wedge (ω₁ ω₂ : E → E [⋀^Fin m]→L[ℝ] F) (τ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    ((ω₁ + ω₂) ∧r[f] τ) = (ω₁ ∧r[f] τ) + (ω₂ ∧r[f] τ) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.add_wedge (ω₁ x) (ω₂ x) (τ x) f

/- Right distributivity of wedge product -/
theorem wedge_add (ω : E → E [⋀^Fin m]→L[ℝ] F) (τ₁ τ₂ : E → E [⋀^Fin n]→L[ℝ] F') (f : F →L[ℝ] F' →L[ℝ] F'') :
    (ω ∧r[f] (τ₁ + τ₂)) = (ω ∧r[f] τ₁) + (ω ∧r[f] τ₂) := by
  ext1 x
  rw[wedge_product_def, _root_.add_apply, _root_.add_apply, wedge_product_def, wedge_product_def]
  exact ContinuousAlternatingMap.wedge_add (ω x) (τ₁ x) (τ₂ x) f

theorem smul_wedge (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) (c : ℝ) :
    c • (ω ∧r τ) = (c • ω) ∧r τ := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact (ContinuousAlternatingMap.smul_wedge c (ω x) (τ x)
    (ContinuousLinearMap.mul ℝ ℝ)).symm

theorem wedge_smul (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) (c : ℝ) :
    c • (ω ∧r τ) = ω ∧r (c • τ) := by
  ext1 x
  rw[_root_.smul_apply, wedge_product_mul, wedge_product_mul, _root_.smul_apply]
  exact (ContinuousAlternatingMap.wedge_smul c (ω x) (τ x)
    (ContinuousLinearMap.mul ℝ ℝ)).symm

/- Antisymmetry of multiplication wedge product -/
theorem wedge_antisymm [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (τ : E → E [⋀^Fin n]→L[ℝ] ℝ) :
    (ω ∧r τ) = RoughDifferentialForm.domDomCongr Fin.finAddCongr ((-1 : ℝ)^(m*n) • (τ ∧r ω)) := by
  ext x y
  rw[wedge_product_mul, domDomCongr_apply, _root_.smul_apply,
    wedge_product_mul, ← ContinuousAlternatingMap.domDomCongr_apply]
  let h := ContinuousAlternatingMap.wedge_antisymm (ω x) (τ x)
  exact congrFun (congrArg DFunLike.coe h) y

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]

/- Corollary of `wedge_antisymm` saying that a wedge of a m-form with itself is
zero if m is odd. -/
theorem wedge_self_odd_zero [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin m]→L[ℝ] ℝ) (m_odd : Odd m) :
    (ω ∧r ω) = 0 := by
  ext1 x
  rw[wedge_product_mul]
  exact ContinuousAlternatingMap.wedge_self_odd_zero (ω x) m_odd

/- Pullback commutes with taking the wedge product -/
theorem pullback_wedge (f : G → E) (ω₁ : E → E [⋀^Fin m]→L[ℝ] F) (ω₂ : E → E [⋀^Fin n]→L[ℝ] F')
    (f' : F →L[ℝ] F' →L[ℝ] F'') : pullback f (ω₁ ∧r[f'] ω₂) = pullback f ω₁ ∧r[f'] pullback f ω₂ := by
  ext x y
  rw[wedge_product_def, pullback, wedge_product_def, pullback, pullback,
    compContinuousLinearMap_apply]
  rw[ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousAlternatingMap.wedge_product_def, uncurryFinAdd,
    ContinuousAlternatingMap.domDomCongr_apply, uncurrySum_apply,
    ContinuousMultilinearMap.sum_apply, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rcases σ with ⟨σ₁⟩
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply]
  rw[uncurrySum.summand_mk]
  rw[ContinuousMultilinearMap.smul_apply, ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurrySum_apply, ContinuousMultilinearMap.flipMultilinear_apply,
    coe_toContinuousMultilinearMap, ContinuousMultilinearMap.flipAlternating_apply,
    coe_toContinuousMultilinearMap, ContinuousLinearMap.compContinuousAlternatingMap₂_apply,
    compContinuousLinearMap_apply, compContinuousLinearMap_apply]
  simp only [Function.comp_apply, smul_left_cancel_iff]
  rfl

theorem iprod_wedge [FiniteDimensional ℝ E]
    (ω : E → E [⋀^Fin (m + 1)]→L[ℝ] ℝ) (τ : E → E [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (v : E → E) :
      iprod (domDomCongr Fin.finAddFlipAssoc (ω ∧r τ)) v = ((iprod ω v) ∧r τ)
        + (-1 : ℝ)^(m + 1) • (domDomCongr Fin.finAddFlipAssoc (ω ∧r (iprod τ v))) := by
  funext e
  exact ContinuousAlternatingMap.iprod_wedge_product_mul (ω e) (τ e) (v e)

end RoughDifferentialForm
