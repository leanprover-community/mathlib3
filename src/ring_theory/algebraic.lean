/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.finite_dimensional
import ring_theory.integral_closure
import data.polynomial.integral_normalization

/-!
# Algebraic elements and algebraic extensions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

universes u v w

open_locale classical polynomial
open polynomial

section
variables (R : Type u) {A : Type v} [comm_ring R] [ring A] [algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
def is_algebraic (x : A) : Prop :=
∃ p : R[X], p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def transcendental (x : A) : Prop := ¬ is_algebraic R x

lemma is_transcendental_of_subsingleton [subsingleton R] (x : A) : transcendental R x :=
λ ⟨p, h, _⟩, h $ subsingleton.elim p 0

variables {R}

/-- A subalgebra is algebraic if all its elements are algebraic. -/
def subalgebra.is_algebraic (S : subalgebra R A) : Prop := ∀ x ∈ S, is_algebraic R x

variables (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
def algebra.is_algebraic : Prop := ∀ x : A, is_algebraic R x

variables {R A}

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
lemma subalgebra.is_algebraic_iff (S : subalgebra R A) :
  S.is_algebraic ↔ @algebra.is_algebraic R S _ _ S.algebra :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  rw subtype.forall',
  refine forall_congr (λ x, exists_congr (λ p, and_congr iff.rfl _)),
  have h : function.injective S.val := subtype.val_injective,
  conv_rhs { rw [← h.eq_iff, alg_hom.map_zero] },
  rw [← aeval_alg_hom_apply, S.val_apply]
end

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
lemma algebra.is_algebraic_iff : algebra.is_algebraic R A ↔ (⊤ : subalgebra R A).is_algebraic :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  simp only [algebra.mem_top, forall_prop_of_true, iff_self],
end

lemma is_algebraic_iff_not_injective {x : A} : is_algebraic R x ↔
  ¬ function.injective (polynomial.aeval x : R[X] →ₐ[R] A) :=
by simp only [is_algebraic, injective_iff_map_eq_zero, not_forall, and.comm, exists_prop]

end

section zero_ne_one
variables (R : Type u) {S : Type*} {A : Type v} [comm_ring R]
variables [comm_ring S] [ring A] [algebra R A] [algebra R S] [algebra S A]
variables [is_scalar_tower R S A]

/-- An integral element of an algebra is algebraic.-/
lemma is_integral.is_algebraic [nontrivial R] {x : A} : is_integral R x → is_algebraic R x :=
λ ⟨p, hp, hpx⟩, ⟨p, hp.ne_zero, hpx⟩

variables {R}

lemma is_algebraic_zero [nontrivial R] : is_algebraic R (0 : A) :=
⟨_, X_ne_zero, aeval_X 0⟩

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
lemma is_algebraic_algebra_map [nontrivial R] (x : R) : is_algebraic R (algebra_map R A x) :=
⟨_, X_sub_C_ne_zero x, by rw [_root_.map_sub, aeval_X, aeval_C, sub_self]⟩

lemma is_algebraic_one [nontrivial R] : is_algebraic R (1 : A) :=
by { rw ←_root_.map_one _, exact is_algebraic_algebra_map 1 }

lemma is_algebraic_nat [nontrivial R] (n : ℕ) : is_algebraic R (n : A) :=
by { rw ←map_nat_cast _, exact is_algebraic_algebra_map n }

lemma is_algebraic_int [nontrivial R] (n : ℤ) : is_algebraic R (n : A) :=
by { rw ←_root_.map_int_cast (algebra_map R A), exact is_algebraic_algebra_map n }

lemma is_algebraic_rat (R : Type u) {A : Type v} [division_ring A] [field R] [algebra R A] (n : ℚ) :
  is_algebraic R (n : A) :=
by { rw ←map_rat_cast (algebra_map R A), exact is_algebraic_algebra_map n }

lemma is_algebraic_of_mem_root_set {R : Type u} {A : Type v} [field R] [field A] [algebra R A]
  {p : R[X]} {x : A} (hx : x ∈ p.root_set A) : is_algebraic R x :=
⟨p, ne_zero_of_mem_root_set hx, aeval_eq_zero_of_mem_root_set hx⟩

open is_scalar_tower

lemma is_algebraic_algebra_map_of_is_algebraic {a : S} :
  is_algebraic R a → is_algebraic R (algebra_map S A a) :=
λ ⟨f, hf₁, hf₂⟩, ⟨f, hf₁, by rw [aeval_algebra_map_apply, hf₂, map_zero]⟩

/-- This is slightly more general than `is_algebraic_algebra_map_of_is_algebraic` in that it
  allows noncommutative intermediate rings `A`. -/
lemma is_algebraic_alg_hom_of_is_algebraic {B} [ring B] [algebra R B]
  (f : A →ₐ[R] B) {a : A} (h : is_algebraic R a) : is_algebraic R (f a) :=
let ⟨p, hp, ha⟩ := h in ⟨p, hp, by rw [aeval_alg_hom, f.comp_apply, ha, map_zero]⟩

/-- Transfer `algebra.is_algebraic` across an `alg_equiv`. -/
lemma _root_.alg_equiv.is_algebraic {B} [ring B] [algebra R B] (e : A ≃ₐ[R] B)
  (h : algebra.is_algebraic R A) : algebra.is_algebraic R B :=
λ b, by convert ← is_algebraic_alg_hom_of_is_algebraic e.to_alg_hom (h _); apply e.apply_symm_apply

lemma _root_.alg_equiv.is_algebraic_iff {B} [ring B] [algebra R B] (e : A ≃ₐ[R] B) :
  algebra.is_algebraic R A ↔ algebra.is_algebraic R B := ⟨e.is_algebraic, e.symm.is_algebraic⟩

lemma is_algebraic_algebra_map_iff {a : S} (h : function.injective (algebra_map S A)) :
  is_algebraic R (algebra_map S A a) ↔ is_algebraic R a :=
⟨λ ⟨p, hp0, hp⟩, ⟨p, hp0, h (by rwa [map_zero, ← aeval_algebra_map_apply])⟩,
  is_algebraic_algebra_map_of_is_algebraic⟩

lemma is_algebraic_of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : is_algebraic R (r ^ n)) :
  is_algebraic R r :=
begin
  obtain ⟨p, p_nonzero, hp⟩ := ht,
  refine ⟨polynomial.expand _ n p, _, _⟩,
  { rwa polynomial.expand_ne_zero hn },
  { rwa polynomial.expand_aeval n p r },
end

lemma transcendental.pow {r : A} (ht : transcendental R r) {n : ℕ} (hn : 0 < n) :
  transcendental R (r ^ n) :=
λ ht', ht $ is_algebraic_of_pow hn ht'

end zero_ne_one

section field
variables {K : Type u} {A : Type v} [field K] [ring A] [algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral.-/
lemma is_algebraic_iff_is_integral {x : A} :
  is_algebraic K x ↔ is_integral K x :=
begin
  refine ⟨_, is_integral.is_algebraic K⟩,
  rintro ⟨p, hp, hpx⟩,
  refine ⟨_, monic_mul_leading_coeff_inv hp, _⟩,
  rw [← aeval_def, alg_hom.map_mul, hpx, zero_mul],
end

protected lemma algebra.is_algebraic_iff_is_integral :
  algebra.is_algebraic K A ↔ algebra.is_integral K A :=
⟨λ h x, is_algebraic_iff_is_integral.mp (h x),
  λ h x, is_algebraic_iff_is_integral.mpr (h x)⟩

end field

namespace algebra
variables {K : Type*} {L : Type*} {R : Type*} {S : Type*} {A : Type*}
variables [field K] [field L] [comm_ring R] [comm_ring S] [comm_ring A]
variables [algebra K L] [algebra L A] [algebra K A] [is_scalar_tower K L A]
variables [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K A :=
begin
  simp only [is_algebraic, is_algebraic_iff_is_integral] at L_alg A_alg ⊢,
  exact is_integral_trans L_alg A_alg,
end

variables (K L)

/-- If x is algebraic over R, then x is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
lemma _root_.is_algebraic_of_larger_base_of_injective (hinj : function.injective (algebra_map R S))
  {x : A} (A_alg : _root_.is_algebraic R x) : _root_.is_algebraic S x :=
let ⟨p, hp₁, hp₂⟩ := A_alg in
⟨p.map (algebra_map _ _),
  by rwa [ne.def, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot],
  by simpa⟩

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
lemma is_algebraic_of_larger_base_of_injective (hinj : function.injective (algebra_map R S))
  (A_alg : is_algebraic R A) : is_algebraic S A :=
λ x, is_algebraic_of_larger_base_of_injective hinj (A_alg x)

/-- If x is a algebraic over K, then x is algebraic over L when L is an extension of K -/
lemma _root_.is_algebraic_of_larger_base {x : A} (A_alg : _root_.is_algebraic K x) :
  _root_.is_algebraic L x :=
_root_.is_algebraic_of_larger_base_of_injective (algebra_map K L).injective A_alg

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
lemma is_algebraic_of_larger_base (A_alg : is_algebraic K A) : is_algebraic L A :=
is_algebraic_of_larger_base_of_injective (algebra_map K L).injective A_alg

variables (K L)

/-- A field extension is integral if it is finite. -/
lemma is_integral_of_finite [finite_dimensional K L] : algebra.is_integral K L :=
λ x, is_integral_of_submodule_noetherian ⊤
  (is_noetherian.iff_fg.2 infer_instance) x algebra.mem_top

/-- A field extension is algebraic if it is finite. -/
lemma is_algebraic_of_finite [finite : finite_dimensional K L] : is_algebraic K L :=
algebra.is_algebraic_iff_is_integral.mpr (is_integral_of_finite K L)

variables {K L}

theorem is_algebraic.alg_hom_bijective
  (ha : algebra.is_algebraic K L) (f : L →ₐ[K] L) : function.bijective f :=
begin
  refine ⟨f.to_ring_hom.injective, λ b, _⟩,
  obtain ⟨p, hp, he⟩ := ha b,
  let f' : p.root_set L → p.root_set L := (root_set_maps_to' id f).restrict f _ _,
  have : function.surjective f' := finite.injective_iff_surjective.1
    (λ _ _ h, subtype.eq $ f.to_ring_hom.injective $ subtype.ext_iff.1 h),
  obtain ⟨a, ha⟩ := this ⟨b, mem_root_set.2 ⟨hp, he⟩⟩,
  exact ⟨a, subtype.ext_iff.1 ha⟩,
end

theorem _root_.alg_hom.bijective [finite_dimensional K L] (ϕ : L →ₐ[K] L) : function.bijective ϕ :=
(algebra.is_algebraic_of_finite K L).alg_hom_bijective ϕ

variables (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps] noncomputable
def is_algebraic.alg_equiv_equiv_alg_hom
  (ha : algebra.is_algebraic K L) : (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
{ to_fun := λ ϕ, ϕ.to_alg_hom,
  inv_fun := λ ϕ, alg_equiv.of_bijective ϕ (ha.alg_hom_bijective ϕ),
  left_inv := λ _, by {ext, refl},
  right_inv := λ _, by {ext, refl},
  map_mul' := λ _ _, rfl }

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[reducible] noncomputable def _root_.alg_equiv_equiv_alg_hom [finite_dimensional K L] :
  (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) := (algebra.is_algebraic_of_finite K L).alg_equiv_equiv_alg_hom K L

end algebra

variables {R S : Type*} [comm_ring R] [is_domain R] [comm_ring S]

lemma exists_integral_multiple [algebra R S] {z : S} (hz : is_algebraic R z)
  (inj : ∀ x, algebra_map R S x = 0 → x = 0) :
  ∃ (x : integral_closure R S) (y ≠ (0 : R)),
    z * algebra_map R S y = x :=
begin
  rcases hz with ⟨p, p_ne_zero, px⟩,
  set a := p.leading_coeff with a_def,
  have a_ne_zero : a ≠ 0 := mt polynomial.leading_coeff_eq_zero.mp p_ne_zero,
  have y_integral : is_integral R (algebra_map R S a) := is_integral_algebra_map,
  have x_integral : is_integral R (z * algebra_map R S a) :=
    ⟨p.integral_normalization,
     monic_integral_normalization p_ne_zero,
     integral_normalization_aeval_eq_zero px inj⟩,
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩
end

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `S` is the integral closure of `R` in an algebraic extension `L` of `R`. -/
lemma is_integral_closure.exists_smul_eq_mul {L : Type*} [field L]
  [algebra R S] [algebra S L] [algebra R L] [is_scalar_tower R S L] [is_integral_closure S R L]
  (h : algebra.is_algebraic R L) (inj : function.injective (algebra_map R L))
  (a : S) {b : S} (hb : b ≠ 0) : ∃ (c : S) (d ≠ (0 : R)), d • a = b * c :=
begin
  obtain ⟨c, d, d_ne, hx⟩ := exists_integral_multiple
    (h (algebra_map _ L a / algebra_map _ L b))
    ((injective_iff_map_eq_zero _).mp inj),
  refine ⟨is_integral_closure.mk' S (c : L) c.2, d, d_ne,
    is_integral_closure.algebra_map_injective S R L _⟩,
  simp only [algebra.smul_def, ring_hom.map_mul, is_integral_closure.algebra_map_mk', ← hx,
    ← is_scalar_tower.algebra_map_apply],
  rw [← mul_assoc _ (_ / _), mul_div_cancel' (algebra_map S L a), mul_comm],
  exact mt ((injective_iff_map_eq_zero _).mp (is_integral_closure.algebra_map_injective S R L) _) hb
end

section field

variables {K L : Type*} [field K] [field L] [algebra K L] (A : subalgebra K L)

lemma inv_eq_of_aeval_div_X_ne_zero {x : L} {p : K[X]}
  (aeval_ne : aeval x (div_X p) ≠ 0) :
  x⁻¹ = aeval x (div_X p) / (aeval x p - algebra_map _ _ (p.coeff 0)) :=
begin
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm],
  conv_lhs { rw ← div_X_mul_X_add p },
  rw [alg_hom.map_add, alg_hom.map_mul, aeval_X, aeval_C],
  exact aeval_ne
end

lemma inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]}
  (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) :
  x⁻¹ = - (aeval x (div_X p) / algebra_map _ _ (p.coeff 0)) :=
begin
  convert inv_eq_of_aeval_div_X_ne_zero (mt (λ h, (algebra_map K L).injective _) coeff_zero_ne),
  { rw [aeval_eq, zero_sub, div_neg] },
  rw ring_hom.map_zero,
  convert aeval_eq,
  conv_rhs { rw ← div_X_mul_X_add p },
  rw [alg_hom.map_add, alg_hom.map_mul, h, zero_mul, zero_add, aeval_C]
end

lemma subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
  (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A :=
begin
  suffices : (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (div_X p),
  { rw [this], exact A.smul_mem (aeval x _).2 _ },
  have : aeval (x : L) p = 0, by rw [subalgebra.aeval_coe, aeval_eq, subalgebra.coe_zero],
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul,
    algebra.smul_def, map_inv₀, map_neg, inv_neg, neg_mul, subalgebra.aeval_coe]
end

lemma subalgebra.inv_mem_of_algebraic {x : A} (hx : is_algebraic K (x : L)) : (x⁻¹ : L) ∈ A :=
begin
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx,
  rw [subalgebra.aeval_coe, subalgebra.coe_eq_zero] at aeval_eq,
  revert ne_zero aeval_eq,
  refine p.rec_on_horner _ _ _,
  { intro h,
    contradiction },
  { intros p a hp ha ih ne_zero aeval_eq,
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq _,
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl] },
  { intros p hp ih ne_zero aeval_eq,
    rw [alg_hom.map_mul, aeval_X, mul_eq_zero] at aeval_eq,
    cases aeval_eq with aeval_eq x_eq,
    { exact ih hp aeval_eq },
    { rw [x_eq, subalgebra.coe_zero, inv_zero],
      exact A.zero_mem } }
end

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
lemma subalgebra.is_field_of_algebraic (hKL : algebra.is_algebraic K L) : is_field A :=
{ mul_inv_cancel := λ a ha, ⟨
        ⟨a⁻¹, A.inv_mem_of_algebraic (hKL a)⟩,
        subtype.ext (mul_inv_cancel (mt (subalgebra.coe_eq_zero _).mp ha))⟩,
  .. show nontrivial A, by apply_instance,
  .. subalgebra.to_comm_ring A }

end field

section pi

variables (R' : Type u) (S' : Type v) (T' : Type w)

/-- This is not an instance as it forms a diamond with `pi.has_smul`.

See the `instance_diamonds` test for details. -/
def polynomial.has_smul_pi [semiring R'] [has_smul R' S'] :
  has_smul (R'[X]) (R' → S') :=
⟨λ p f x, eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `pi.has_smul`.

See the `instance_diamonds` test for details. -/
noncomputable def polynomial.has_smul_pi' [comm_semiring R'] [semiring S'] [algebra R' S']
  [has_smul S' T'] :
  has_smul (R'[X]) (S' → T') :=
⟨λ p f x, aeval x p • f x⟩

variables {R} {S}

local attribute [instance] polynomial.has_smul_pi polynomial.has_smul_pi'

@[simp] lemma polynomial_smul_apply [semiring R'] [has_smul R' S']
  (p : R'[X]) (f : R' → S') (x : R') :
  (p • f) x = eval x p • f x := rfl

@[simp] lemma polynomial_smul_apply' [comm_semiring R'] [semiring S'] [algebra R' S']
  [has_smul S' T'] (p : R'[X]) (f : S' → T') (x : S') :
  (p • f) x = aeval x p • f x := rfl

variables [comm_semiring R'] [comm_semiring S'] [comm_semiring T'] [algebra R' S'] [algebra S' T']

/-- This is not an instance for the same reasons as `polynomial.has_smul_pi'`. -/
noncomputable def polynomial.algebra_pi :
  algebra (R'[X]) (S' → T') :=
{ to_fun := λ p z, algebra_map S' T' (aeval z p),
  map_one' := funext $ λ z, by simp only [polynomial.aeval_one, pi.one_apply, map_one],
  map_mul' := λ f g, funext $ λ z, by simp only [pi.mul_apply, map_mul],
  map_zero' := funext $ λ z, by simp only [polynomial.aeval_zero, pi.zero_apply, map_zero],
  map_add' := λ f g, funext $ λ z, by simp only [polynomial.aeval_add, pi.add_apply, map_add],
  commutes' := λ p f, funext $ λ z, mul_comm _ _,
  smul_def' := λ p f, funext $ λ z, by
    simp only [algebra.algebra_map_eq_smul_one, polynomial_smul_apply', one_mul,
      pi.mul_apply, algebra.smul_mul_assoc],
  ..polynomial.has_smul_pi' R' S' T' }

local attribute [instance] polynomial.algebra_pi

@[simp] lemma polynomial.algebra_map_pi_eq_aeval :
  (algebra_map (R'[X]) (S' → T') : R'[X] → (S' → T')) =
    λ p z, algebra_map _ _ (aeval z p) := rfl

@[simp] lemma polynomial.algebra_map_pi_self_eq_eval :
  (algebra_map (R'[X]) (R' → R') : R'[X] → (R' → R')) = λ p z, eval z p := rfl

end pi
