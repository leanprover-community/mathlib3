import ring_theory.adjoin_root
import ring_theory.integral_closure
import field_theory.minimal_polynomial

universe variables u v w

namespace polynomial
variables {α : Type*} {β : Type*} {γ : Type*}

noncomputable theory
open_locale classical

section coeffs
variables [comm_semiring α] (p : polynomial α)

def nonzero_coeffs : finset α := p.support.image p.coeff

lemma mem_nonzero_coeffs (i : ℕ) (hi : p.coeff i ≠ 0) : p.coeff i ∈ p.nonzero_coeffs :=
finset.mem_image.mpr ⟨i, finsupp.mem_support_iff.mpr hi, rfl⟩

def coeffs : finset α := p.nonzero_coeffs ∪ {0}

lemma mem_coeffs (i : ℕ) : p.coeff i ∈ p.coeffs :=
if hi : p.coeff i = 0
then finset.mem_union_right _ (by simp [hi])
else finset.mem_union_left  _ $ mem_nonzero_coeffs p i hi

end coeffs

section
variables [decidable_eq α] [comm_semiring α]

lemma coeff_sum' (s : finset β) (f : β → polynomial α) (n : ℕ) :
  coeff (s.sum f) n = s.sum (λ x, coeff (f x) n) :=
(@finset.sum_hom _ _ _ s f _ _ (λ q, coeff q n) _).symm

end

section injective
open function
variables [decidable_eq α] [decidable_eq β] [comm_semiring α] [comm_semiring β]
variables {f : α → β} [is_semiring_hom f]

lemma map_injective (hf : function.injective f) :
  function.injective (map f : polynomial α → polynomial β) :=
λ p q h, ext $ λ m, hf $
begin
  rw ext_iff at h,
  specialize h m,
  rw [coeff_map f, coeff_map f] at h,
  exact h
end

lemma leading_coeff_of_injective (hf : injective f) (p : polynomial α) :
  leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  delta leading_coeff,
  rw [coeff_map f, nat_degree_map' p hf]
end

lemma monic_of_injective (hf : injective f) {p : polynomial α} (hp : (p.map f).monic) : p.monic :=
begin
  apply hf,
  rw [← leading_coeff_of_injective hf, hp.leading_coeff, is_semiring_hom.map_one f]
end

end injective
section lift
open function
variables [decidable_eq α] [comm_ring α] (s : set α) [is_subring s]
variables (p : polynomial α) (hp : ∀ i, p.coeff i ∈ s)

def lift : polynomial s :=
(finset.range (p.nat_degree + 1)).sum (λ i, C ⟨(p.coeff i), hp i⟩ * X^i)

lemma map_coe_lift : map coe (p.lift s hp) = p :=
begin
  conv_rhs {rw p.as_sum},
  rw ext_iff, intro n,
  rw [coeff_map, lift, coeff_sum', coeff_sum', ← finset.sum_hom coe],
  all_goals { try {apply_instance} },
  apply finset.sum_congr rfl,
  intros i hi,
  rw [coeff_C_mul, coeff_C_mul, is_ring_hom.map_mul coe, ← coeff_map coe, map_pow coe, map_X coe],
  { refl },
  all_goals { apply_instance }
end

end lift

end polynomial

namespace subalgebra
open polynomial
variables {R : Type*} {A : Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]

lemma zero_mem (S : subalgebra R A) : (0 : A) ∈ S :=
submodule.zero_mem (S : submodule R A)

variables [decidable_eq R] [decidable_eq A]

protected lemma is_integral (S : subalgebra R A) (x : A) (hx : is_integral R x) :
  is_integral S x :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  use p.map (algebra_map S),
  split,
  { exact monic_map _ pmonic },
  { rwa [aeval_def, eval₂_map] }
end

end subalgebra

section subfield
variables {K : Type u} [discrete_field K]
variables (s : set K) [is_subring s]

def subfield_of_inv_mem (h : ∀ x ∈ s, x⁻¹ ∈ s) : discrete_field s :=
{ inv := λ x, ⟨x⁻¹, h x.val x.property⟩,
  zero_ne_one := λ h, zero_ne_one $ congr_arg subtype.val h,
  mul_inv_cancel := λ x hx, subtype.val_injective $ mul_inv_cancel
    $ λ hz, hx $ subtype.val_injective hz,
  inv_mul_cancel := λ x hx, subtype.val_injective $ inv_mul_cancel
    $ λ hz, hx $ subtype.val_injective hz,
  inv_zero := subtype.val_injective $ inv_zero,
  has_decidable_eq := subtype.decidable_eq,
  .. @subtype.comm_ring K _ s _ }

end subfield

namespace subalgebra
open polynomial
variables {K : Type u} {L : Type v} [discrete_field K] [discrete_field L] [algebra K L]

noncomputable def inv_poly (x : L) (hx : is_integral K x) : polynomial K :=
let p := minimal_polynomial hx in
((p - C (p.coeff 0)) /ₘ X) * C (p.coeff 0)⁻¹

variables (L_alg : ∀ x:L, is_integral K x)
include L_alg

instance (E : subalgebra K L) : discrete_field (subtype E.carrier) :=
subfield_of_inv_mem _ $ λ x (hx : x ∈ E), sorry

end subalgebra

namespace algebra
open set polynomial
variables {R : Type*} {A : Type*} {B : Type*}
variables [decidable_eq R] [decidable_eq A] [decidable_eq B]
variables [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B]

def adjoin_singleton_desc (x : A) (hx : is_integral R x)
  (f : R → B) [is_ring_hom f] (y : B) (hy : is_root ((minimal_polynomial hx).map f) y) :
(adjoin R ({x} : set A) : Type _) → B :=
sorry

instance adjoin_singleton_desc.is_ring_hom (x : A) (hx : is_integral R x)
  (f : R → B) [is_ring_hom f] (y : B) (hy : is_root ((minimal_polynomial hx).map f) y) :
  is_ring_hom (adjoin_singleton_desc x hx f y hy) :=
sorry

end algebra

-- namespace subalgebra
-- open set lattice
-- variables {R : Type*} {A : Type*} {B : Type*}
-- variables [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]

-- def Sup.desc (Ss : set (subalgebra R A)) (f : Π S : Ss, (S : subalgebra R A) →ₐ[R] B)
--   (hf : ∀ S₁ S₂ : Ss, ∃ h : (S₁ : subalgebra R A) ≤ S₂, (f S₂) ∘ inclusion h = f S₁) :
--   (Sup Ss : subalgebra R A) →ₐ[R] B :=
-- sorry

-- end subalgebra

open function algebra polynomial
variables {R : Type*} {A : Type*} {B : Type*}
variables [decidable_eq R] [decidable_eq A] [decidable_eq B]
variables [comm_ring R] [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra A B]
variables (A_alg : ∀ x : A, is_integral R x)

include A_alg

set_option class.instance_max_depth 50

lemma is_integral_trans_aux (x : B) {p : polynomial A} (pmonic : monic p) (hp : aeval A B x p = 0)
  (S : set (comap R A B))
  (hS : S = (↑((finset.range (p.nat_degree + 1)).image
    (λ i, to_comap R A B (p.coeff i))) : set (comap R A B))) :
  is_integral (adjoin R S) (comap.to_comap R A B x) :=
begin
  have coeffs_mem : ∀ i, coeff (map (to_comap R A B) p) i ∈ adjoin R S,
  { intro i,
    by_cases hi : i ∈ finset.range (p.nat_degree + 1),
    { apply algebra.subset_adjoin, subst S,
      rw [finset.mem_coe, finset.mem_image, coeff_map],
      exact ⟨i, hi, rfl⟩ },
    { rw [finset.mem_range, not_lt] at hi,
      rw [coeff_map, coeff_eq_zero_of_nat_degree_lt hi, alg_hom.map_zero],
      exact subalgebra.zero_mem _ } },
  let q : polynomial (adjoin R S) := polynomial.lift _ (p.map $ to_comap R A B) coeffs_mem,
  have hq : (q.map (algebra_map (comap R A B))) = (p.map $ to_comap R A B) :=
    map_coe_lift _ (p.map $ to_comap R A B) coeffs_mem,
  use q,
  split,
  { suffices h : (q.map (algebra_map (comap R A B))).monic,
    { refine @monic_of_injective _ _ _ _ _ _ _
        (by exact is_ring_hom.is_semiring_hom _) _ _ h,
      exact subtype.val_injective },
    { erw map_coe_lift, exact monic_map _ pmonic } },
  { convert hp using 1,
    replace hq := congr_arg (eval (comap.to_comap R A B x)) hq,
    convert hq using 1; symmetry, swap,
    exact eval_map _ _,
    refine @eval_map _ _ _ _ _ _ (by exact is_ring_hom.is_semiring_hom _) _ },
end

lemma is_integral_trans (x : B) (hx : is_integral A x) :
  is_integral R (comap.to_comap R A B x) :=
begin
  rcases hx with ⟨p, pmonic, hp⟩,
  let S : set (comap R A B) :=
    (↑((finset.range (p.nat_degree + 1)).image
      (λ i, to_comap R A B (p.coeff i))) : set (comap R A B)),
  refine is_integral_of_mem_of_fg (adjoin R (S ∪ {comap.to_comap R A B x})) _ _ _,
  swap, { apply subset_adjoin, simp },
  apply fg_trans,
  { apply fg_adjoin_of_finite, { apply finset.finite_to_set },
    intros x hx,
    rw [finset.mem_coe, finset.mem_image] at hx,
    rcases hx with ⟨i, hi, rfl⟩,
    rcases A_alg (p.coeff i) with ⟨q, qmonic, hq⟩,
    use [q, qmonic],
    replace hq := congr_arg (to_comap R A B : A → (comap R A B)) hq,
    rw alg_hom.map_zero at hq,
    convert hq using 1,
    symmetry, exact polynomial.hom_eval₂ _ _ _ _ },
  { apply fg_adjoin_singleton_of_integral,
    exact is_integral_trans_aux A_alg _ pmonic hp _ rfl }
end
.

lemma algebraic_trans (B_alg : ∀ x : B, is_integral A x) :
  ∀ x : comap R A B, is_integral R x :=
λ x, is_integral_trans A_alg x (B_alg x)
