/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import linear_algebra.finite_dimensional
import ring_theory.nilpotent

/-!

# Dedekind finite rings


## References

* Lam, First Course in Noncommutative Ring Theory
* https://ysharifi.wordpress.com/2010/09/17/dedekind-finite-rings/
* The Factorization Theory of Power Monoids - Antoniou,
  https://etd.ohiolink.edu/apexprod/rws_etd/send_file/send?accession=osu1586355818066608&disposition=inline

-/


@[priority 80] -- see Note [lower instance priority]
instance ring.is_noetherian_ring_of_fintype (R) [fintype R] [ring R] :
  is_noetherian_ring R := by rw is_noetherian_ring_iff; refine ring.is_noetherian_of_fintype R R
-- TODO this should be global


-- reduced for poly instance
-- reduced for subrings, sums, pis
-- opposites


/-- A `monoid_with_zero` is reversible if two elements whose product is 0 necessarily still have
product zero when the order of the multiplication is reversed. -/
class is_reversible (R : Type*) [monoid_with_zero R] : Prop :=
(mul_eq_zero_of_mul_swap_eq_zero : ∀ {a b : R}, a * b = 0 → b * a = 0)
-- TODO opposites?
namespace is_reversible
lemma mul_eq_zero_iff_mul_swap_eq_zero {R : Type*} [monoid_with_zero R]
  [is_reversible R] (a b : R) : a * b = 0 ↔ b * a = 0 :=
⟨mul_eq_zero_of_mul_swap_eq_zero, mul_eq_zero_of_mul_swap_eq_zero⟩

end is_reversible
variable (R : Type*)

@[priority 100]
instance no_zero_divisors.is_reversible [monoid_with_zero R] [no_zero_divisors R] :
  is_reversible R := ⟨λ a b h,
begin
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h with rfl | rfl,
  { rw [mul_zero], },
  { rw [zero_mul], },
end⟩

@[priority 100]
instance is_reduced.is_reversible [ring R] [is_reduced R] : is_reversible R := ⟨λ a b h,
begin
  apply is_reduced.eq_zero (b * a),
  use 2,
  rw [pow_two, ← mul_assoc, mul_assoc b, h, mul_zero, zero_mul],
end⟩

@[priority 100]
instance comm_ring.is_reversible [comm_ring R] : is_reversible R :=
⟨λ a b h, h ▸ mul_comm b a⟩


/-- A (noncommutative) monoid is Dedekind-finite if for any pair of elements `a b : R` with
  `a * b = 1` we have `b * a = 1`, i.e. multiplication is commutative on inverse pairs.
  This concept is often studied for rings, but can be defined more generally for monoids, and some
  results hold for monoids without any additive structure.

  This is implemented as a mixin for `monoid R`.  -/
class is_dedekind_finite [monoid R] : Prop :=
(inv_comm : ∀ a b : R, a * b = 1 → b * a = 1)

namespace dedekind_finite

instance {ι : Type*} {α : ι → Type*} [∀ i, monoid $ α i]
  [∀ i, is_dedekind_finite $ α i] : is_dedekind_finite (Π i, α i) :=
by pi_instance

--instance subring.is_dedekind_finite [ring R] [is_dedekind_finite R] (S : set R)
-- [is_subring S] : is_dedekind_finite S :=
--by subtype_instance
variable {R}

lemma left_mul [ring R] {a b : R} (hab : a * b = 1) : a * (1 - b * a) = 0 :=
by rw [mul_sub, ← mul_assoc, hab, mul_one, one_mul, sub_self]
lemma right_mul [ring R] {a b : R} (hab : a * b = 1) : (1 - b * a) * b = 0 :=
by rw [sub_mul, mul_assoc, hab, mul_one, one_mul, sub_self]
lemma idemp [ring R] {a b : R} (hab : a * b = 1) : (1 - b * a) * (1 - b * a) = (1 - b * a) :=
begin
  assoc_rw [sub_mul, mul_sub, mul_sub, hab],
  simp,
end

@[priority 100]
instance is_reversible.is_dedekind_finite [ring R] [is_reversible R] : is_dedekind_finite R :=
⟨λ a b h,
  begin
    have := right_mul h,
    rw [← neg_sub, neg_mul_eq_neg_mul_symm, neg_eq_zero,
      is_reversible.mul_eq_zero_iff_mul_swap_eq_zero, mul_sub, mul_one,
      ← mul_assoc, ← pow_two, sub_eq_zero] at this,
    apply_fun ((*) a) at this,
    rw [h] at this,
    calc b * a = a * (b^2 * a) * b * a : by simp [this]
        ...    = a * b^2 * (a * b) * a : by simp [mul_assoc] -- I feel like ac_refl should do this
        ...    = a * b^2 * a           : by simp [h]
        ...    = 1                     : by assoc_rw [this],
  end⟩

section
open linear_map
open function

-- we have ker_id already but neither seems to be simp normal
@[simp] theorem ker_one {R : Type*} [ring R] {M : Type*} [add_comm_group M] [module R M] :
  ker (1 : M →ₗ[R] M) = ⊥ := rfl
end

-- TODO artinian version of ring stuff?

section

variable [ring R]

open_locale classical

@[priority 100]
instance is_dedekind_finite_of_noetherian [is_noetherian_ring R] : is_dedekind_finite R :=
⟨λ a b h,
  begin
    set f : R →ₗ[R] R := (is_linear_map.is_linear_map_smul' b).mk' _,
    have f_surj : function.surjective f := λ x, ⟨x * a, by simp [mul_assoc, h]⟩,
    rw ← sub_eq_zero,
    apply is_noetherian.injective_of_surjective_endomorphism f f_surj,
    simp [sub_mul, mul_assoc, h],
  end⟩

end

section

variable {R}

lemma pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one [monoid R] {a b : R} (hab : a * b = 1) :
  ∀ (i j : ℕ), a ^ i * b ^ j = b ^ (j - i) * a ^ (i - j)
| 0       0       := by simp
| (i + 1) 0       := by simp
| 0       (j + 1) := by simp
| (i + 1) (j + 1) := begin
  rw [pow_succ', pow_succ],
  assoc_rw hab,
  rw [mul_one, pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one i j,
      nat.succ_sub_succ_eq_sub, nat.succ_sub_succ_eq_sub],
end

private def e [ring R] (a b : R) (i j : ℕ) : R := b ^ i * (1 - b * a) * a ^ j

lemma e_orthogonal [ring R] {a b : R} (hab : a * b = 1) {i j k l : ℕ} :
  e a b i j * e a b k l = if j = k then e a b i l else 0 :=
begin
  rw [e, e, e],
  assoc_rw [pow_mul_pow_eq_pow_sub_mul_pow_sub_of_mul_eq_one hab],
  rcases lt_trichotomy j k with H | rfl | H,
  { rw [if_neg (ne_of_lt H),
        show k - j = k - j - 1 + 1, from (nat.succ_pred_eq_of_pos (tsub_pos_of_lt H)).symm,
        pow_succ],
    assoc_rw right_mul hab,
    simp [H], },
  { simp only [mul_one, if_true, eq_self_iff_true, tsub_self, pow_zero],
    assoc_rw idemp hab, },
  { rw [if_neg (ne_of_gt H),
        show j - k = j - k - 1 + 1, from (nat.succ_pred_eq_of_pos (tsub_pos_of_lt H)).symm,
        pow_succ'],
    assoc_rw left_mul hab,
    simp [H], },
end

lemma e_pow_two_eq_zero_of_ne [ring R] {a b : R} (hab : a * b = 1) {i j : ℕ} (hij : i ≠ j) :
  e a b i j ^ 2 = 0 :=
by rw [pow_two, e_orthogonal hab, if_neg (ne.symm hij)]

open_locale classical

lemma is_dedekind_finite_of_fin_nilpotents [ring R] (h : {x : R | is_nilpotent x}.finite) :
  is_dedekind_finite R :=
⟨begin
  contrapose! h,
  rw [← set.not_infinite, not_not, ← set.infinite_coe_iff],
  rcases h with ⟨a, b, hab, hba⟩,
  refine infinite.of_injective
    (λ n, ⟨e a b (n + 1) 0, 2, e_pow_two_eq_zero_of_ne hab n.succ_ne_zero⟩) _,
  intros n m hnm,
  rw [subtype.mk_eq_mk] at hnm,
  by_contradiction h,
  have : e a b 0 (n + 1) * e a b (m + 1) 0 = 0,
  { rw [e_orthogonal hab, if_neg],
    intro hmn,
    exact h ((add_left_inj 1).mp hmn) },
  apply absurd _ hba.symm,
  rw ← sub_eq_zero,
  calc 1 - b * a
       = e a b 0 0                         : by rw [e, pow_zero, pow_zero, mul_one, one_mul]
  ...  = e a b 0 (n + 1) * e a b (n + 1) 0 : by rw [e_orthogonal hab, if_pos rfl]
  ...  = e a b 0 (n + 1) * e a b (m + 1) 0 : by rw hnm
  ...  = 0                                 : this,
end⟩

end
end dedekind_finite
