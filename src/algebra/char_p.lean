/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau, Joey van Langen, Casper Putz
-/

import data.fintype.basic
import data.nat.choose
import data.int.modeq
import algebra.module
import algebra.iterate_hom

/-!
# Characteristic of semirings
-/

universes u v

/-- The generator of the kernel of the unique homomorphism ℕ → α for a semiring α -/
class char_p (α : Type u) [semiring α] (p : ℕ) : Prop :=
(cast_eq_zero_iff [] : ∀ x:ℕ, (x:α) = 0 ↔ p ∣ x)

theorem char_p.cast_eq_zero (α : Type u) [semiring α] (p : ℕ) [char_p α p] : (p:α) = 0 :=
(char_p.cast_eq_zero_iff α p p).2 (dvd_refl p)

lemma char_p.int_cast_eq_zero_iff (R : Type u) [ring R] (p : ℕ) [char_p R p] (a : ℤ) :
  (a : R) = 0 ↔ (p:ℤ) ∣ a :=
begin
  rcases lt_trichotomy a 0 with h|rfl|h,
  { rw [← neg_eq_zero, ← int.cast_neg, ← dvd_neg],
    lift -a to ℕ using neg_nonneg.mpr (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] },
  { simp only [int.cast_zero, eq_self_iff_true, dvd_zero] },
  { lift a to ℕ using (le_of_lt h) with b,
    rw [int.cast_coe_nat, char_p.cast_eq_zero_iff R p, int.coe_nat_dvd] }
end

lemma char_p.int_coe_eq_int_coe_iff (R : Type*) [ring R] (p : ℕ) [char_p R p] (a b : ℤ) :
  (a : R) = (b : R) ↔ a ≡ b [ZMOD p] :=
by rw [eq_comm, ←sub_eq_zero, ←int.cast_sub,
       char_p.int_cast_eq_zero_iff R p, int.modeq.modeq_iff_dvd]

theorem char_p.eq (α : Type u) [semiring α] {p q : ℕ} (c1 : char_p α p) (c2 : char_p α q) : p = q :=
nat.dvd_antisymm
  ((char_p.cast_eq_zero_iff α p q).1 (char_p.cast_eq_zero _ _))
  ((char_p.cast_eq_zero_iff α q p).1 (char_p.cast_eq_zero _ _))

instance char_p.of_char_zero (α : Type u) [semiring α] [char_zero α] : char_p α 0 :=
⟨λ x, by rw [zero_dvd_iff, ← nat.cast_zero, nat.cast_inj]⟩

theorem char_p.exists (α : Type u) [semiring α] : ∃ p, char_p α p :=
by letI := classical.dec_eq α; exact
classical.by_cases
  (assume H : ∀ p:ℕ, (p:α) = 0 → p = 0, ⟨0,
    ⟨λ x, by rw [zero_dvd_iff]; exact ⟨H x, by rintro rfl; refl⟩⟩⟩)
  (λ H, ⟨nat.find (classical.not_forall.1 H), ⟨λ x,
    ⟨λ H1, nat.dvd_of_mod_eq_zero (by_contradiction $ λ H2,
      nat.find_min (classical.not_forall.1 H)
        (nat.mod_lt x $ nat.pos_of_ne_zero $ not_of_not_imp $
          nat.find_spec (classical.not_forall.1 H))
        (not_imp_of_and_not ⟨by rwa [← nat.mod_add_div x (nat.find (classical.not_forall.1 H)),
          nat.cast_add, nat.cast_mul, of_not_not (not_not_of_not_imp $ nat.find_spec (classical.not_forall.1 H)),
          zero_mul, add_zero] at H1, H2⟩)),
    λ H1, by rw [← nat.mul_div_cancel' H1, nat.cast_mul,
      of_not_not (not_not_of_not_imp $ nat.find_spec (classical.not_forall.1 H)), zero_mul]⟩⟩⟩)

theorem char_p.exists_unique (α : Type u) [semiring α] : ∃! p, char_p α p :=
let ⟨c, H⟩ := char_p.exists α in ⟨c, H, λ y H2, char_p.eq α H2 H⟩

/-- Noncomuptable function that outputs the unique characteristic of a semiring. -/
noncomputable def ring_char (α : Type u) [semiring α] : ℕ :=
classical.some (char_p.exists_unique α)

theorem ring_char.spec (α : Type u) [semiring α] : ∀ x:ℕ, (x:α) = 0 ↔ ring_char α ∣ x :=
by letI := (classical.some_spec (char_p.exists_unique α)).1;
unfold ring_char; exact char_p.cast_eq_zero_iff α (ring_char α)

theorem ring_char.eq (α : Type u) [semiring α] {p : ℕ} (C : char_p α p) : p = ring_char α :=
(classical.some_spec (char_p.exists_unique α)).2 p C

theorem add_pow_char (α : Type u) [comm_ring α] {p : ℕ} (hp : nat.prime p)
  [char_p α p] (x y : α) : (x + y)^p = x^p + y^p :=
begin
  rw [add_pow, finset.sum_range_succ, nat.sub_self, pow_zero, nat.choose_self],
  rw [nat.cast_one, mul_one, mul_one, add_right_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { intros b h1 h2,
      have := nat.prime.dvd_choose_self (nat.pos_of_ne_zero h2) (finset.mem_range.1 h1) hp,
      rw [← nat.div_mul_cancel this, nat.cast_mul, char_p.cast_eq_zero α p],
      simp only [mul_zero] },
    { intro H, exfalso, apply H, exact finset.mem_range.2 hp.pos } },
  rw [pow_zero, nat.sub_zero, one_mul, nat.choose_zero_right, nat.cast_one, mul_one]
end

lemma eq_iff_modeq_int (R : Type*) [ring R] (p : ℕ) [char_p R p] (a b : ℤ) :
  (a : R) = b ↔ a ≡ b [ZMOD p] :=
by rw [eq_comm, ←sub_eq_zero, ←int.cast_sub,
       char_p.int_cast_eq_zero_iff R p, int.modeq.modeq_iff_dvd]

lemma char_p.neg_one_ne_one (R : Type*) [ring R] (p : ℕ) [char_p R p] [fact (2 < p)] :
  (-1 : R) ≠ (1 : R) :=
begin
  suffices : (2 : R) ≠ 0,
  { symmetry, rw [ne.def, ← sub_eq_zero, sub_neg_eq_add], exact this },
  assume h,
  rw [show (2 : R) = (2 : ℕ), by norm_cast] at h,
  have := (char_p.cast_eq_zero_iff R p 2).mp h,
  have := nat.le_of_dvd dec_trivial this,
  rw fact at *, linarith,
end

section frobenius

variables (R : Type u) [comm_ring R] {S : Type v} [comm_ring S] (f : R →* S) (g : R →+* S)
  (p : ℕ) [fact p.prime] [char_p R p]  [char_p S p] (x y : R)

/-- The frobenius map that sends x to x^p -/
def frobenius : R →+* R :=
{ to_fun := λ x, x^p,
  map_one' := one_pow p,
  map_mul' := λ x y, mul_pow x y p,
  map_zero' := zero_pow (lt_trans zero_lt_one ‹nat.prime p›.one_lt),
  map_add' := add_pow_char R ‹nat.prime p› }

variable {R}

theorem frobenius_def : frobenius R p x = x ^ p := rfl

theorem frobenius_mul : frobenius R p (x * y) = frobenius R p x * frobenius R p y :=
(frobenius R p).map_mul x y

theorem frobenius_one : frobenius R p 1 = 1 := one_pow _

variable {R}

theorem monoid_hom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) :=
f.map_pow x p

theorem ring_hom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) :=
g.map_pow x p

theorem monoid_hom.map_iterate_frobenius (n : ℕ) :
  f (frobenius R p^[n] x) = (frobenius S p^[n] (f x)) :=
function.semiconj.iterate_right (f.map_frobenius p) n x

theorem ring_hom.map_iterate_frobenius (n : ℕ) :
  g (frobenius R p^[n] x) = (frobenius S p^[n] (g x)) :=
g.to_monoid_hom.map_iterate_frobenius p x n

theorem monoid_hom.iterate_map_frobenius (f : R →* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

theorem ring_hom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [fact p.prime] [char_p R p] (n : ℕ) :
  f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
f.iterate_map_pow _ _ _

variable (R)

theorem frobenius_zero : frobenius R p 0 = 0 := (frobenius R p).map_zero

theorem frobenius_add : frobenius R p (x + y) = frobenius R p x + frobenius R p y :=
(frobenius R p).map_add x y

theorem frobenius_neg : frobenius R p (-x) = -frobenius R p x := (frobenius R p).map_neg x

theorem frobenius_sub : frobenius R p (x - y) = frobenius R p x - frobenius R p y :=
(frobenius R p).map_sub x y

theorem frobenius_nat_cast (n : ℕ) : frobenius R p n = n := (frobenius R p).map_nat_cast n

end frobenius

theorem frobenius_inj (α : Type u) [integral_domain α] (p : ℕ) [fact p.prime] [char_p α p] :
  function.injective (frobenius α p) :=
λ x h H, by { rw ← sub_eq_zero at H ⊢, rw ← frobenius_sub at H, exact pow_eq_zero H }

namespace char_p

section
variables (α : Type u) [ring α]

lemma char_p_to_char_zero [char_p α 0] : char_zero α :=
add_group.char_zero_of_inj_zero $
  λ n h0, eq_zero_of_zero_dvd ((cast_eq_zero_iff α 0 n).mp h0)

lemma cast_eq_mod (p : ℕ) [char_p α p] (k : ℕ) : (k : α) = (k % p : ℕ) :=
calc (k : α) = ↑(k % p + p * (k / p)) : by rw [nat.mod_add_div]
         ... = ↑(k % p)               : by simp[cast_eq_zero]

theorem char_ne_zero_of_fintype (p : ℕ) [hc : char_p α p] [fintype α] : p ≠ 0 :=
assume h : p = 0,
have char_zero α := @char_p_to_char_zero α _ (h ▸ hc),
absurd (@nat.cast_injective α _ _ this) (not_injective_infinite_fintype coe)

end

section integral_domain
open nat

variables (α : Type u) [integral_domain α]

theorem char_ne_one (p : ℕ) [hc : char_p α p] : p ≠ 1 :=
assume hp : p = 1,
have ( 1 : α) = 0, by simpa using (cast_eq_zero_iff α p 1).mpr (hp ▸ dvd_refl p),
absurd this one_ne_zero

theorem char_is_prime_of_ge_two (p : ℕ) [hc : char_p α p] (hp : p ≥ 2) : nat.prime p :=
suffices ∀d ∣ p, d = 1 ∨ d = p, from ⟨hp, this⟩,
assume (d : ℕ) (hdvd : ∃ e, p = d * e),
let ⟨e, hmul⟩ := hdvd in
have (p : α) = 0, from (cast_eq_zero_iff α p p).mpr (dvd_refl p),
have (d : α) * e = 0, from (@cast_mul α _ d e) ▸ (hmul ▸ this),
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero this)
  (assume hd : (d : α) = 0,
  have p ∣ d, from (cast_eq_zero_iff α p d).mp hd,
  show d = 1 ∨ d = p, from or.inr (dvd_antisymm ⟨e, hmul⟩ this))
  (assume he : (e : α) = 0,
  have p ∣ e, from (cast_eq_zero_iff α p e).mp he,
  have e ∣ p, from dvd_of_mul_left_eq d (eq.symm hmul),
  have e = p, from dvd_antisymm ‹e ∣ p› ‹p ∣ e›,
  have h₀ : p > 0, from gt_of_ge_of_gt hp (nat.zero_lt_succ 1),
  have d * p = 1 * p, by rw ‹e = p› at hmul; rw [one_mul]; exact eq.symm hmul,
  show d = 1 ∨ d = p, from or.inl (eq_of_mul_eq_mul_right h₀ this))

theorem char_is_prime_or_zero (p : ℕ) [hc : char_p α p] : nat.prime p ∨ p = 0 :=
match p, hc with
| 0,     _  := or.inr rfl
| 1,     hc := absurd (eq.refl (1 : ℕ)) (@char_ne_one α _ (1 : ℕ) hc)
| (m+2), hc := or.inl (@char_is_prime_of_ge_two α _ (m+2) hc (nat.le_add_left 2 m))
end

lemma char_is_prime_of_pos (p : ℕ) [h : fact (0 < p)] [char_p α p] : fact p.prime :=
(char_p.char_is_prime_or_zero α _).resolve_right (nat.pos_iff_ne_zero.1 h)

theorem char_is_prime [fintype α] (p : ℕ) [char_p α p] : p.prime :=
or.resolve_right (char_is_prime_or_zero α p) (char_ne_zero_of_fintype α p)

end integral_domain

section char_one

variables {R : Type*}

section prio
set_option default_priority 100 -- see Note [default priority]

instance [semiring R] [char_p R 1] : subsingleton R :=
subsingleton.intro $
suffices ∀ (r : R), r = 0,
  from assume a b, show a = b, by rw [this a, this b],
assume r,
calc r = 1 * r       : by rw one_mul
   ... = (1 : ℕ) * r : by rw nat.cast_one
   ... = 0 * r       : by rw char_p.cast_eq_zero
   ... = 0           : by rw zero_mul

end prio

lemma false_of_nonzero_of_char_one [semiring R] [nonzero R] [char_p R 1] : false :=
zero_ne_one $ show (0:R) = 1, from subsingleton.elim 0 1

lemma ring_char_ne_one [semiring R] [nonzero R] : ring_char R ≠ 1 :=
by { intros h, apply @zero_ne_one R, symmetry, rw [←nat.cast_one, ring_char.spec, h], }

end char_one

end char_p
