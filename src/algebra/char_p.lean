/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau, Joey van Langen, Casper Putz

Characteristic of semirings.
-/

import data.padics.padic_norm data.nat.choose data.fintype
import data.zmod.basic algebra.module

universes u v

/-- The generator of the kernel of the unique homomorphism ℤ → α for a semiring α -/
class char_p (α : Type u) [semiring α] (p : ℕ) : Prop :=
(cast_eq_zero_iff : ∀ x:ℕ, (x:α) = 0 ↔ p ∣ x)

theorem char_p.cast_eq_zero (α : Type u) [semiring α] (p : ℕ) [char_p α p] : (p:α) = 0 :=
(char_p.cast_eq_zero_iff α p p).2 (dvd_refl p)

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
  rw [nat.cast_one, mul_one, mul_one, add_left_inj],
  transitivity,
  { refine finset.sum_eq_single 0 _ _,
    { intros b h1 h2,
      have := nat.prime.dvd_choose (nat.pos_of_ne_zero h2) (finset.mem_range.1 h1) hp,
      rw [← nat.div_mul_cancel this, nat.cast_mul, char_p.cast_eq_zero α p],
      simp only [mul_zero] },
    { intro H, exfalso, apply H, exact finset.mem_range.2 hp.pos } },
  rw [pow_zero, nat.sub_zero, one_mul, nat.choose_zero_right, nat.cast_one, mul_one]
end

/-- The frobenius map that sends x to x^p -/
def frobenius (α : Type u) [monoid α] (p : ℕ) (x : α) : α := x^p

theorem frobenius_def (α : Type u) [monoid α] (p : ℕ) (x : α) : frobenius α p x = x ^ p := rfl

theorem frobenius_mul (α : Type u) [comm_monoid α] (p : ℕ) (x y : α) :
  frobenius α p (x * y) = frobenius α p x * frobenius α p y := mul_pow x y p
theorem frobenius_one (α : Type u) [monoid α] (p : ℕ) :
  frobenius α p 1 = 1 := one_pow _

theorem is_monoid_hom.map_frobenius {α : Type u} {β : Type v} [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]
  (p : ℕ) (x : α) : f (frobenius α p x) = frobenius β p (f x) :=
by unfold frobenius; induction p; simp only [pow_zero, pow_succ,
  is_monoid_hom.map_one f, is_monoid_hom.map_mul f, *]

instance {α : Type u} [comm_ring α] (p : ℕ) [hp : nat.prime p] [char_p α p] : is_ring_hom (frobenius α p) :=
{ map_one := frobenius_one α p,
  map_mul := frobenius_mul α p,
  map_add := add_pow_char α hp }

section
variables (α : Type u) [comm_ring α] (p : ℕ) [hp : nat.prime p]
theorem frobenius_zero : frobenius α p 0 = 0 := zero_pow hp.pos
variables [char_p α p] (x y : α)
include hp
theorem frobenius_add : frobenius α p (x + y) = frobenius α p x + frobenius α p y := is_ring_hom.map_add _
theorem frobenius_neg : frobenius α p (-x) = -frobenius α p x := is_ring_hom.map_neg _
theorem frobenius_sub : frobenius α p (x - y) = frobenius α p x - frobenius α p y := is_ring_hom.map_sub _
end

theorem frobenius_inj (α : Type u) [integral_domain α] (p : ℕ) [nat.prime p] [char_p α p] (x y : α)
  (H : frobenius α p x = frobenius α p y) : x = y :=
by rw ← sub_eq_zero at H ⊢; rw ← frobenius_sub at H; exact pow_eq_zero H

theorem frobenius_nat_cast (α : Type u) [comm_ring α] (p : ℕ) [nat.prime p] [char_p α p] (x : ℕ) :
  frobenius α p x = x :=
by induction x; simp only [nat.cast_zero, nat.cast_succ, frobenius_zero, frobenius_one, frobenius_add, *]

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
absurd (@nat.cast_injective α _ _ this) (@set.not_injective_nat_fintype α _ _ _)

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
or.elim (no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero (d : α) e this)
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

theorem char_is_prime [fintype α] (p : ℕ) [char_p α p] : nat.prime p :=
or.resolve_right (char_is_prime_or_zero α p) (char_ne_zero_of_fintype α p)

end integral_domain

end char_p

namespace zmod

variables {α : Type u} [ring α] {n : ℕ+}

instance cast_is_ring_hom [char_p α n] : is_ring_hom (cast : zmod n → α) :=
{ map_one := by rw ←@nat.cast_one α _ _; exact eq.symm (char_p.cast_eq_mod α n 1),
  map_mul := assume x y : zmod n, show ↑((x * y).val) = ↑(x.val) * ↑(y.val),
    by rw [zmod.mul_val, ←char_p.cast_eq_mod, nat.cast_mul],
  map_add := assume x y : zmod n, show ↑((x + y).val) = ↑(x.val) + ↑(y.val),
    by rw [zmod.add_val, ←char_p.cast_eq_mod, nat.cast_add] }

instance to_module [char_p α n] : module (zmod n) α := is_ring_hom.to_module cast

instance to_module' {m : ℕ} {hm : m > 0} [hc : char_p α m] : module (zmod ⟨m, hm⟩) α :=
@zmod.to_module α _ ⟨m, hm⟩ hc

end zmod
