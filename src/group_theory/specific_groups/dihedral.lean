/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import data.zmod.basic
import group_theory.exponent

/-!
# Dihedral Groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the dihedral groups `dihedral_group n`, with elements `r i` and `sr i` for `i : zmod n`.

For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/

/--
For `n ≠ 0`, `dihedral_group n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `dihedral_group 0` corresponds to the infinite dihedral group.
-/
@[derive decidable_eq]
inductive dihedral_group (n : ℕ) : Type
| r : zmod n → dihedral_group
| sr : zmod n → dihedral_group

namespace dihedral_group

variables {n : ℕ}

/--
Multiplication of the dihedral group.
-/
private def mul : dihedral_group n → dihedral_group n → dihedral_group n
| (r i) (r j) := r (i + j)
| (r i) (sr j) := sr (j - i)
| (sr i) (r j) := sr (i + j)
| (sr i) (sr j) := r (j - i)

/--
The identity `1` is the rotation by `0`.
-/
private def one : dihedral_group n := r 0

instance : inhabited (dihedral_group n) := ⟨one⟩

/--
The inverse of a an element of the dihedral group.
-/
private def inv : dihedral_group n → dihedral_group n
| (r i) := r (-i)
| (sr i) := sr i

/--
The group structure on `dihedral_group n`.
-/
instance : group (dihedral_group n) :=
{ mul := mul,
  mul_assoc :=
  begin
    rintros (a | a) (b | b) (c | c);
    simp only [mul];
    ring,
  end,
  one := one,
  one_mul :=
  begin
    rintros (a | a),
    exact congr_arg r (zero_add a),
    exact congr_arg sr (sub_zero a),
  end,
  mul_one := begin
    rintros (a | a),
    exact congr_arg r (add_zero a),
    exact congr_arg sr (add_zero a),
  end,
  inv := inv,
  mul_left_inv := begin
    rintros (a | a),
    exact congr_arg r (neg_add_self a),
    exact congr_arg r (sub_self a),
  end }

@[simp] lemma r_mul_r (i j : zmod n) : r i * r j = r (i + j) := rfl
@[simp] lemma r_mul_sr (i j : zmod n) : r i * sr j = sr (j - i) := rfl
@[simp] lemma sr_mul_r (i j : zmod n) : sr i * r j = sr (i + j) := rfl
@[simp] lemma sr_mul_sr (i j : zmod n) : sr i * sr j = r (j - i) := rfl

lemma one_def : (1 : dihedral_group n) = r 0 := rfl

private def fintype_helper : (zmod n ⊕ zmod n) ≃ dihedral_group n :=
{ inv_fun := λ i, match i with
                 | (r j) := sum.inl j
                 | (sr j) := sum.inr j
                 end,
  to_fun := λ i, match i with
                 | (sum.inl j) := r j
                 | (sum.inr j) := sr j
                 end,
  left_inv := by rintro (x | x); refl,
  right_inv := by rintro (x | x); refl }

/--
If `0 < n`, then `dihedral_group n` is a finite group.
-/
instance [ne_zero n] : fintype (dihedral_group n) := fintype.of_equiv _ fintype_helper

instance : nontrivial (dihedral_group n) := ⟨⟨r 0, sr 0, dec_trivial⟩⟩

/--
If `0 < n`, then `dihedral_group n` has `2n` elements.
-/
lemma card [ne_zero n] : fintype.card (dihedral_group n) = 2 * n :=
by rw [← fintype.card_eq.mpr ⟨fintype_helper⟩, fintype.card_sum, zmod.card, two_mul]

@[simp] lemma r_one_pow (k : ℕ) : (r 1 : dihedral_group n) ^ k = r k :=
begin
  induction k with k IH,
  { rw nat.cast_zero, refl },
  { rw [pow_succ, IH, r_mul_r],
    congr' 1,
    norm_cast,
    rw nat.one_add }
end

@[simp] lemma r_one_pow_n : (r (1 : zmod n))^n = 1 :=
begin
  rw [r_one_pow, one_def],
  congr' 1,
  exact zmod.nat_cast_self _,
end

@[simp] lemma sr_mul_self (i : zmod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]

/--
If `0 < n`, then `sr i` has order 2.
-/
@[simp] lemma order_of_sr (i : zmod n) : order_of (sr i) = 2 :=
begin
  rw order_of_eq_prime _ _,
  { exact ⟨nat.prime_two⟩ },
  rw [sq, sr_mul_self],
  dec_trivial,
end

/--
If `0 < n`, then `r 1` has order `n`.
-/
@[simp] lemma order_of_r_one : order_of (r 1 : dihedral_group n) = n :=
begin
  rcases eq_zero_or_ne_zero n with rfl | hn,
  { rw order_of_eq_zero_iff',
    intros n hn,
    rw [r_one_pow, one_def],
    apply mt r.inj,
    simpa using hn.ne' },
  { resetI,
    apply (nat.le_of_dvd (ne_zero.pos n) $ order_of_dvd_of_pow_eq_one $ @r_one_pow_n n)
      .lt_or_eq.resolve_left,
    intro h,
    have h1 : (r 1 : dihedral_group n)^(order_of (r 1)) = 1,
    { exact pow_order_of_eq_one _ },
    rw r_one_pow at h1,
    injection h1 with h2,
    rw [← zmod.val_eq_zero, zmod.val_nat_cast, nat.mod_eq_of_lt h] at h2,
    exact absurd h2.symm (order_of_pos _).ne },
end

/--
If `0 < n`, then `i : zmod n` has order `n / gcd n i`.
-/
lemma order_of_r [ne_zero n] (i : zmod n) : order_of (r i) = n / nat.gcd n i.val :=
begin
  conv_lhs { rw ←zmod.nat_cast_zmod_val i },
  rw [←r_one_pow, order_of_pow, order_of_r_one]
end

lemma exponent : monoid.exponent (dihedral_group n) = lcm n 2 :=
begin
  rcases eq_zero_or_ne_zero n with rfl | hn,
  { exact monoid.exponent_eq_zero_of_order_zero order_of_r_one },
  resetI,
  apply nat.dvd_antisymm,
  { apply monoid.exponent_dvd_of_forall_pow_eq_one,
    rintro (m | m),
    { rw [←order_of_dvd_iff_pow_eq_one, order_of_r],
      refine nat.dvd_trans ⟨gcd n m.val, _⟩ (dvd_lcm_left n 2),
      { exact (nat.div_mul_cancel (nat.gcd_dvd_left n m.val)).symm } },
    { rw [←order_of_dvd_iff_pow_eq_one, order_of_sr],
      exact dvd_lcm_right n 2 } },
  { apply lcm_dvd,
    { convert monoid.order_dvd_exponent (r 1),
      exact order_of_r_one.symm },
    { convert monoid.order_dvd_exponent (sr 0),
      exact (order_of_sr 0).symm } }
end

end dihedral_group
