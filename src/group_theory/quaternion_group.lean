/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer (heavily based on `dihedral` by Shing Tak Lam)
-/
import data.zmod.basic
import group_theory.order_of_element
import data.nat.basic
import tactic.interval_cases
import group_theory.dihedral

/-!
# Quaternion Groups

We define the (generalised) quaternion groups `quaternion_group n` of order `4n`, also known as
dicyclic groups, with elements `a i` and `xa i` for `i : zmod n`.

## Main definition

`quaternion_group n`: The (generalised) quaternion group of order `4n`.

## Implementation notes

In mathematics, the name `quaternion_group` is reserved for the cases `n ≥ 2`. Since it would be
inconvenient to carry around this condition we define `quaternion_group` also for `n = 0` and
`n = 1`. `quaternion_group 0` is isomorphic to the infinite dihedral group, while
`quaternion_group 1` is isomorphic to a cyclic group of order `4`.

## References

https://en.wikipedia.org/wiki/Dicyclic_group
https://en.wikipedia.org/wiki/Quaternion_group

## TODO

Show that `quaternion_group 2 ≃* units (quaternion ℤ)`.

-/

/--
The (generalised) quaternion group `quaternion_group n` of order `4n`. It can be defined by the
presentation `⟨a, x | a²ⁿ = 1, x² = aⁿ, x⁻¹ax=a⁻¹⟩`. We write `a i` for `aⁱ` and `xa i` for `xaⁱ`.
-/
@[derive decidable_eq]
inductive quaternion_group (n : ℕ) : Type
| a : zmod (2 * n) → quaternion_group
| xa : zmod (2 * n) → quaternion_group

namespace quaternion_group

variables {n : ℕ}

/--
Multiplication of the dihedral group.
-/
private def mul : quaternion_group n → quaternion_group n → quaternion_group n
| (a i) (a j) := a (i + j)
| (a i) (xa j) := xa (j - i)
| (xa i) (a j) := xa (i + j)
| (xa i) (xa j) := a (n + j - i)

/--
The identity `1` is given by `aⁱ`.
-/
private def one : quaternion_group n := a 0

instance : inhabited (quaternion_group n) := ⟨one⟩

/--
The inverse of an element of the dihedral group.
-/
private def inv : quaternion_group n → quaternion_group n
| (a i) := a (-i)
| (xa i) := xa (n + i)

/--
The group structure on `quaternion_group n`.
-/
instance : group (quaternion_group n) :=
{ mul := mul,
  mul_assoc :=
  begin
    rintros (i | i) (j | j) (k | k);
    simp only [mul];
    abel,
    simp only [neg_mul_eq_neg_mul_symm, one_mul, int.cast_one, gsmul_eq_mul, int.cast_neg, add_right_inj],
    calc -(n : zmod (2 * n)) = 0 - n : by rw zero_sub
      ... = 2 * n - n : by { norm_cast, simp, }
      ... = n : by ring
  end,
  one := one,
  one_mul :=
  begin
    rintros (i | i),
    exact congr_arg a (zero_add i),
    exact congr_arg xa (sub_zero i),
  end,
  mul_one := begin
    rintros (i | i),
    exact congr_arg a (add_zero i),
    exact congr_arg xa (add_zero i),
  end,
  inv := inv,
  mul_left_inv := begin
    rintros (i | i),
    exact congr_arg a (neg_add_self i),
    exact congr_arg a (sub_self (n + i)),
  end }

variable {n}

@[simp] lemma a_mul_a (i j : zmod (2 * n)) : a i * a j = a (i + j) := rfl
@[simp] lemma a_mul_xa (i j : zmod (2 * n)) : a i * xa j = xa (j - i) := rfl
@[simp] lemma xa_mul_a (i j : zmod (2 * n)) : xa i * a j = xa (i + j) := rfl
@[simp] lemma xa_mul_xa (i j : zmod (2 * n)) : xa i * xa j = a (n + j - i) := rfl

lemma one_def : (1 : quaternion_group n) = a 0 := rfl

private def fintype_helper : (zmod (2 * n) ⊕ zmod (2 * n)) ≃ quaternion_group n :=
{ inv_fun := λ i, match i with
                 | (a j) := sum.inl j
                 | (xa j) := sum.inr j
                 end,
  to_fun := λ i, match i with
                 | (sum.inl j) := a j
                 | (sum.inr j) := xa j
                 end,
  left_inv := by rintro (x | x); refl,
  right_inv := by rintro (x | x); refl }

/-- The special case that more or less by definition `quaternion_group 0` is isomorphic to the
infinite dihedral group. -/
def quaternion_group_zero_equiv_dihedral_zero : quaternion_group 0 ≃* dihedral 0 :=
{ to_fun := λ i, quaternion_group.rec_on i dihedral.r dihedral.sr,
  inv_fun := λ i, match i with
                | (dihedral.r j) := a j
                | (dihedral.sr j) := xa j
                end,
  left_inv := by rintro (k | k); refl,
  right_inv := by rintro (k | k); refl,
  map_mul' := by { rintros (k | k) (l | l); { dsimp, simp, }, } }

/-- Some of the lemmas on `zmod m` require that `m` is positive, as `m = 2 * n` is the case relevant
in this file but we don't want to write `[fact (0 < 2 * n)]` we make this lemma a local instance. -/
private lemma two_mul_pos_of_pos [fact (0 < n)] : fact (0 < 2 * n) :=
begin
rw ← zero_mul 0,
          apply mul_lt_mul',
            { exact zero_le 2 },
            { assumption },
            { exact zero_le 0 },
            { exact nat.zero_lt_succ 1 }
end

local attribute [instance] two_mul_pos_of_pos

/--
If `0 < n`, then `quaternion_group n` is a finite group.
-/
instance [fact (0 < n)] : fintype (quaternion_group n) := fintype.of_equiv _ fintype_helper

instance : nontrivial (quaternion_group n) := ⟨⟨a 0, xa 0, dec_trivial⟩⟩

/--
If `0 < n`, then `quaternion_group n` has `4n` elements.
-/
lemma card [fact (0 < n)] : fintype.card (quaternion_group n) = 4 * n :=
begin
  rw ← fintype.card_eq.mpr ⟨fintype_helper⟩,
  change fintype.card (zmod (2 * n) ⊕ zmod (2 * n)) = 4 * n,
  rw [fintype.card_sum, zmod.card, two_mul],
  ring
end

@[simp] lemma a_one_pow (k : ℕ) : (a 1 : quaternion_group n) ^ k = a k :=
begin
  induction k with k IH,
  { refl },
  { rw [pow_succ, IH, a_mul_a],
    congr' 1,
    norm_cast,
    rw nat.one_add }
end

@[simp] lemma a_one_pow_n : (a 1 : quaternion_group n)^(2 * n) = 1 :=
begin
  cases n,
  { simp_rw [mul_zero, pow_zero] },
  { rw [a_one_pow, one_def],
    congr' 1,
    exact zmod.nat_cast_self _ }
end

@[simp] lemma xa_pow_two (i : zmod (2 * n)) : xa i ^ 2 = a n :=
begin
  simp [pow_two]
end

@[simp] lemma xa_pow_four (i : zmod (2 * n)) : xa i ^ 4 = 1 :=
begin
  simp only [pow_succ, pow_two, xa_mul_xa, xa_mul_a, add_sub_cancel, add_sub_assoc, add_sub_cancel',
             sub_self, add_zero],
  norm_cast,
  rw ← two_mul,
  simp [one_def],
end

/--
If `0 < n`, then `xa i` has order 4.
-/
@[simp] lemma order_of_xa [fact (0 < n)] (i : zmod (2 * n)) : order_of (xa i) = 4 :=
begin
  have h : order_of (xa i) ≤ 4 := order_of_le_of_pow_eq_one (by norm_num) (xa_pow_four i),
  interval_cases (order_of (xa i)) with hcas,
  { -- Show that order_of (xa i) is not 0.
    exfalso,
    have hpos : order_of (xa i) > 0 := order_of_pos (xa i),
    linarith },
  { -- Show that order_of (xa i) is not 1.
    exfalso,
    rw order_of_eq_one_iff at hcas,
    injection hcas },
  { -- Show that order_of (xa i) is not 2.
    exfalso,
    have hcontra : (xa i) ^ 2 = 1,
      { rw ← hcas,
        exact pow_order_of_eq_one _ },
    simp at hcontra,
    injection hcontra with hcontra',
    apply_fun zmod.val at hcontra',
    apply_fun ( / n) at hcontra',
    simp only [zmod.val_nat_cast, zmod.val_zero, nat.zero_div, nat.mod_mul_left_div_self,
               nat.div_self (_inst_1)] at hcontra',
    norm_num at hcontra' },
  { -- Show that order_of (xa i) is not 3.
    exfalso,
    have : order_of (xa i) ∣ 4,
      { apply order_of_dvd_of_pow_eq_one,
        simp },
    rw hcas at this,
    norm_num at this, },
  { -- `order_of (xa i) = 4` is the only possibility left.
    assumption
  }
end

/-- In the special case `n = 1`, `quaternion 1` is a cyclic group (of order `4`).-/
lemma quaternion_group_one_is_cyclic : is_cyclic (quaternion_group 1) :=
begin
  apply is_cyclic_of_order_of_eq_card,
  rw [card, mul_one],
  exact order_of_xa 0
end

/--
If `0 < n`, then `a 1` has order `2 * n`.
-/
@[simp] lemma order_of_a_one [fact (0 < n)] : order_of (a 1 : quaternion_group n) = 2 * n :=
begin
  cases lt_or_eq_of_le (nat.le_of_dvd (two_mul_pos_of_pos)
    (order_of_dvd_of_pow_eq_one (@a_one_pow_n n))) with h h,
  { have h1 : (a 1 : quaternion_group n)^(order_of (a 1)) = 1,
    { exact pow_order_of_eq_one _ },
    rw a_one_pow at h1,
    injection h1 with h2,
    rw [← zmod.val_eq_zero, zmod.val_nat_cast, nat.mod_eq_of_lt h] at h2,
    exact absurd h2.symm (ne_of_lt (order_of_pos _)) },
  { exact h }
end

/--
If `0 < n`, then `a i` has order `n / gcd n i`
-/
lemma order_of_a [fact (0 < n)] (i : zmod (2 * n)) :
  order_of (a i) = (2 * n) / nat.gcd (2 * n) i.val :=
begin
  conv_lhs { rw ← zmod.nat_cast_zmod_val i },
  rw [← a_one_pow, order_of_pow, order_of_a_one]
end

end quaternion_group
