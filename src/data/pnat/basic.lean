/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import data.pnat.defs
import data.nat.bits
import data.nat.order.basic
import data.set.basic
import algebra.group_with_zero.divisibility
import algebra.order.positive.ring

/-!
# The positive natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
It is defined in `data.pnat.defs`, but most of the development is deferred to here so
that `data.pnat.defs` can have very few imports.
-/

attribute [derive [add_left_cancel_semigroup, add_right_cancel_semigroup, add_comm_semigroup,
  linear_ordered_cancel_comm_monoid, has_add, has_mul, distrib]] pnat

namespace pnat

@[simp] lemma one_add_nat_pred (n : ℕ+) : 1 + n.nat_pred = n :=
by rw [nat_pred, add_tsub_cancel_iff_le.mpr $ show 1 ≤ (n : ℕ), from n.2]

@[simp] lemma nat_pred_add_one (n : ℕ+) : n.nat_pred + 1 = n :=
(add_comm _ _).trans n.one_add_nat_pred

@[mono] lemma nat_pred_strict_mono : strict_mono nat_pred := λ m n h, nat.pred_lt_pred m.2.ne' h
@[mono] lemma nat_pred_monotone : monotone nat_pred := nat_pred_strict_mono.monotone
lemma nat_pred_injective : function.injective nat_pred := nat_pred_strict_mono.injective

@[simp] lemma nat_pred_lt_nat_pred {m n : ℕ+} : m.nat_pred < n.nat_pred ↔ m < n :=
nat_pred_strict_mono.lt_iff_lt

@[simp] lemma nat_pred_le_nat_pred {m n : ℕ+} : m.nat_pred ≤ n.nat_pred ↔ m ≤ n :=
nat_pred_strict_mono.le_iff_le

@[simp] lemma nat_pred_inj {m n : ℕ+} : m.nat_pred = n.nat_pred ↔ m = n := nat_pred_injective.eq_iff

end pnat

namespace nat

@[mono] theorem succ_pnat_strict_mono : strict_mono succ_pnat := λ m n, nat.succ_lt_succ

@[mono] theorem succ_pnat_mono : monotone succ_pnat := succ_pnat_strict_mono.monotone

@[simp] theorem succ_pnat_lt_succ_pnat {m n : ℕ} : m.succ_pnat < n.succ_pnat ↔ m < n :=
succ_pnat_strict_mono.lt_iff_lt

@[simp] theorem succ_pnat_le_succ_pnat {m n : ℕ} : m.succ_pnat ≤ n.succ_pnat ↔ m ≤ n :=
succ_pnat_strict_mono.le_iff_le

theorem succ_pnat_injective : function.injective succ_pnat := succ_pnat_strict_mono.injective

@[simp] theorem succ_pnat_inj {n m : ℕ} : succ_pnat n = succ_pnat m ↔ n = m :=
succ_pnat_injective.eq_iff

end nat

namespace pnat

open nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/

@[simp, norm_cast] lemma coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n := set_coe.ext_iff

@[simp, norm_cast] theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n := rfl

/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coe_add_hom : add_hom ℕ+ ℕ :=
{ to_fun := coe,
  map_add' := add_coe }

instance : covariant_class ℕ+ ℕ+ (+) (≤) := positive.covariant_class_add_le
instance : covariant_class ℕ+ ℕ+ (+) (<) := positive.covariant_class_add_lt
instance : contravariant_class ℕ+ ℕ+ (+) (≤) := positive.contravariant_class_add_le
instance : contravariant_class ℕ+ ℕ+ (+) (<) := positive.contravariant_class_add_lt

/-- An equivalence between `ℕ+` and `ℕ` given by `pnat.nat_pred` and `nat.succ_pnat`. -/
@[simps { fully_applied := ff }] def _root_.equiv.pnat_equiv_nat : ℕ+ ≃ ℕ :=
{ to_fun := pnat.nat_pred,
  inv_fun := nat.succ_pnat,
  left_inv := succ_pnat_nat_pred,
  right_inv := nat.nat_pred_succ_pnat }

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps apply { fully_applied := ff }] def _root_.order_iso.pnat_iso_nat : ℕ+ ≃o ℕ :=
{ to_equiv := equiv.pnat_equiv_nat,
  map_rel_iff' := λ _ _, nat_pred_le_nat_pred }

@[simp] lemma _root_.order_iso.pnat_iso_nat_symm_apply :
  ⇑order_iso.pnat_iso_nat.symm = nat.succ_pnat := rfl

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b :=
λ a b, nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b :=
λ a b, nat.add_one_le_iff

instance : order_bot ℕ+ :=
{ bot := 1,
  bot_le := λ a, a.property }

@[simp] lemma bot_eq_one : (⊥ : ℕ+) = 1 := rfl

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp] lemma mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) := rfl
@[simp] lemma mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) := rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp] lemma bit0_le_bit0 (n m : ℕ+) : (bit0 n) ≤ (bit0 m) ↔ (bit0 (n : ℕ)) ≤ (bit0 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit0_le_bit1 (n m : ℕ+) : (bit0 n) ≤ (bit1 m) ↔ (bit0 (n : ℕ)) ≤ (bit1 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit1_le_bit0 (n m : ℕ+) : (bit1 n) ≤ (bit0 m) ↔ (bit1 (n : ℕ)) ≤ (bit0 (m : ℕ)) :=
iff.rfl
@[simp] lemma bit1_le_bit1 (n m : ℕ+) : (bit1 n) ≤ (bit1 m) ↔ (bit1 (n : ℕ)) ≤ (bit1 (m : ℕ)) :=
iff.rfl

@[simp, norm_cast] theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n := rfl

/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coe_monoid_hom : ℕ+ →* ℕ :=
{ to_fun := coe,
  map_one' := one_coe,
  map_mul' := mul_coe }

@[simp] lemma coe_coe_monoid_hom : (coe_monoid_hom : ℕ+ → ℕ) = coe := rfl

@[simp] lemma le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 := le_bot_iff

lemma lt_add_left (n m : ℕ+) : n < m + n := lt_add_of_pos_left _ m.2

lemma lt_add_right (n m : ℕ+) : n < n + m := (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast] lemma coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) := rfl
@[simp, norm_cast] lemma coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) := rfl

@[simp, norm_cast] theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
rfl

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : has_sub ℕ+ := ⟨λ a b, to_pnat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 :=
begin
  change (to_pnat' _ : ℕ) = ite _ _ _,
  split_ifs with h,
  { exact to_pnat'_coe (tsub_pos_of_lt h) },
  { rw tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : ℕ) ≤ b), refl }
end

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b :=
 λ h, eq $ by { rw [add_coe, sub_coe, if_pos h],
                exact add_tsub_cancel_of_le h.le }

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
lemma exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (h1 : n ≠ 1), ∃ (k : ℕ+), n = k + 1
| ⟨1, _⟩ h1 := false.elim $ h1 rfl
| ⟨n+2, _⟩ _ := ⟨⟨n+1, by simp⟩, rfl⟩

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def case_strong_induction_on {p : ℕ+ → Sort*} (a : ℕ+) (hz : p 1)
  (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a :=
begin
  apply strong_induction_on a,
  rintro ⟨k, kprop⟩ hk,
  cases k with k,
  { exact (lt_irrefl 0 kprop).elim },
  cases k with k,
  { exact hz },
  exact hi ⟨k.succ, nat.succ_pos _⟩ (λ m hm, hk _ (lt_succ_iff.2 hm)),
end

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_eliminator]
def rec_on (n : ℕ+) {p : ℕ+ → Sort*} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n :=
begin
  rcases n with ⟨n, h⟩,
  induction n with n IH,
  { exact absurd h dec_trivial },
  { cases n with n,
    { exact p1 },
    { exact hp _ (IH n.succ_pos) } }
end

@[simp] theorem rec_on_one {p} (p1 hp) : @pnat.rec_on 1 p p1 hp = p1 := rfl

@[simp] theorem rec_on_succ (n : ℕ+) {p : ℕ+ → Sort*} (p1 hp) :
  @pnat.rec_on (n + 1) p p1 hp = hp n (@pnat.rec_on n p p1 hp) :=
by { cases n with n h, cases n; [exact absurd h dec_trivial, refl] }

lemma mod_div_aux_spec : ∀ (k : ℕ+) (r q : ℕ) (h : ¬ (r = 0 ∧ q = 0)),
 (((mod_div_aux k r q).1 : ℕ) + k * (mod_div_aux k r q).2 = (r + k * q))
| k 0 0 h := (h ⟨rfl, rfl⟩).elim
| k 0 (q + 1) h := by
{ change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1),
  rw [nat.pred_succ, nat.mul_succ, zero_add, add_comm]}
| k (r + 1) q h := rfl

theorem mod_add_div (m k : ℕ+) : ((mod m k) + k * (div m k) : ℕ) = m :=
begin
  let h₀ := nat.mod_add_div (m : ℕ) (k : ℕ),
  have : ¬ ((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0),
  by { rintro ⟨hr, hq⟩, rw [hr, hq, mul_zero, zero_add] at h₀,
       exact (m.ne_zero h₀.symm).elim },
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this,
  exact (this.trans h₀),
end

theorem div_add_mod (m k : ℕ+) : (k * (div m k) + mod m k : ℕ) = m :=
(add_comm _ _).trans (mod_add_div _ _)

lemma mod_add_div' (m k : ℕ+) : ((mod m k) + (div m k) * k : ℕ) = m :=
by { rw mul_comm, exact mod_add_div _ _ }

lemma div_add_mod' (m k : ℕ+) : ((div m k) * k + mod m k : ℕ) = m :=
by { rw mul_comm, exact div_add_mod _ _ }

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k :=
begin
  change ((mod m k) : ℕ) ≤ (m : ℕ) ∧ ((mod m k) : ℕ) ≤ (k : ℕ),
  rw [mod_coe], split_ifs,
  { have hm : (m : ℕ) > 0 := m.pos,
    rw [← nat.mod_add_div (m : ℕ) (k : ℕ), h, zero_add] at hm ⊢,
    by_cases h' : ((m : ℕ) / (k : ℕ)) = 0,
    { rw [h', mul_zero] at hm, exact (lt_irrefl _ hm).elim},
    { let h' := nat.mul_le_mul_left (k : ℕ)
             (nat.succ_le_of_lt (nat.pos_of_ne_zero h')),
      rw [mul_one] at h', exact ⟨h', le_refl (k : ℕ)⟩ } },
  { exact ⟨nat.mod_le (m : ℕ) (k : ℕ), (nat.mod_lt (m : ℕ) k.pos).le⟩ }
end

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) :=
begin
  split; intro h, rcases h with ⟨_, rfl⟩, apply dvd_mul_right,
  rcases h with ⟨a, h⟩, cases a, { contrapose h, apply ne_zero, },
  use a.succ, apply nat.succ_pos, rw [← coe_inj, h, mul_coe, mk_coe],
end

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k :=
begin
  rw dvd_iff,
  rw [nat.dvd_iff_mod_eq_zero], split,
  { intro h, apply eq, rw [mod_coe, if_pos h] },
  { intro h, by_cases h' : (m : ℕ) % (k : ℕ) = 0,
    { exact h'},
    { replace h : ((mod m k) : ℕ) = (k : ℕ) := congr_arg _ h,
      rw [mod_coe, if_neg h'] at h,
      exact ((nat.mod_lt (m : ℕ) k.pos).ne h).elim } }
end

lemma le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n :=
by { rw dvd_iff', intro h, rw ← h, apply (mod_le n m).left }

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * (div_exact m k) = m :=
begin
 apply eq, rw [mul_coe],
 change (k : ℕ) * (div m k).succ = m,
 rw [← div_add_mod m k, dvd_iff'.mp h, nat.mul_succ]
end

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n :=
λ hmn hnm, (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
 ⟨λ h, dvd_antisymm h (one_dvd n), λ h, h.symm ▸ (dvd_refl 1)⟩

lemma pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a :=
begin
  apply pos_iff_ne_zero.2,
  intro hzero,
  rw hzero at h,
  exact pnat.ne_zero n (eq_zero_of_zero_dvd h)
end

end pnat
