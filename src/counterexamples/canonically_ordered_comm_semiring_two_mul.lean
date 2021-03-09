/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.zmod.basic
import ring_theory.subsemiring
import algebra.ordered_monoid
/-!

A `canonically_ordered_comm_semiring` with two different elements `a` and `b` such that
`a ≠ b` and `2 * a = 2 * b`.

Reference:
https://
leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology
-/

namespace from_Bhavik

/--  Bhavik Mehta's example. -/
@[derive [comm_semiring]]
def K : Type := subsemiring.closure ({1.5} : set ℚ)

instance : has_coe K ℚ := ⟨λ x, x.1⟩

instance inhabited_K : inhabited K := ⟨0⟩

instance : preorder K :=
{ le := λ x y, x = y ∨ (x : ℚ) + 1 ≤ (y : ℚ),
  le_refl := λ x, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _), { apply yz },
    rcases yz with (rfl | _), { right, apply xy },
    right,
    exact xy.trans (le_trans ((le_add_iff_nonneg_right _).mpr zero_le_one) yz)
  end }

end from_Bhavik

lemma mem_zmod_2 (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  rcases a with ⟨_ | _ | _ | _ | a_val, _ | ⟨_, _ | ⟨_, ⟨⟩⟩⟩⟩,
  { exact or.inl rfl },
  { exact or.inr rfl },
end

lemma add_self_zmod_2 (a : zmod 2) : a + a = 0 :=
begin
  rcases mem_zmod_2 a with rfl | rfl;
  refl,
end

namespace Nxzmod_2

variables {a b : ℕ × zmod 2}

/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable each pair of elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
whereas, `∀ n ∈ ℤ`, the elements `(n,0)` and `(n,1)` are incomparable.
-/
instance preN2 : partial_order (ℕ × zmod 2) :=
{ le := λ x y, x = y ∨ x.1 < y.1,
  le_refl := λ a, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _),
    { exact yz },
    { rcases yz with (rfl | _),
      { exact or.inr xy},
      { exact or.inr (xy.trans yz) } }
  end,
  le_antisymm := begin
    intros a b ab ba,
    cases ab with ab ab,
    { exact ab },
    { cases ba with ba ba,
      { exact ba.symm },
      { exact (nat.lt_asymm ab ba).elim } }
  end }

instance csrN2 : comm_semiring (ℕ × zmod 2) := by apply_instance

instance csrN2_1 : add_cancel_comm_monoid (ℕ × zmod 2) :=
{ add_left_cancel := λ a b c h, (add_right_inj a).mp h,
  add_right_cancel := λ a b c h, (add_left_inj b).mp h,
  ..Nxzmod_2.csrN2 }

/-- A strict inequality forces the first components to be different. -/
@[simp] lemma lt_def : a < b ↔ a.1 < b.1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨(rfl | a1), h1⟩,
    { exact ((not_or_distrib.mp h1).1).elim rfl },
    { exact a1 } },
  refine ⟨or.inr h, not_or_distrib.mpr ⟨λ k, _, not_lt.mpr h.le⟩⟩,
  rw k at h,
  exact nat.lt_asymm h h
end

lemma add_left_cancel : ∀ (a b c : ℕ × zmod 2), a + b = a + c → b = c :=
λ a b c h, (add_right_inj a).mp h

lemma add_le_add_left : ∀ (a b : ℕ × zmod 2), a ≤ b → ∀ (c : ℕ × zmod 2), c + a ≤ c + b :=
begin
  rintros a b (rfl | ab) c,
  { refl },
  { exact or.inr (by simpa) }
end

lemma le_of_add_le_add_left : ∀ (a b c : ℕ × zmod 2), a + b ≤ a + c → b ≤ c :=
begin
  rintros a b c (bc | bc),
  { exact le_of_eq ((add_right_inj a).mp bc) },
  { exact or.inr (by simpa using bc) }
end

lemma zero_le_one : (0 : ℕ × zmod 2) ≤ 1 := dec_trivial

lemma mul_lt_mul_of_pos_left : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → c * a < c * b :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def.mp ab))

lemma mul_lt_mul_of_pos_right : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → a * c < b * c :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def.mp ab))

instance ocsN2 : ordered_comm_semiring (ℕ × zmod 2) :=
{ add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_le_one := zero_le_one,
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  ..Nxzmod_2.csrN2_1,
  ..(infer_instance : partial_order (ℕ × zmod 2)),
  ..(infer_instance : comm_semiring (ℕ × zmod 2)) }

end Nxzmod_2

/-- Pullback an `ordered_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid {α β : Type*} [ordered_comm_monoid α]
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c,
    show f (c * a) ≤ f (c * b), by simp [mul, mul_le_mul_left' ab],
  lt_of_mul_lt_mul_left :=
    λ a b c bc, @lt_of_mul_lt_mul_left' _ _ (f a) _ _ (by rwa [← mul, ← mul]),
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map. -/
@[to_additive function.injective.ordered_cancel_add_comm_monoid
"Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.ordered_cancel_comm_monoid {α β : Type*} [ordered_cancel_comm_monoid α]
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ x y z (xy : f (x * y) ≤ f (x * z)),
    (by { rw [mul, mul] at xy, exact le_of_mul_le_mul_left' xy }),
  ..hf.left_cancel_semigroup f mul,
  ..hf.right_cancel_semigroup f mul,
  ..hf.ordered_comm_monoid f one mul }

/-- Pullback an `ordered_semiring` under an injective map. -/
def function.injective.ordered_semiring {α β : Type*} [ordered_semiring α]
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_semiring β :=
{ zero_le_one := show f 0 ≤ f 1, by  simp only [zero, one, zero_le_one],
  mul_lt_mul_of_pos_left := λ  a b c ab c0, show f (c * a) < f (c * b),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_left ab _,
      rwa ← zero,
    end,
  mul_lt_mul_of_pos_right := λ a b c ab c0, show f (a * c) < f (b * c),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_right ab _,
      rwa ← zero,
    end,
  ..hf.ordered_cancel_add_comm_monoid f zero add,
  ..hf.semiring f zero one add mul }

/-- Pullback an `ordered_comm_semiring` under an injective map. -/
def function.injective.ordered_comm_semiring {α β : Type*} [ordered_comm_semiring α]
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_semiring β :=
{ ..hf.comm_semiring f zero one add mul,
  ..hf.ordered_semiring f zero one add mul }

namespace ex_L

open Nxzmod_2 subtype

def L_1 : Type := { l : (ℕ × zmod 2) // l ≠ (0, 1) }

instance zero : has_zero L_1 := ⟨⟨(0, 0), dec_trivial⟩⟩

instance one : has_one L_1 := ⟨⟨(1, 1), dec_trivial⟩⟩

instance : inhabited L_1 := ⟨1⟩

lemma add_L_1 {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
  a + b ≠ (0, 1) :=
begin
  rcases a with ⟨a, a2⟩,
  rcases b with ⟨b, b2⟩,
  cases b,
  { rcases mem_zmod_2 b2 with rfl | rfl,
    { simp [ha] },
    { simpa only } },
  { simp [(a + b).succ_ne_zero] }
end

lemma mul_L_1 {a b : ℕ × zmod 2} (ha : a ≠ (0, 1)) (hb : b ≠ (0, 1)) :
  a * b ≠ (0, 1) :=
begin
  rcases a with ⟨a, a2⟩,
  rcases b with ⟨b, b2⟩,
  cases b,
  { rcases mem_zmod_2 b2 with rfl | rfl;
    rcases mem_zmod_2 a2 with rfl | rfl;
    -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
    -- it does not finish the proof and on that goal it asks to prove `false`
    simp,
    exact hb rfl },
  cases a,
  { rcases mem_zmod_2 b2 with rfl | rfl;
    rcases mem_zmod_2 a2 with rfl | rfl;
    -- while this looks like a non-terminal `simp`, it (almost) isn't: there is only one goal where
    -- it does not finish the proof and on that goal it asks to prove `false`
    simp,
    exact ha rfl },
  { simp [mul_ne_zero _ _, nat.succ_ne_zero _] }
end

instance has_add_L_1 : has_add L_1 :=
{ add := λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨a + b, add_L_1 ha hb⟩ }

instance : has_mul L_1 :=
{ mul := λ ⟨a, ha⟩ ⟨b, hb⟩, ⟨a * b, mul_L_1 ha hb⟩ }

instance : ordered_comm_semiring L_1 :=
begin
  refine function.injective.ordered_comm_semiring _ subtype.coe_injective rfl rfl _ _;
  { refine λ x y, _,
    cases x,
    cases y,
    refl }
end

lemma bot_le : ∀ (a : L_1), 0 ≤ a :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩,
  cases an,
  { rcases mem_zmod_2 a2 with (rfl | rfl),
    { refl, },
    { exact (ha rfl).elim } },
  { refine or.inr _,
    exact nat.succ_pos _ }
end

instance order_bot : order_bot L_1 :=
{ bot := 0,
  bot_le := bot_le,
  ..(infer_instance : partial_order L_1) }

lemma lt_of_add_lt_add_left : ∀ (a b c : L_1), a + b < a + c → b < c :=
λ (a : L_1) {b c : L_1}, (add_lt_add_iff_left a).mp

lemma le_iff_exists_add : ∀ (a b : L_1), a ≤ b ↔ ∃ (c : L_1), b = a + c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ ⟨⟨bn, b2⟩, hb⟩,
  rw subtype.mk_le_mk,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨rfl, rfl⟩ | h,
    { exact ⟨(0 : L_1), (add_zero _).symm⟩ },
    { refine ⟨⟨⟨bn - an, b2 + a2⟩, _⟩, _⟩,
      { rw [ne.def, prod.mk.inj_iff, not_and_distrib],
        exact or.inl (ne_of_gt (nat.sub_pos_of_lt h)) },
      { congr,
        { exact (nat.add_sub_cancel' h.le).symm },
        { change b2 = a2 + (b2 + a2),
          rw [add_comm b2, ← add_assoc, add_self_zmod_2, zero_add] } } } },
  { rcases h with ⟨⟨⟨c, c2⟩, hc⟩, abc⟩,
    injection abc with abc,
    rw [prod.mk_add_mk, prod.mk.inj_iff] at abc,
    rcases abc with ⟨rfl, rfl⟩,
    cases c,
    { refine or.inl _,
      rw [ne.def, prod.mk.inj_iff, eq_self_iff_true, true_and] at hc,
      rcases mem_zmod_2 c2 with rfl | rfl,
      { rw [add_zero, add_zero] },
      { exact (hc rfl).elim } },
    { refine or.inr _,
      exact (lt_add_iff_pos_right _).mpr c.succ_pos } }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : L_1), a * b = 0 → a = 0 ∨ b = 0 :=
begin
  rintros ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1,
  injection ab1 with ab,
  injection ab with abn ab2,
  rw mul_eq_zero at abn,
  rcases abn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { refine or.inl _,
    rcases mem_zmod_2 a2 with rfl | rfl,
    { refl },
    { exact (ha rfl).elim } },
  { refine or.inr _,
    rcases mem_zmod_2 b2 with rfl | rfl,
    { refl },
    { exact (hb rfl).elim } }
end

instance can : canonically_ordered_comm_semiring L_1 :=
{ lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  le_iff_exists_add := le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  ..(infer_instance : order_bot L_1),
  ..(infer_instance : ordered_comm_semiring L_1) }

lemma one_eq : (1 : ℕ × zmod 2).2 = 1 := rfl

lemma one_eq_L_1 : (1 : L_1).1.2 = 1 := rfl

/--
The elements `(1,0)` and `(1,1)` of `L_1` are different, but their doubles coincide.
-/
example : ∃ a b : L_1, a ≠ b ∧ 2 * a = 2 * b :=
begin
  refine ⟨⟨(1,0), by simp⟩, 1, λ (h : (⟨(1, 0), _⟩ : L_1) = ⟨⟨1, 1⟩, _⟩), _, rfl⟩,
  obtain (F : (0 : zmod 2) = 1) := congr_arg (λ j : L_1, j.1.2) h,
  cases F,
end

#exit

lemma mul_one_val {a b : ℕ × zmod 2}
  (ha : (a = (1, 0) ∨ a = (1, 1))) (hb : (b = (1, 0) ∨ b = (1, 1))) :
  a * b = (1, 0) ∨ a * b = (1, 1) :=
by rcases ha with rfl | rfl; { rcases hb with rfl | rfl; simp }

instance can : canonically_ordered_comm_semiring L_1 :=
{ lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  le_iff_exists_add := le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  ..(infer_instance : order_bot L),
  ..(infer_instance : ordered_comm_semiring L_1) }


/-- A slightly different example. -/
@[derive [comm_semiring]]
def L : Type := subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2))

variables {a b : L}

instance inhabited_L : inhabited L := ⟨0⟩

/-- `L` is a subtype of `ℕ × ℤ/2ℤ`. -/
instance : has_coe L (ℕ × zmod 2) := ⟨λ x, x.1⟩

instance : partial_order L :=
{ le := λ x y, (x : ℕ × zmod 2) ≤ y,
  le_refl := λ a, or.inl rfl,
  le_trans := λ x y z xy yz, xy.trans yz,
  le_antisymm := λ a b ab ba, begin
    cases ab with ab ab,
    { exact subtype.ext ab },
    { cases ba with ba ba,
      { exact (subtype.ext ba).symm },
      { exact (nat.lt_asymm ab ba).elim } }
  end }

lemma add_left_cancel : ∀ (a b c : L), a + b = a + c → b = c :=
begin
  rintros a ⟨b, hb⟩ ⟨c, hc⟩ abc,
  rw [mk_eq_mk],
  refine add_left_cancel a _ _ _,
  injection abc,
end

lemma add_right_cancel : ∀ (a b c : L), a + b = c + b → a = c :=
begin
  rintros ⟨a, ha⟩ b ⟨c, hc⟩ abc,
  rw [mk_eq_mk],
  apply add_right_cancel,
  injection abc,
end

lemma add_le_add_left : ∀ (a b : L), a ≤ b → ∀ (c : L), c + a ≤ c + b :=
λ a b ab c, coe_le_coe.mp (add_le_add_left _ _ (coe_le_coe.mp ab) _)

lemma le_of_add_le_add_left : ∀ (a b c : L), a + b ≤ a + c → b ≤ c :=
λ a b c bc, coe_le_coe.mp (le_of_add_le_add_left _ _ _ (coe_le_coe.mp bc))

lemma mul_lt_mul_of_pos_left : ∀ (a b c : L), a < b → 0 < c → c * a < c * b :=
λ a b c ab c0, coe_lt_coe.mp (mul_lt_mul_of_pos_left _ _ _ (coe_lt_coe.mpr ab) (coe_lt_coe.mpr c0))

lemma mul_lt_mul_of_pos_right : ∀ (a b c : L), a < b → 0 < c → a * c < b * c :=
λ a b c ab c0, coe_lt_coe.mp (mul_lt_mul_of_pos_right _ _ _ (coe_lt_coe.mpr ab) (coe_lt_coe.mpr c0))

instance ocsL : ordered_comm_semiring L :=
{ add_left_cancel := add_left_cancel,
  add_right_cancel := add_right_cancel,
  add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_le_one := zero_le_one,
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  ..(infer_instance : partial_order L),
  ..(infer_instance : comm_semiring L) }

lemma lt_of_add_lt_add_left : ∀ (a b c : L), a + b < a + c → b < c :=
λ (a : L) {b c : L}, (add_lt_add_iff_left a).mp

@[simp] lemma list_prod_one {l : list (ℕ × zmod 2)}
  (l1 : ∀ (e : (ℕ × zmod 2)), e ∈ l → (e = (1, 0))) :
  l.prod = (1, 0) ∨ l.prod = (1, 1) :=
begin
  revert l1,
  induction l,
  { exact λ l1, or.inr list.prod_nil },
  { intros l1,
    rw [list.prod_cons],
    refine mul_one_val (or.inl _) _,
    { exact l1 l_hd (list.mem_cons_self l_hd l_tl) },
    { exact l_ih (λ e he, l1 _ (list.mem_cons_of_mem l_hd he)) } }
end

@[simp] lemma list_prod_one_val {l : list (ℕ × zmod 2)}
  (l1 : ∀ (e : (ℕ × zmod 2)), e ∈ l → (e = (1, 0))) :
  l.prod.1 = 1 :=
begin
  cases list_prod_one l1 with h1 h1;
  exact (congr_arg prod.fst h1).trans rfl,
end

lemma zero_one_not_mem :
  (⟨0, 1⟩ : ℕ × zmod 2) ∉ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) :=
begin
  intros ha,
  obtain ⟨li, c, F⟩ := subsemiring.mem_closure_iff_exists_list.mp ha,
  induction li with li li2 ili,
  { injection F with h1 h2,
    cases h2 },
  { rw [list.map, list.sum_cons] at F,
    have : (li.prod).1 + (list.map list.prod li2).sum.1 = 0 := (congr_arg prod.fst F).trans rfl,
    have nuo : li.prod.1 = 1,
    { cases li,
      { simp only [list.prod_nil, prod.fst_one] },
      { refine list_prod_one_val _,
        exact c (li_hd :: li_tl) (list.mem_cons_self (li_hd :: li_tl) li2) } },
    refine (0 : ℕ).not_succ_le_zero _,
    refine (le_add_right _).trans this.le,
    exact le_of_eq nuo.symm }
end

lemma one_zero_mem_L :
  ((1, 0) : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) :=
begin
  refine (subsemiring.mem_closure).mpr (λ S hS, _),
  apply set.mem_of_mem_of_subset (set.mem_singleton ((1, 0) : ℕ × zmod 2)) hS
end

lemma succ_eq_add_one_zero (n : ℕ) (a : zmod 2) : ((n.succ, a) : ℕ × zmod 2) = (n, a) + (1, 0) :=
by rw [prod.mk_add_mk, fin.add_zero]

lemma nat_zero_mem_L (l : ℕ × zmod 2) (l0 : l.2 = 0) :
  l ∈ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) :=
begin
  rcases l with ⟨n, n2⟩,
  change n2 = 0 at l0,
  subst l0,
  induction n with n hi,
  { exact (subsemiring.closure {(1, 0)}).zero_mem },
  { rw succ_eq_add_one_zero,
    refine subsemiring.add_mem _ hi one_zero_mem_L }
end

lemma nat_succ_mem_L (l0 : ℕ) :
  ((l0.succ, 1) : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) :=
begin
  induction l0 with n hi,
  { exact subsemiring.one_mem _ },
  { rw succ_eq_add_one_zero,
    exact subsemiring.add_mem _ hi one_zero_mem_L }
end

lemma nat_one_mem_L (l : ℕ × zmod 2) (l0 : l.1 ≠ 0) (l1 : l.2 = 1) :
  l ∈ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) :=
begin
  rcases l with ⟨l, l2⟩,
  dsimp at l0 l1,
  subst l1,
  rw ← (nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr l0)),
  exact nat_succ_mem_L l.pred,
end

@[simp] lemma not_mem_L_iff {l : ℕ × zmod 2} :
  l ∉ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) ↔ l = (⟨0, 1⟩ : ℕ × zmod 2) :=
begin
  refine ⟨λ h, _, _⟩,
  { rcases l with ⟨n, n2⟩,
    rcases mem_zmod_2 n2 with rfl | rfl,
    { refine (h _).elim,
      exact nat_zero_mem_L (n, 0) rfl },
    { by_contra k,
      rw [prod.mk.inj_iff, eq_self_iff_true, and_true] at k,
      refine h (nat_one_mem_L (n, 1) k rfl) } },
  { rintro rfl,
    exact zero_one_not_mem }
end

lemma mem_L_iff_ne {l : ℕ × zmod 2} :
  l ∈ subsemiring.closure ({(1, 0)} : set (ℕ × zmod 2)) ↔ l ≠ (0, 1) :=
by rw [ne.def, ← not_mem_L_iff, not_not]

lemma bot_le : ∀ (a : L), 0 ≤ a :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩,
  by_cases a0 : an ≠ 0,
  { refine or.inr _,
    exact nat.pos_of_ne_zero a0 },
  { rw not_not at a0,
    subst a0,
    rcases mem_zmod_2 a2 with (rfl | rfl),
    { refl, },
    { exact (mem_L_iff_ne.mp ha rfl).elim } }
end

instance order_bot : order_bot L :=
{ bot := 0,
  bot_le := bot_le,
  ..(infer_instance : partial_order L) }

lemma le_iff_exists_add : ∀ (a b : L), a ≤ b ↔ ∃ (c : L), b = a + c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ ⟨⟨bn, b2⟩, hb⟩,
  rw subtype.mk_le_mk,
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨rfl, rfl⟩ | h,
    { exact ⟨(0 : L), (add_zero _).symm⟩ },
    { refine ⟨⟨⟨bn - an, b2 + a2⟩, mem_L_iff_ne.mpr _⟩, _⟩,
      { rw [ne.def, prod.mk.inj_iff, not_and_distrib],
        exact or.inl (ne_of_gt (nat.sub_pos_of_lt h)) },
      { congr,
        { exact (nat.add_sub_cancel' h.le).symm },
        { change b2 = a2 + (b2 + a2),
          rw [add_comm b2, ← add_assoc, add_self_zmod_2, zero_add] } } } },
  { rcases h with ⟨⟨⟨c, c2⟩, hc⟩, abc⟩,
    injection abc with abc,
    rw [prod.mk_add_mk, prod.mk.inj_iff] at abc,
    rcases abc with ⟨rfl, rfl⟩,
    cases c,
    { refine or.inl _,
      rw [mem_L_iff_ne, ne.def, prod.mk.inj_iff, eq_self_iff_true, true_and] at hc,
      rcases mem_zmod_2 c2 with rfl | rfl,
      { rw [add_zero, add_zero] },
      { exact (hc rfl).elim } },
    { refine or.inr _,
      exact (lt_add_iff_pos_right _).mpr c.succ_pos } }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : L), a * b = 0 → a = 0 ∨ b = 0 :=
begin
  rintros ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1,
  injection ab1 with ab,
  injection ab with abn ab2,
  rw mul_eq_zero at abn,
  rcases abn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { refine or.inl _,
    rcases mem_zmod_2 a2 with rfl | rfl,
    { refl },
    { exact ((mem_L_iff_ne.mp ha) rfl).elim } },
  { refine or.inr _,
    rcases mem_zmod_2 b2 with rfl | rfl,
    { refl },
    { exact ((mem_L_iff_ne.mp hb) rfl).elim } }
end

instance can : canonically_ordered_comm_semiring L :=
{ lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  le_iff_exists_add := le_iff_exists_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  ..(infer_instance : order_bot L),
  ..(infer_instance : ordered_comm_semiring L) }

/--
The elements `(1,0)` and `(1,1)` of `L` are different, but their doubles coincide.
-/
example : ∃ a b : L, a ≠ b ∧ 2 * a = 2 * b :=
⟨⟨_, one_zero_mem_L⟩, ⟨_, subsemiring.one_mem _⟩, by simp, rfl⟩

end ex_L
