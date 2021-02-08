/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.zmod.basic
import ring_theory.subsemiring
/-!
Reference:
https://
leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology

-/

namespace counterexample

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
/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable the two elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
but `(3,0)` and `(3,1)` are incomparable.
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


@[simp] lemma mem_zmod_2 (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  cases a with a1 h1,
  rw [nat.add_def, add_zero] at h1,
  cases h1 with h1 h1,
  { exact or.inr (by simpa only) },
  { refine or.inl _,
    congr,
    rw nat.le_zero_iff.mp (nat.lt_succ_iff.mp (nat.succ_le_iff.mp h1)) }
end

lemma le_def (a b : ℕ × zmod 2) : a ≤ b ↔ (a : ℕ × zmod 2) ≤ b := by refl

lemma le_def_1 (a b : ℕ × zmod 2) : a ≤ b ↔ ( a = b ∨ a.1 < b.1 ) := by refl


lemma le_of_le {a b : ℕ × zmod 2} (h : a ≤ b) : a.1 ≤ b.1 :=
begin
  rcases h with ⟨rfl, h⟩,
  { exact rfl.le },
  { exact h.le }
end

/-- A strict inequality forces the first components to be different. -/
@[simp] lemma lt_def {a b : ℕ × zmod 2} : a < b ↔ a.1 < b.1 :=
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

/--
instance po_Z2 : partial_order (zmod 2) :=
begin
  refine {le := (λ a b, a = 0 ∨ b = 1),
 lt := λ (a b : zmod 2), begin
 exact (a = 0 ∨ b = 1) ∧ ¬(a = 0 ∨ b = 1),
 end ,
 le_refl := by dec_trivial,
 le_trans := by dec_trivial,
 lt_iff_le_not_le := begin

  refine λ a b, ⟨λ h, _, λ h, _⟩,
  { rcases mem_zmod_2 a with rfl | rfl,
    rcases mem_zmod_2 b with rfl | rfl,
    exact ((and_not_self _).mp h).elim,
    repeat{ exact dec_trivial },
    rcases mem_zmod_2 b with rfl | rfl,
    exact ((and_not_self _).mp h).elim,
    exact ((and_not_self _).mp h).elim},
  {
    rcases mem_zmod_2 a with rfl | rfl,
    rcases mem_zmod_2 b with rfl | rfl,
    exfalso,exact (and_not_self _).mp h,
    cases h,
    cases h_left,
    injections_and_clear,
    simp at h_right,

  }
  --refine ⟨_, _⟩,library_search,

 end,
 le_antisymm := _}
end

instance ocsN2 : ordered_comm_semiring (zmod 2) :=
begin
  refine {add := (+),
 add_assoc := _,
 zero := 0,
 zero_add := _,
 add_zero := _,
 add_comm := _,
 mul := _,
 mul_assoc := _,
 one := 1,
 one_mul := _,
 mul_one := _,
 zero_mul := _,
 mul_zero := _,
 left_distrib := _,
 right_distrib := _,
 add_left_cancel := _,
 add_right_cancel := _,
 le := (λ a b, a = 0 ∨ b = 1),
 lt := λ (a b : zmod 2), a ≤ b ∧ ¬b ≤ a,
 le_refl := _,
 le_trans := _,
 lt_iff_le_not_le := _,
 le_antisymm := _,
 add_le_add_left := _,
 le_of_add_le_add_left := _,
 zero_le_one := _,
 mul_lt_mul_of_pos_left := _,
 mul_lt_mul_of_pos_right := _,
 mul_comm := _},
end
-/

lemma mul_lt_mul_of_pos_left : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → c * a < c * b :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def.mp ab))

lemma mul_lt_mul_of_pos_right : ∀ (a b c : ℕ × zmod 2), a < b → 0 < c → a * c < b * c :=
λ a b c ab c0, lt_def.mpr ((mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def.mp ab))

instance ocsN2 : ordered_comm_semiring (ℕ × zmod 2) :=
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := mul_add,
  right_distrib := add_mul,
  add_left_cancel := λ a b c h, (add_right_inj a).mp h,
  add_right_cancel := λ a b c h, (add_left_inj b).mp h,
  le := (≤),
  lt := λ (a b : ℕ × zmod 2), a ≤ b ∧ ¬b ≤ a,
  le_refl := λ _, le_rfl,
  le_trans := λ _ _ _, le_trans,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  le_antisymm := λ _ _, antisymm,
  add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_le_one := zero_le_one,
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  mul_comm := mul_comm }


/-- A slightly different example. -/
@[derive [comm_semiring]]
def L : Type := subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2))

instance inhabited_L : inhabited L := ⟨0⟩

/-- `L` is a subtype of `ℕ × ℤ/2ℤ`. -/
instance : has_coe L (ℕ × zmod 2) := ⟨λ x, x.1⟩

lemma coe_add_val (a b : L) : (a + b).val = a.val + b.val := rfl

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

instance ocsL : ordered_comm_semiring (ℕ × zmod 2) := by apply_instance


/-
instance : preorder L :=
{ le := λ x y, ( x = y ∨ (x : ℕ × zmod 2) < y ),
  le_refl := λ a, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _),
    { exact yz },
    { rcases yz with (rfl | _),
      { exact or.inr xy},
      { exact or.inr (xy.trans yz) } }
  end }
-/

--@[simp] lemma le_def_L (a b : L) : a ≤ b ↔ ( a = b ∨ a.1 < b.1 ) := by refl

lemma le_L_iff_le {a b : L} : a ≤ b ↔ a.val ≤ b.val := by refl

lemma le_of_le_L {a b : L} (h : a ≤ b) : a.val.1 ≤ b.val.1 :=
le_of_le (le_L_iff_le.mp h)

@[simp] lemma lt_def_L {a b : L} : a < b ↔ (a : ℕ × zmod 2).1 < (b : ℕ × zmod 2).1 :=
by rw [← lt_def, subtype.coe_lt_coe]

/-- The assumption `0 < a` forbids the second component of `a` to be `1`. -/
@[simp] lemma zero_lt_iff (a : L) : 0 < a ↔ 0 < a.1 :=
by simpa only [lt_def_L, lt_def, prod.fst_zero, subtype.val_eq_coe]

/-- The converse is not true: `(0, 1) ≠ (0, 0)`, however `(0, 0)` and `(0,1)` are incomparable. -/
lemma ne_zero_of_pos {a : L} (a0 : 0 < a) : a ≠ 0 :=
begin
  rw [zero_lt_iff, lt_def, subtype.val_eq_coe] at a0,
  exact ne_of_gt (by simpa only [gt_iff_lt, lt_def, zero_lt_iff])
end

lemma lt_L_coe (a b : L) : a < b ↔ a.val.1 < b.val.1 :=
by rw lt_def_L; simp only [subtype.val_eq_coe]

lemma le_antisymm : ∀ (a b : L), a ≤ b → b ≤ a → a = b :=
λ a b ab ba, le_antisymm ab ba

lemma add_left_cancel_L : ∀ (a b c : L), a + b = a + c → b = c :=
begin
  rintros a ⟨b, hb⟩ ⟨c, hc⟩ h,
  injections_and_clear,
  simpa only [prod.mk.inj_iff, subtype.mk_eq_mk, add_right_inj] using h_1
end

lemma add_right_cancel : ∀ (a b c : L), a + b = c + b → a = c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ b ⟨⟨cn, c2⟩, hc⟩ h,
  injections_and_clear,
  simpa only [prod.mk.inj_iff, subtype.mk_eq_mk, add_left_inj] using h_1
end

lemma add_le_add_left : ∀ (a b : L), a ≤ b → ∀ (c : L), c + a ≤ c + b :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ b ab c,
  rw le_L_iff_le,
  cases ab,
  simp,
  rintros ⟨⟨an, a2⟩, ha⟩ b (rfl | ab) c,
  { refl },
  refine or.inr _,
  rcases b with ⟨⟨bn, b2⟩, hb⟩,
  rcases ab with ⟨(⟨rfl, rfl⟩ | ab2), ab1⟩,
  { push_neg at ab1,
    exact ab1.1.elim rfl },
  { unfold_coes,
    simpa [coe_add_val] }
end

lemma le_of_add_le_add_left : ∀ (a b c : L), a + b ≤ a + c → b ≤ c :=
begin
  rintros a ⟨⟨bn, b2⟩, hb⟩ ⟨⟨cn, c2⟩, hc⟩ (ab | ab),
  { refine or.inl _,
    injection ab with h,
    exact subtype.mk_eq_mk.mpr ((add_right_inj a.val).mp h) },
  { refine or.inr _,
    exact lt_def.mpr ((add_lt_add_iff_left _).mp (lt_def.mp ab)) }
end


lemma mul_lt_mul_of_pos_left : ∀ (a b c : L), a < b → 0 < c → c * a < c * b :=
begin
  rintros a b c ab ⟨(rfl | c0), c0⟩,
  { exact (not_or_distrib.mp c0).1.elim rfl },
  { refine lt_def_L.mpr _,
    exact (mul_lt_mul_left (lt_def.mp c0)).mpr (lt_def_L.mp ab) }
end

lemma mul_lt_mul_of_pos_right : ∀ (a b c : L), a < b → 0 < c → a * c < b * c :=
begin
  rintros a b c ab ⟨(rfl | c0), c0⟩,
  { exact (not_or_distrib.mp c0).1.elim rfl },
  { refine lt_def_L.mpr _,
    exact (mul_lt_mul_right (lt_def.mp c0)).mpr (lt_def_L.mp ab) }
end

/-- The unit of multiplication of `L`. -/
def has_one : L := 1

instance ocs : ordered_comm_semiring L :=
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul := (*),
  mul_assoc := mul_assoc,
  one := has_one,
  one_mul := one_mul,
  mul_one := mul_one,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := mul_add,
  right_distrib := add_mul,
  add_left_cancel := add_left_cancel,
  add_right_cancel := add_right_cancel,
  le := (≤),
  lt := λ (a b : L), a ≤ b ∧ ¬b ≤ a,
  le_refl := λ _, le_rfl,
  le_trans := λ _ _ _, le_trans,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  le_antisymm := le_antisymm,
  add_le_add_left := add_le_add_left,
  le_of_add_le_add_left := le_of_add_le_add_left,
  zero_le_one := or.inr (lt_def.mpr zero_lt_one),
  mul_lt_mul_of_pos_left := mul_lt_mul_of_pos_left,
  mul_lt_mul_of_pos_right := mul_lt_mul_of_pos_right,
  mul_comm := mul_comm }

lemma lt_of_add_lt_add_left : ∀ (a b c : L), a + b < a + c → b < c :=
begin
  rintros a ⟨⟨bn, b2⟩, hb⟩ ⟨⟨cn, c2⟩, hc⟩ h,
  rw [lt_def_L] at ⊢ h,
  exact (add_lt_add_iff_left a.val.1).mp h,
end

lemma lt_of_add_lt_add_right : ∀ (a b c : L), a + b < c + b → a < c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ b ⟨⟨cn, c2⟩, hc⟩ h,
  rw [lt_def_L] at ⊢ h,
  exact (add_lt_add_iff_right b.val.1).mp h,
end

@[simp] lemma mul_one_val {a b : ℕ × zmod 2}
  (ha : (a = (1,0) ∨ a = (1,1))) (hb : (b = (1,0) ∨ b = (1,1))) :
  a * b = (1,0) ∨ a * b = (1,1) :=
begin
  rcases ha with rfl | rfl;
  { rcases hb with rfl | rfl;
    simp }
end

@[simp] lemma list_prod_one {l : list (ℕ × zmod 2)}
  (l1 : ∀ (e : (ℕ × zmod 2)), e ∈ l → (e = (1,0) ∨ e = (1,1))) :
  l.prod = (1, 0) ∨ l.prod = (1, 1) :=
begin
  revert l1,
  induction l,
  { exact λ l1, or.inr list.prod_nil },
  { intros l1,
    rw [list.prod_cons],
    refine mul_one_val _ _,
    { exact l1 l_hd (list.mem_cons_self l_hd l_tl) },
    { exact l_ih (λ e he, l1 _ (list.mem_cons_of_mem l_hd he)) } }
end

@[simp] lemma list_prod_one_val {l : list (ℕ × zmod 2)}
  (l1 : ∀ (e : (ℕ × zmod 2)), e ∈ l → (e = (1,0) ∨ e = (1,1))) :
  l.prod.1 = 1 :=
begin
  cases list_prod_one l1 with h1 h1;
  exact (congr_arg prod.fst h1).trans rfl,
end

lemma zu_not_mem_L :
  (⟨0, 1⟩ : ℕ × zmod 2) ∉ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
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
  ((1, 0) : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
begin
  rintros _ ⟨H, _, rfl⟩,
  rintros _ ⟨(H1 : ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) ⊆ H), _, rfl⟩,
  refine set.mem_of_mem_of_subset _ H1,
  exact or.inl rfl
end

lemma one_one_mem_L :
  ((1, 1) : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
begin
  rintros _ ⟨H, _, rfl⟩,
  rintros _ ⟨(H1 : ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) ⊆ H), _, rfl⟩,
  refine set.mem_of_mem_of_subset _ H1,
  exact or.inr rfl
end

lemma add_one_zero (n : ℕ) : ((n.succ, 0) : ℕ × zmod 2) = (n, 0) + (1, 0) := rfl

lemma add_one_one (n : ℕ) : ((n.succ, 1) : ℕ × zmod 2) = (n, 1) + (1, 0) := rfl

lemma nat_zero_mem_L (l : ℕ × zmod 2) (l0 : l.2 = 0) :
  l ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
begin
  rcases l with ⟨n, n2⟩,
  change n2 = 0 at l0,
  subst l0,
  induction n with n hi,
  { exact (subsemiring.closure {(1, 0), (1, 1)}).zero_mem },
  rw add_one_zero,
  refine subsemiring.add_mem _ hi one_zero_mem_L
end

lemma nat_succ_mem_L (l0 : ℕ) :
  ((l0.succ, 1) : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
begin
  induction l0 with n hi,
  { exact one_one_mem_L },
  { rw add_one_one,
    exact subsemiring.add_mem _ hi one_zero_mem_L }
end

lemma nat_one_mem_L (l : ℕ × zmod 2) (l0 : l.1 ≠ 0) (l1 : l.2 = 1) :
  l ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
begin
  rcases l with ⟨l, l2⟩,
  dsimp at l0 l1,
  subst l1,
  rw (nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr l0)).symm,
  exact nat_succ_mem_L l.pred,
end

@[simp] lemma not_mem_L_iff {l : ℕ × zmod 2} :
  l ∉ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) ↔ l = (⟨0, 1⟩ : ℕ × zmod 2) :=
begin
  refine ⟨λ h, _, _⟩,
  { rcases l with ⟨n, n2⟩,
    obtain F := mem_zmod_2 n2,
    rcases F with rfl | rfl,
    { refine (h _).elim,
      exact nat_zero_mem_L (n, 0) rfl },
    { by_contra k,
      rw [prod.mk.inj_iff, eq_self_iff_true, and_true] at k,
      refine h (nat_one_mem_L (n, 1) k rfl) } },
  { rintro rfl,
    exact zu_not_mem_L }
end

lemma mem_L_iff_ne {l : ℕ × zmod 2} :
  l ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) ↔ l ≠ (0, 1) :=
by rw [ne.def, ← not_mem_L_iff, not_not]

lemma bot_le : ∀ (a : L), 0 ≤ a :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩,
  by_cases a0 : an ≠ 0,
  { refine or.inr _,
    exact lt_def.mpr (nat.pos_of_ne_zero a0) },
  { rw not_not at a0,
    refine or.inl _,
    subst a0,
    rcases mem_zmod_2 a2 with (rfl | rfl),
    { refl, },
    { exact (mem_L_iff_ne.mp ha rfl).elim } }
end

lemma add_self_zmod_2 (a : zmod 2) : a + a = 0 :=
begin
  rcases mem_zmod_2 a with rfl | rfl;
  refl,
end

lemma le_iff_exists_add : ∀ (a b : L), a ≤ b ↔ ∃ (c : L), b = a + c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ ⟨⟨bn, b2⟩, hb⟩,
  rw [le_def_L, lt_def, subtype.mk_eq_mk, prod.mk.inj_iff],
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
      { rw [add_zero, add_zero],
        exact ⟨rfl, rfl⟩ },
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
{ add := (+),
  add_assoc := add_assoc,
  zero := 0,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  le := (≤),
  lt := λ (a b : L), a ≤ b ∧ ¬b ≤ a,
  le_refl := λ _, le_rfl,
  le_trans := λ _ _ _, le_trans,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  le_antisymm := le_antisymm,
  add_le_add_left := add_le_add_left,
  lt_of_add_lt_add_left := lt_of_add_lt_add_left,
  bot := 0,
  bot_le := bot_le,
  le_iff_exists_add := le_iff_exists_add,
  mul := (*),
  mul_assoc := mul_assoc,
  one := 1,
  one_mul := one_mul,
  mul_one := mul_one,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  left_distrib := mul_add,
  right_distrib := add_mul,
  mul_comm := mul_comm,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero }

end counterexample
