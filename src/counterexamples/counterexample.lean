/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.char_zero
import data.real.basic
import data.zmod.basic
import ring_theory.subsemiring
import tactic
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

instance : preorder K :=
{ le := λ x y, x = y ∨ (x : ℚ) + 1 ≤ (y : ℚ),
  le_refl := λ x, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _), { apply yz },
    rcases yz with (rfl | _), { right, apply xy },
    right,
    linarith
  end }

/-- A slightly different example. -/
@[derive [comm_semiring]]
def L : Type := subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2))

--lemma ssr : ((L : set (ℕ × zmod 2)) : subsemiring (ℕ × zmod 2)) :=
/-- The preorder relation on `ℕ × ℤ/2ℤ` where we only compare the first coordinate,
except that we leave incomparable the two elements with the same first component.
For instance, `∀ α, β ∈ ℤ/2ℤ`, the inequality `(1,α) ≤ (2,β)` holds,
but `(3,0)` and `(3,1)` are incomparable.
-/
instance : preorder (ℕ × zmod 2) :=
{ le := λ x y, ( x = y ∨ x.1 < y.1 ),
  le_refl := λ a, or.inl rfl,
  le_trans := λ x y z xy yz,
  begin
    rcases xy with (rfl | _),
    { exact yz },
    { rcases yz with (rfl | _),
      { exact or.inr xy},
      { exact or.inr (xy.trans yz) } }
  end }

/-- `L` is a subtype of `ℕ × ℤ/2ℤ`. -/
instance : has_coe L (ℕ × zmod 2) := ⟨λ x, x.1⟩

@[simp] lemma coe_add (a b : L) : ((a + b) : ℕ × zmod 2) = a.val + b.val := rfl

@[simp] lemma coe_add_u (a b : L) : ((a + b) : ℕ × zmod 2) = (a : ℕ × zmod 2) + (b : ℕ × zmod 2) := rfl

@[simp] lemma coe_add_val (a b : L) : (a + b).val = a.val + b.val := rfl

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

@[simp] lemma mem_zmod_2 (a : zmod 2) : a = 0 ∨ a = 1 :=
begin
  cases a with a1 h1,
  rw [nat.add_def, add_zero] at h1,
  cases h1 with h1 h1,
  { exact or.inr (by simpa only) },
  { have : a1 = 0 := nat.le_zero_iff.mp (nat.lt_succ_iff.mp (nat.succ_le_iff.mp h1)),
    simp_rw this,
    exact or.inl fin.mk_zero }
end

@[simp] lemma sec_comp (a : ℕ × zmod 2) : a.2 = 0 ∨ a.2 = 1 :=
by simp only [mem_zmod_2]

@[simp] lemma le_def (a b : ℕ × zmod 2) : a ≤ b ↔ ( a = b ∨ a.1 < b.1 ) := by refl

@[simp] lemma le_def_L (a b : L) : a ≤ b ↔ ( a = b ∨ a.1 < b.1 ) := by refl

lemma le_of_le {a b : ℕ × zmod 2} (h : a ≤ b) : a.1 ≤ b.1 :=
begin
  rcases h with ⟨rfl, h⟩,
  { exact rfl.le },
  { exact h.le }
end

lemma le_of_le_L {a b : L} (h : a ≤ b) : a.val.1 ≤ b.val.1 :=
begin
  rcases h with ⟨rfl, h⟩,
  { exact rfl.le },
  { exact le_of_le h.le }
end

/-- A strict inequality forces the first components to be different. -/
@[simp] lemma lt_def (a b : ℕ × zmod 2) : a < b ↔ a.1 < b.1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨(rfl | a1), h1⟩,
    { exact ((not_or_distrib.mp h1).1).elim rfl },
    { exact a1 } },
  refine ⟨or.inr h, not_or_distrib.mpr ⟨λ k, _, not_lt.mpr h.le⟩⟩,
  subst k,
  exact nat.lt_asymm h h
end

@[simp] lemma lt_def_L (a b : L) : a < b ↔ (a : ℕ × zmod 2).1 < (b : ℕ × zmod 2).1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨(rfl | a1), h1⟩,
    { exact ((not_or_distrib.mp h1).1).elim rfl },
    { exact (lt_def a b).mp a1 } },
  refine ⟨or.inr ((lt_def a b).mpr h), not_or_distrib.mpr ⟨λ k, _, _⟩⟩,
  subst k,
  exact nat.lt_asymm h h,
  simp only [not_lt, lt_def],
  exact h.le
end

/-- The assumption `0 < a` forbids the second component of `a` to be `1`. -/
@[simp] lemma zero_lt_iff (a : L) : 0 < a ↔ 0 < a.1 :=
by simpa only [lt_def_L, lt_def, prod.fst_zero, subtype.val_eq_coe]

/-- The converse is not true: `(0, 1) ≠ (0, 0)`, however `(0, 0)` and `(0,1)` are incomparable. -/
lemma ne_zero_of_pos {a : L} (a0 : 0 < a) : a ≠ 0 :=
begin
  rw [zero_lt_iff, lt_def, subtype.val_eq_coe] at a0,
  exact ne_of_gt (by simpa only [gt_iff_lt, lt_def, zero_lt_iff])
end

@[simp] lemma sec_comp_L (a : L) : (a : ℕ × zmod 2).2 = 0 ∨ (a : ℕ × zmod 2).2 = 1 :=
sec_comp _

lemma lt_L_coe (a b : L) : a < b ↔ a.val.1 < b.val.1 :=
by rw lt_def_L; simp only [subtype.val_eq_coe]

lemma le_antisymm : ∀ (a b : L), a ≤ b → b ≤ a → a = b :=
begin
  rintros a b (rfl | ab) ba,
  { refl },
  { exact (not_le.mpr ((lt_def _ _).mp ab)).elim (le_of_le_L ba) }
end

lemma add_left_cancel : ∀ (a b c : L), a + b = a + c → b = c :=
begin
  rintros a ⟨⟨bn, b2⟩, hb⟩ ⟨⟨cn, c2⟩, hc⟩ h,
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
  rintros a b (rfl | ab) c,
  { refl },
  refine or.inr _,
  rcases a with ⟨⟨an, a2⟩, ha⟩,
  rcases b with ⟨⟨bn, b2⟩, hb⟩,
  rcases ab with ⟨(⟨rfl, rfl⟩ | ab2), ab1⟩,
  { push_neg at ab1,
    exact ab1.1.elim rfl },
  { unfold_coes,
    simpa }
end

lemma le_of_add_le_add_left : ∀ (a b c : L), a + b ≤ a + c → b ≤ c :=
begin
  rintros a ⟨⟨bn, b2⟩, hb⟩ ⟨⟨cn, c2⟩, hc⟩ (ab | ab),
  { refine or.inl _,
    injection ab with h,
    exact subtype.mk_eq_mk.mpr ((add_right_inj a.val).mp h) },
  { refine or.inr _,
    exact (lt_def _ _).mpr ((add_lt_add_iff_left _).mp ((lt_def _ _).mp ab)) }
end


lemma mul_lt_mul_of_pos_left : ∀ (a b c : L), a < b → 0 < c → c * a < c * b :=
begin
  intros a b c ab c0,
  rcases c0 with (rfl | c0),
  { exact (not_or_distrib.mp c0_right).1.elim rfl },
  { refine (lt_def_L _ _).mpr _,
    exact (mul_lt_mul_left ((lt_def _ _).mp c0)).mpr ((lt_def_L a b).mp ab) }
end

lemma mul_lt_mul_of_pos_right : ∀ (a b c : L), a < b → 0 < c → a * c < b * c :=
begin
  intros a b c ab c0,
  rcases c0 with (rfl | c0),
  { exact (not_or_distrib.mp c0_right).1.elim rfl },
  { refine (lt_def_L _ _).mpr _,
    exact (mul_lt_mul_right ((lt_def _ _).mp c0)).mpr ((lt_def_L a b).mp ab) }
end

/-- The unit of multiplication of `L`. -/
def has_one : L :=
begin
  refine ⟨(1, 1), _⟩,
  rintros _ ⟨H1, rfl⟩,
  rintros _ ⟨H2, rfl⟩,
  refine set.mem_of_mem_of_subset _ H2,
  exact set.mem_union_right _ rfl
end

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
  zero_le_one := or.inr ((lt_def _ _).mpr zero_lt_one),
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

lemma add_proj (a b : ℕ × zmod 2) : (a + b).1 = a.1 + b.1 := rfl

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


lemma zu_not_mem : (⟨0, 1⟩ : ℕ × zmod 2) ∉ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  rintros ⟨⟨⟨an, a2⟩, ha⟩, h⟩,
  rcases mem_zmod_2 a2 with (rfl | rfl),
  { simpa using h },
  dsimp at *,
  simp at *,
  induction h,
  obtain ⟨li, c, F⟩ := subsemiring.mem_closure_iff_exists_list.mp ha,
  induction li with li li2 ili,
  { injection F with h1 h2,
    cases h2 },
  { simp at F,
    have : (li.prod).1 + (list.map list.prod li2).sum.1 = 0,
    { rw ← add_proj,
      exact (congr_arg prod.fst F).trans rfl },
    have nuo : li.prod.1 = 1,
    { cases li,
      simp only [list.prod_nil, prod.fst_one],
      apply list_prod_one_val,
      exact c (li_hd :: li_tl) (list.mem_cons_self (li_hd :: li_tl) li2) },
    refine ili (λ t ht y yt, _) _;
    { exfalso,
      finish } }
end

lemma add_one_zero (n : ℕ) : ((n.succ, 0) : ℕ × zmod 2) = (n, 0) + (1, 0) := rfl

lemma add_one_one (n : ℕ) : ((n.succ, 1) : ℕ × zmod 2) = (n, 1) + (1, 0) := rfl


lemma L_mem_n_zero (l : ℕ × zmod 2) (l0 : l.2 = 0) :
  l ∈ --subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
  {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  rcases l with ⟨n, n2⟩,
  simp only at l0,
  subst l0,
  induction n with n hi,
  { exact ⟨0, rfl⟩ },
  simp,
  refine ⟨⟨(n.succ, 0), _⟩, _⟩,
  rw add_one_zero,
  refine subsemiring.add_mem _ _ _,
  { rintros _ ⟨H, _, rfl⟩,
    rintros _ ⟨H, _, rfl⟩,
    dsimp at *,
    rcases hi with ⟨⟨⟨n, n2, np2⟩, hip⟩, hiw⟩,
    simp only [prod.mk.inj_iff, subtype.coe_mk] at hiw,
    rcases hiw with ⟨rfl, hiw⟩,
    rw ← hiw at hip,
    exact subsemiring.mem_closure.mp hip _ H_1 },
  { rintros _ ⟨H, _, rfl⟩,
    rintros _ ⟨H, _, rfl⟩,
    dsimp at *,
    refine set.mem_of_mem_of_subset _ H_1,
    exact or.inl rfl },
  { exact (subtype.coe_mk _ _).symm }
end

lemma one_zero_mem : ((1, 0) : ℕ × zmod 2) ∈ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  refine ⟨⟨⟨1, 0⟩, _⟩, rfl⟩,
  rintros _ ⟨H, _, rfl⟩,
  rintros _ ⟨H, _, rfl⟩,
  dsimp at *,
  refine set.mem_of_mem_of_subset _ H_1,
  exact or.inl rfl
end

lemma L_ext (l : L) : l.val ∈ {a : ℕ × zmod 2 | ∃ (l : L), a = ↑l} :=
⟨l, rfl⟩

lemma L_ext_sub (l : L) :
  (l : ℕ × zmod 2) ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) :=
l.2

lemma one_one_mem : ((1, 1) : ℕ × zmod 2) ∈ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  refine ⟨⟨⟨1, 1⟩, _⟩, rfl⟩,
  rintros _ ⟨H, _, rfl⟩,
  rintros _ ⟨H, _, rfl⟩,
  dsimp at *,
  refine set.mem_of_mem_of_subset _ H_1,
  exact or.inr rfl
end

lemma L_mem_n_succ (l0 : ℕ) :
  ((l0.succ, 1) : ℕ × zmod 2) ∈ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  induction l0 with n hi,
  { exact one_one_mem },
  simp,
  refine ⟨⟨(n.succ.succ, 1), _⟩, _⟩,
  rw add_one_one,
  refine subsemiring.add_mem _ _ _,
  { cases hi with l hl,
    rw hl,
    exact l.2 },
  { rintros _ ⟨H, _, rfl⟩,
    rintros _ ⟨H, _, rfl⟩,
    dsimp at *,
    refine set.mem_of_mem_of_subset _ H_1,
    exact or.inl rfl },
  { exact (subtype.coe_mk _ _).symm }
end

lemma L_mem_n_one (l : ℕ × zmod 2) (l0 : l.1 ≠ 0) (l1 : l.2 = 1) :
  l ∈ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } :=
begin
  rcases l with ⟨l, l2⟩,
  dsimp at l0 l1,
  subst l1,
  rw (nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr l0)).symm,
  exact L_mem_n_succ l.pred,
end

lemma L_not_mem (l : ℕ × zmod 2) :
  l ∉ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } ↔ l = (⟨0, 1⟩ : ℕ × zmod 2) :=
begin
  refine ⟨λ h, _, _⟩,
  { rcases l with ⟨n, n2⟩,
    obtain F := mem_zmod_2 n2,
    rcases F with rfl | rfl,
    { refine (h _).elim,
      exact L_mem_n_zero (n, 0) rfl },
    {
      by_contra k,
      simp only [and_true, prod.mk.inj_iff, eq_self_iff_true] at k,
      apply h,
      exact L_mem_n_one (n, 1) k rfl } },
  { rintro rfl,
    exact zu_not_mem }
end

lemma L_mem (l : ℕ × zmod 2) :
  l ∈ {a : ℕ × zmod 2 | ∃ l : L, a = ↑l } ↔ l ≠ (⟨0, 1⟩ : ℕ × zmod 2) :=
begin
  convert not_congr (L_not_mem l),
  rw not_not,
end

lemma L_mem_ssr (l : ℕ × zmod 2) :
  l ∈ subsemiring.closure ({(1, 0), (1, 1)} : set (ℕ × zmod 2)) ↔ l ≠ (0, 1) :=
begin
  rw ← L_mem,
  refine ⟨λ h, ⟨⟨l, h⟩, rfl⟩, _⟩,
  rintro ⟨l, rfl⟩,
  exact L_ext_sub l,
end

lemma bot_le : ∀ (a : L), 0 ≤ a :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩,
  by_cases a0 : an ≠ 0,
  { refine or.inr _,
    exact (lt_def _ _).mpr (nat.pos_of_ne_zero a0) },
  { rw not_not at a0,
    refine or.inl _,
    subst a0,
    rcases mem_zmod_2 a2 with (rfl | rfl),
    { simpa only, },
    { refine (zu_not_mem).elim _,
      exact ⟨⟨_, ha⟩, rfl⟩ } }
end

lemma add_self_zmod_2 (a : zmod 2) : a + a = 0 :=
begin
  rcases mem_zmod_2 a with rfl | rfl;
  refl,
end

instance zm2 : nontrivial (zmod 2) :=
⟨⟨0, 1, fin.zero_ne_one⟩⟩

lemma le_iff_exists_add : ∀ (a b : L), a ≤ b ↔ ∃ (c : L), b = a + c :=
begin
  rintros ⟨⟨an, a2⟩, ha⟩ ⟨⟨bn, b2⟩, hb⟩,
  refine ⟨λ h, _, λ h, _⟩,
  { refine ⟨⟨⟨bn - an, b2 + a2⟩, (L_mem_ssr _).mpr _⟩, _⟩,
    { rcases h with h1 | h2,
      { rcases subtype.mk_eq_mk.mp h1 with ⟨rfl, rfl⟩,
        rw [ne.def, nat.sub_self, prod.mk.inj_iff, eq_self_iff_true, true_and],
        intros h,
        rw [add_self_zmod_2 a2] at h,
        exact (@zero_ne_one (zmod 2) _ _) h },
      { rw [lt_def, subtype.coe_mk] at h2,
        rw [ne.def, prod.mk.inj_iff, not_and_distrib],
        exact or.inl (ne_of_gt (nat.sub_pos_of_lt h2)) } },
    { congr,
      simp only,
      apply (nat.add_sub_cancel' _).symm,
      simp only [prod.mk.inj_iff, lt_def, subtype.mk_eq_mk, le_def_L] at h,
      rcases h with ⟨rfl, rfl⟩ | h,
      refl,
      exact h.le,
      simp only,
      rw [add_comm b2, ← add_assoc, add_self_zmod_2, zero_add] } },
  { simp only [prod.mk.inj_iff, lt_def, subtype.mk_eq_mk, le_def_L],
    rcases h with ⟨⟨⟨c, c2⟩, hc⟩, abc⟩,
    injection abc with abc,
    simp only [prod.mk_add_mk, prod.mk.inj_iff] at abc,
    cases c,
    { refine or.inl _,
      rw L_mem_ssr at hc,
      simp only [true_and, prod.mk.inj_iff, eq_self_iff_true, ne.def] at hc,
      rcases mem_zmod_2 c2 with rfl | rfl,
      { simp_rw [add_zero] at abc,
        rcases b2 with ⟨b2, bp⟩, rcases a2 with ⟨a2, ap⟩,
        simp only [subtype.mk_eq_mk] at abc ⊢,
        exact ⟨abc.1.symm, abc.2.symm⟩ },
      { exfalso,
        exact hc rfl } },
    { refine or.inr _,
      rw abc.1,
      exact (lt_add_iff_pos_right _).mpr c.succ_pos } }
end

lemma eq_zero_or_eq_zero_of_mul_eq_zero : ∀ (a b : L), a * b = 0 → a = 0 ∨ b = 0 :=
begin
  rintros ⟨⟨a, a2⟩, ha⟩ ⟨⟨b, b2⟩, hb⟩ ab1,
  injection ab1 with ab,
  injection ab with abn ab2,
  clear ab1 ab ab2,
  rw mul_eq_zero at abn,
  rcases abn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩,
  { refine or.inl _,
    rcases mem_zmod_2 a2 with rfl | rfl,
    { refl },
    { exact (((L_mem_ssr _).mp ha) rfl).elim } },
  { refine or.inr _,
    rcases mem_zmod_2 b2 with rfl | rfl,
    { refl },
    { rw L_mem_ssr at hb,
      exact (hb rfl).elim } }
end

lemma can : canonically_ordered_comm_semiring L :=
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
