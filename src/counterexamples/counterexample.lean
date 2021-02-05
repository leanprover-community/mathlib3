import algebra.char_zero
import data.real.basic
import data.zmod.basic
import ring_theory.subsemiring
import tactic
/-! Reference:
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/canonically_ordered.20pathology

-/


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

instance : preorder L :=
{ le := λ x y, ( x.1 = y.1 ∨ x.1.1 < y.1.1 ),
  le_refl := by simp only [forall_const, true_or, eq_self_iff_true],
  le_trans := λ x y z xy yz,
  begin
    rcases xy,
    { rcases yz,
      { exact or.inl (xy.trans yz) },
      { exact or.inr (lt_of_le_of_lt (congr_arg prod.fst xy).le yz) } },
    { refine or.inr (xy.trans_le _),
      cases yz,
      { exact (congr_arg prod.fst yz).le },
      {  exact le_of_lt yz } },
  end }

@[simp] lemma pro (a b : L) : a < b ↔ a.val.1 < b.val.1 :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {cases h, cases b, cases a, cases h_left, cases a_val, cases b_val, work_on_goal 0 { cases b_val_snd, cases a_val_snd, dsimp at *, simp at *, cases h_left, induction h_left_right, induction h_left_left, simp at *, cases h_right }, exact h_left},
  cases b,
  cases a,
  cases a_val,
  cases b_val,
  cases b_val_snd,
  cases a_val_snd,
  dsimp at *,
  fsplit,
  refine or.inr h,
  intros hh,
  cases hh,
  apply not_le.mpr h,
  apply le_of_eq,
  simp at *,
  cases hh,
  assumption,
  apply not_le.mpr h,
  apply le_of_lt,
  assumption,
end

lemma ocs : ordered_comm_semiring L :=
begin
  refine {add := (+),
 add_assoc := add_assoc,
 zero := 0,
 zero_add := zero_add,
 add_zero := add_zero,
 add_comm := add_comm,
 mul := (*),
 mul_assoc := mul_assoc,
 one := by {refine ⟨(1, 1), _⟩,
  rintros _ ⟨H1, rfl⟩,
  rintros _ ⟨H2, rfl⟩,
  refine set.mem_of_mem_of_subset _ H2,
  exact set.mem_union_right _ rfl },
 one_mul := one_mul,
 mul_one := mul_one,
 zero_mul := zero_mul,
 mul_zero := mul_zero,
 left_distrib := mul_add,
 right_distrib := add_mul,
 add_left_cancel := by {
    intros a b c h,
    cases c,
    cases b,
    cases b_val,
    cases c_val,
    simp only [prod.mk.inj_iff, subtype.mk_eq_mk],
    fsplit;
    { injections_and_clear,
      simp only [prod.mk.inj_iff, subtype.mk_eq_mk, add_right_inj] at h_1,
      cases h_1,
      assumption } },
 add_right_cancel := by {
    intros a b c h,
    cases c,
    cases a,
    cases a_val,
    cases c_val,
    simp only [prod.mk.inj_iff, subtype.mk_eq_mk],
    fsplit;
    { injections_and_clear,
      simp at h_1,
      cases h_1,
      assumption } },
 le := (≤),
 lt := λ (a b : L), a ≤ b ∧ ¬b ≤ a,
 le_refl := λ _, le_rfl,
 le_trans := λ _ _ _, le_trans,
 lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
 le_antisymm := by {
  intros a b ab ba,
  cases ab,
  { exact subtype.eq ab },
  { apply (not_le.mpr ab).elim,
    cases ba,
    exact (congr_arg prod.fst ba).le,
    exact le_of_lt ba } },
 add_le_add_left := by {
  intros a b ab c,
  cases ab,
  { cases b,
    cases a,
    cases ab,
    exact rfl.ge },
  { have ca : (c + a).val = c.val + a.val := rfl,
    have cb : (c + b).val = c.val + b.val := rfl,
    have : (c+a).val.fst <  (c+b).val.fst,
    { simpa [ca, cb] },
     refine or.inr this } },
 le_of_add_le_add_left := begin
   intros a b c ab,
   cases ab,
    { refine or.inl _,
      cases c,
      cases b,
      cases b_val,
      cases c_val,
      simp only [prod.mk.inj_iff],
      fsplit,
      work_on_goal 0
      { injections_and_clear, simp only [add_right_inj] at h_1, exact h_1},
      injections_and_clear,
      simp only [add_right_inj] at h_2,
      exact h_2 },
    refine or.inr _,
    exact (add_lt_add_iff_left a.val.fst).mp ab
 end,
 zero_le_one := or.inr zero_lt_one,
 mul_lt_mul_of_pos_left := begin
  intros a b c ab c0,
  cases c0,
  cases c0_left,
  exact c0_right.elim (or.inl c0_left.symm),
  cases ab,
  cases ab_left,
  exact (ab_right (or.inl ab_left.symm)).elim,
  { cases c, cases c_val, cases c_val_snd,
    simp only [subsemiring.coe_mul, pro, subtype.coe_mk, subtype.val_eq_coe, prod.mk_mul_mk],
    exact (mul_lt_mul_left c0_left).mpr ab_left },
 end,
 mul_lt_mul_of_pos_right := begin
  intros a b c ab c0,
  cases c0,
  cases c0_left,
  exact c0_right.elim (or.inl c0_left.symm),
  cases ab,
  cases ab_left,
  exact (ab_right (or.inl ab_left.symm)).elim,
  { cases c, cases c_val, cases c_val_snd,
    simp only [subsemiring.coe_mul, pro, subtype.coe_mk, subtype.val_eq_coe, prod.mk_mul_mk],
    exact (mul_lt_mul_right c0_left).mpr ab_left },
 end,
 mul_comm := mul_comm},
end

lemma can : canonically_ordered_comm_semiring L :=
begin
  refine {add := (+),
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
 le_antisymm := λ _ _, antisymm,
 add_le_add_left := λ _ _, add_le_add_left,
 lt_of_add_lt_add_left := λ (a : L) {b c : L}, (add_lt_add_iff_left a).mp,
 bot := 0,
 bot_le := begin
    intros a,
    by_cases a0 : a = 0,
    exact eq.ge a0,
    refine or.inr _,simp,
    by_contra,
    apply a0,
    rw not_lt at h,
    cases a, cases a_val, cases a_val_snd, dsimp at *, simp at *, fsplit, work_on_goal 1 { ext1, dsimp at * },
rw ← nat.le_zero_iff,
exact h,
sorry,
 end,
 le_iff_exists_add := begin
   intros a b,
   refine ⟨λ h, _, λ h, _⟩,
   sorry,
   rcases h with ⟨h, rfl⟩,
   cases h, cases a, cases a_val, cases h_val, cases h_val_snd, cases a_val_snd, dsimp at *, simp at *, norm_cast,
   by_cases h0 : h_val_fst = 0,
   { subst h0,
     refine or.inl _,
     simp,
     rw ← zero_iff,
     sorry,
      },
    refine or.inr _,
    by_contra,
    push_neg at h,
    apply h0,
    apply nat.le_zero_iff.mp h,
 end,
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
 eq_zero_or_eq_zero_of_mul_eq_zero := begin
   intros a b ab,

--   tidy?,
 end},
end
