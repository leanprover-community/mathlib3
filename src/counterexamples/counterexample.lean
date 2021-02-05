import algebra.char_zero
import data.real.basic
import data.zmod.basic
import ring_theory.subsemiring
import tactic

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


@[derive [comm_semiring]]
def L : Type := subsemiring.closure ({(1, 1)} : set (ℕ × zmod 2))

--instance : has_coe K ℚ := ⟨λ x, x.1⟩

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

instance ocs : ordered_comm_semiring L :=
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
  simpa only [subsemiring.mem_coe, set.mem_set_of_eq, set.singleton_subset_iff] using H2, },
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
  work_on_goal 0
  { cases b,
    cases a,
    cases ab,
    exact rfl.ge },
  have ca : (c + a).val = c.val + a.val := rfl,
  have cb : (c + b).val = c.val + b.val := rfl,
  have : (c+a).val.fst <  (c+b).val.fst,
  { simpa [ca, cb] },
  simp [(≤)],
  apply le_of_lt,

 },
 le_of_add_le_add_left := _,
 zero_le_one := _,
 mul_lt_mul_of_pos_left := _,
 mul_lt_mul_of_pos_right := _,
 mul_comm := _},
end

instance : preorder L :=
{ le := λ ⟨⟨x0, x1⟩, hx⟩ ⟨⟨y0, y1⟩, hy⟩, ((x0 = y0 ∧ x1 = y1) ∨ (x0 < y0)),
  le_refl := λ a, by {cases a, cases a_val, simp only [true_or, eq_self_iff_true, and_self] },
  le_trans := λ ⟨⟨x0, x1⟩, hx⟩ ⟨⟨y0, y1⟩, hy⟩ z xy yz,
  begin
    rcases z with ⟨⟨z0, z1⟩, hz⟩,
    rcases xy with (⟨rfl, rfl⟩ | _),
    { rcases yz with (⟨rfl, rfl⟩ | _),
      { exact or.inl ⟨rfl, rfl⟩ },
      { exact or.inr yz } },
    { rcases yz with (⟨rfl, rfl⟩ | _),
      { exact or.inr xy },
      { exact or.inr (xy.trans yz) } }
  end }
