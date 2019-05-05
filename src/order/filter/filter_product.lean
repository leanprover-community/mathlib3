/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir
"Filterproducts" (ultraproducts on general filters), ultraproducts.
-/

import order.filter.basic

universes u v
variables {α : Type u} (β : Type v) (φ : filter α)
local attribute [instance] classical.prop_decidable

namespace filter 

/-- Two sequences are bigly equal iff the kernel of their difference is in φ -/
def bigly_equal : setoid (α → β) := 
⟨ λ a b, {n | a n = b n} ∈ φ,
  λ a, by simp only [eq_self_iff_true, (set.univ_def).symm, univ_sets], 
  λ a b ab, by simpa only [eq_comm], 
  λ a b c ab bc, sets_of_superset φ (inter_sets φ ab bc) (λ n r, eq.trans r.1 r.2)⟩

/-- Ultraproduct, but on a general filter -/
def filterprod := quotient (bigly_equal β φ)
local notation `β*` := filterprod β φ

namespace filter_product

variables {α β φ} include φ

def of_seq : (α → β) → β* := @quotient.mk' (α → β) (bigly_equal β φ)

/-- Equivalence class containing the constant sequence of a term in β -/
def of (b : β): β* := of_seq (function.const α b)

/-- Lift function to filter product -/
def lift (f : β → β) : β* → β* :=
λ x, quotient.lift_on' x (λ a, (of_seq $ λ n, f (a n) : β*)) $
  λ a b h, quotient.sound' $ show _ ∈ _, by filter_upwards [h] λ i hi, congr_arg _ hi

/-- Lift binary operation to filter product -/
def lift₂ (f : β → β → β) : β* → β* → β* :=
λ x y, quotient.lift_on₂' x y (λ a b, (of_seq $ λ n, f (a n) (b n) : β*)) $
  λ a₁ a₂ b₁ b₂ h1 h2, quotient.sound' $ show _ ∈ _,
  by filter_upwards [h1, h2] λ i hi1 hi2, congr (congr_arg _ hi1) hi2

/-- Lift properties to filter product -/
def lift_rel (R : β → Prop) : β* → Prop :=
λ x, quotient.lift_on' x (λ a, {i : α | R (a i)} ∈ φ) $ λ a b h, propext 
  ⟨ λ ha, by filter_upwards [h, ha] λ i hi hia, by simpa [hi.symm],
    λ hb, by filter_upwards [h, hb] λ i hi hib, by simpa [hi.symm.symm] ⟩

/-- Lift binary relations to filter product -/
def lift_rel₂ (R : β → β → Prop) : β* → β* → Prop :=
λ x y, quotient.lift_on₂' x y (λ a b, {i : α | R (a i) (b i)} ∈ φ) $
  λ a₁ a₂ b₁ b₂ h₁ h₂, propext 
  ⟨ λ ha, by filter_upwards [h₁, h₂, ha] λ i hi1 hi2 hia, by simpa [hi1.symm, hi2.symm],
    λ hb, by filter_upwards [h₁, h₂, hb] λ i hi1 hi2 hib, by simpa [hi1.symm.symm, hi2.symm.symm] ⟩

instance coe_filterprod : has_coe β β* := ⟨ of ⟩

instance [has_add β] : has_add β* := { add := lift₂ has_add.add }

instance [has_zero β] : has_zero β* := { zero := of 0 }

instance [has_neg β] : has_neg β* :=
{ neg := lift has_neg.neg }

instance [add_semigroup β] : add_semigroup β* :=
{ add_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _ + _ + _ = _ + (_ + _)} ∈ _, by simp only [add_assoc, eq_self_iff_true]; exact φ.univ_sets, 
  ..filter_product.has_add }

instance [add_monoid β] : add_monoid β* :=
{ zero_add := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [zero_add]; apply (setoid.iseqv _).1)),
  add_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound'(by simp only [add_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup, 
  ..filter_product.has_zero }

instance [add_comm_semigroup β] : add_comm_semigroup β* :=
{ add_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [add_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_semigroup }

instance [add_comm_monoid β] : add_comm_monoid β* := 
{ ..filter_product.add_comm_semigroup, 
  ..filter_product.add_monoid }

instance [add_group β] : add_group β* :=
{ add_left_neg := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [add_left_neg]; apply (setoid.iseqv _).1)), 
  ..filter_product.add_monoid, 
  ..filter_product.has_neg }

instance [add_comm_group β] : add_comm_group β* := 
{ ..filter_product.add_comm_monoid, 
  ..filter_product.add_group }

instance [has_mul β] : has_mul β* :=
{ mul := lift₂ has_mul.mul }

instance [has_one β] : has_one β* := { one := of 1 }

instance [has_inv β] : has_inv β* :=
{ inv := lift has_inv.inv }

instance [semigroup β] : semigroup β* :=
{ mul_assoc := λ x y z, quotient.induction_on₃' x y z $ λ a b c, quotient.sound' $
    show {n | _ * _ * _ = _ * (_ * _)} ∈ _, by simp only [mul_assoc, eq_self_iff_true]; exact φ.2, 
  ..filter_product.has_mul }

instance [monoid β] : monoid β* :=
{ one_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [one_mul]; apply (setoid.iseqv _).1)),
  mul_one := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_one]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup,
  ..filter_product.has_one }

instance [comm_semigroup β] : comm_semigroup β* :=
{ mul_comm := λ x y, quotient.induction_on₂' x y 
    (λ a b, quotient.sound' (by simp only [mul_comm]; apply (setoid.iseqv _).1)), 
  ..filter_product.semigroup }

instance [comm_monoid β] : comm_monoid β* := 
{ ..filter_product.comm_semigroup, 
  ..filter_product.monoid }

instance [group β] : group β* :=
{ mul_left_inv := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_left_inv]; apply (setoid.iseqv _).1)), 
  ..filter_product.monoid,
  ..filter_product.has_inv }

instance [comm_group β] : comm_group β* := 
{ ..filter_product.comm_monoid, 
  ..filter_product.group }

instance [distrib β] : distrib β* :=
{ left_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [left_distrib]; apply (setoid.iseqv _).1)),
  right_distrib := λ x y z, quotient.induction_on₃' x y z 
    (λ x y z, quotient.sound' (by simp only [right_distrib]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_add,
  ..filter_product.has_mul }

instance [mul_zero_class β] : mul_zero_class β* :=
{ zero_mul := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [zero_mul]; apply (setoid.iseqv _).1)),
  mul_zero := λ x, quotient.induction_on' x 
    (λ a, quotient.sound' (by simp only [mul_zero]; apply (setoid.iseqv _).1)), 
  ..filter_product.has_mul,
  ..filter_product.has_zero }

instance [semiring β] : semiring β* := 
{ ..filter_product.add_comm_monoid, 
  ..filter_product.monoid, 
  ..filter_product.distrib, 
  ..filter_product.mul_zero_class }

instance [ring β] : ring β* := 
{ ..filter_product.add_comm_group, 
  ..filter_product.monoid, 
  ..filter_product.distrib }

instance [comm_semiring β] : comm_semiring β* := 
{ ..filter_product.semiring, 
  ..filter_product.comm_monoid }

instance [comm_ring β] : comm_ring β* := 
{ ..filter_product.ring, 
  ..filter_product.comm_semigroup }

instance [zero_ne_one_class β] (NT : φ ≠ ⊥) : zero_ne_one_class β* :=
{ zero_ne_one := λ c, have c' : _ := quotient.exact' c, by
  { change _ ∈ _ at c', 
    simp only [set.set_of_false, zero_ne_one, empty_in_sets_eq_bot] at c', 
    exact NT c' },
  ..filter_product.has_zero, 
  ..filter_product.has_one }

instance [division_ring β] (U : is_ultrafilter φ) : division_ring β* :=
{ mul_inv_cancel := λ x, quotient.induction_on' x $ λ a hx, quotient.sound' $
    have hx1 : _ := (not_imp_not.mpr quotient.eq'.mpr) hx,
    have hx2 : _ := (ultrafilter_iff_compl_mem_iff_not_mem.mp U _).mpr hx1,
    have h : {n : α | ¬a n = 0} ⊆ {n : α | a n * (a n)⁻¹ = 1} := 
      by rw [set.set_of_subset_set_of]; exact λ n, division_ring.mul_inv_cancel,
    mem_sets_of_superset hx2 h,
  inv_mul_cancel := λ x, quotient.induction_on' x $ λ a hx, quotient.sound' $
    have hx1 : _ := (not_imp_not.mpr quotient.eq'.mpr) hx,
    have hx2 : _ := (ultrafilter_iff_compl_mem_iff_not_mem.mp U _).mpr hx1,
    have h : {n : α | ¬a n = 0} ⊆ {n : α | (a n)⁻¹ * a n = 1} := 
      by rw [set.set_of_subset_set_of]; exact λ n, division_ring.inv_mul_cancel,
    mem_sets_of_superset hx2 h, 
  ..filter_product.ring, 
  ..filter_product.has_inv, 
  ..filter_product.zero_ne_one_class U.1 }

instance [field β] (U : is_ultrafilter φ) : field β* :=
{ ..filter_product.comm_ring, 
  ..filter_product.division_ring U }

noncomputable instance [discrete_field β] (U : is_ultrafilter φ) : discrete_field β* :=
{ inv_zero := quotient.sound' $ by show _ ∈ _;
    simp only [inv_zero, eq_self_iff_true, (set.univ_def).symm, univ_sets],
  has_decidable_eq := by apply_instance, 
  ..filter_product.field U }

instance [has_le β] : has_le β* := { le := lift_rel₂ has_le.le }

instance [preorder β] : preorder β* :=
{ le_refl := λ x, quotient.induction_on' x $ λ a, show _ ∈ _, 
    by simp only [le_refl, (set.univ_def).symm, univ_sets],
  le_trans := λ x y z, quotient.induction_on₃' x y z $ λ a b c hab hbc, 
    by filter_upwards [hab, hbc] λ i hiab hibc, le_trans hiab hibc, 
  ..filter_product.has_le }

instance [partial_order β] : partial_order β* :=
{ le_antisymm := λ x y, quotient.induction_on₂' x y $ λ a b hab hba, quotient.sound' $ 
    have hI : {n | a n = b n} = _ ∩ _ := set.ext (λ n, le_antisymm_iff), 
    show _ ∈ _, by rw hI; exact inter_sets _ hab hba
  ..filter_product.preorder }

instance [linear_order β] (U : is_ultrafilter φ) : linear_order β* :=
{ le_total := λ x y, quotient.induction_on₂' x y $ λ a b, 
    have hS : _ ⊆ {i | b i ≤ a i} := λ i, le_of_not_le,
    or.cases_on (mem_or_compl_mem_of_ultrafilter U {i | a i ≤ b i})
      (λ h, or.inl h) 
      (λ h, or.inr (sets_of_superset _ h hS))
  ..filter_product.partial_order }

theorem of_inj (NT : φ ≠ ⊥): function.injective (@of _ β φ) :=
begin
  intros r s rs, by_contra N,
  rw [of, of, of_seq, quotient.eq', bigly_equal] at rs, 
  simp only [N, set.set_of_false, empty_in_sets_eq_bot] at rs,
  exact NT rs
end

theorem of_seq_fun (f g : α → β) (h : β → β) (H : {n : α | f n = h (g n) } ∈ φ) : 
  of_seq f = (lift h) (@of_seq _ _ φ g) := quotient.sound' H

theorem of_seq_fun₂ (f g₁ g₂ : α → β) (h : β → β → β) (H : {n : α | f n = h (g₁ n) (g₂ n) } ∈ φ) : 
  of_seq f = (lift₂ h) (@of_seq _ _ φ g₁) (@of_seq _ _ φ g₂) := quotient.sound' H

@[simp] lemma of_seq_zero [has_zero β] (f : α → β) : of_seq 0 = (0 : β*) := rfl

@[simp] lemma of_seq_add [has_add β] (f g : α → β) : of_seq (f + g) = of_seq f + (of_seq g : β*) := rfl

@[simp] lemma of_seq_neg [has_neg β] (f : α → β) : of_seq (-f) = - (of_seq f : β*) := rfl

@[simp] lemma of_seq_one [has_one β] (f : α → β) : of_seq 1 = (1 : β*) := rfl

@[simp] lemma of_seq_mul [has_mul β] (f g : α → β) : of_seq (f * g) = of_seq f * (of_seq g : β*) := rfl

@[simp] lemma of_seq_inv [has_inv β] (f : α → β) : of_seq (f⁻¹) = (of_seq f : β*)⁻¹ := rfl

lemma of_eq_coe (x : β) : of x = (↑x : β*) := rfl

@[simp] lemma of_id (x : β) : of x = (x : β*) := rfl

lemma of_eq (x y : β) (NT : φ ≠ ⊥) : x = y ↔ of x = (of y : β*) := ⟨λ h, by rw h, by apply of_inj NT⟩

lemma of_ne (x y : β) (NT : φ ≠ ⊥) : x ≠ y ↔ of x ≠ (of y : β*) := by show ¬ x = y ↔ of x ≠ of y; rwa [of_eq]

lemma of_eq_zero [has_zero β] (NT : φ ≠ ⊥) (x : β) : x = 0 ↔ of x = (0 : β*) := of_eq _ _ NT

lemma of_ne_zero [has_zero β] (NT : φ ≠ ⊥) (x : β) : x ≠ 0 ↔ of x ≠ (0 : β*) := of_ne _ _ NT

@[simp] lemma of_zero [has_zero β] : of 0 = (0 : β*) := rfl

@[simp] lemma of_add [has_add β] (x y : β) : of (x + y) = of x + (of y : β*) := rfl

@[simp] lemma of_neg [has_neg β] (x : β) : of (- x) = - (of x : β*) := rfl

@[simp] lemma of_one [has_one β] : of 1 = (1 : β*) := rfl

@[simp] lemma of_mul [has_mul β] (x y : β) : of (x * y) = of x * (of y : β*) := rfl

@[simp] lemma of_inv [has_inv β] (x : β) : of (x⁻¹) = (of x : β*)⁻¹ := rfl

lemma of_rel_of_rel (R : β → Prop) (x : β) : 
  R x → (lift_rel R) (of x : β*) := 
λ hx, by show {i | R x} ∈ _; simp only [hx]; exact univ_mem_sets  

lemma of_rel (R : β → Prop) (x : β) (NT: φ ≠ ⊥) : 
  R x ↔ (lift_rel R) (of x : β*) :=
⟨ of_rel_of_rel _ _, 
  λ hxy, by change {i | R x} ∈ _ at hxy; by_contra h;
  simp only [h, set.set_of_false, empty_in_sets_eq_bot] at hxy;
  exact NT hxy ⟩

lemma of_rel_of_rel₂ (R : β → β → Prop) (x y : β) : 
  R x y → (lift_rel₂ R) (of x) (of y : β*) :=
λ hxy, by show {i | R x y} ∈ _; simp only [hxy]; exact univ_mem_sets  

lemma of_rel₂ (R : β → β → Prop) (x y : β) (NT: φ ≠ ⊥) : 
  R x y ↔ (lift_rel₂ R) (of x) (of y : β*) :=
⟨ of_rel_of_rel₂ _ _ _, 
  λ hxy, by change {i | R x y} ∈ _ at hxy; by_contra h;
  simp only [h, set.set_of_false, empty_in_sets_eq_bot] at hxy;
  exact NT hxy ⟩

lemma of_le_of_le [has_le β] (x y : β) : x ≤ y → of x ≤ (of y : β*) := of_rel_of_rel₂ _ _ _

lemma of_le [has_le β] (x y : β) (NT: φ ≠ ⊥) : x ≤ y ↔ of x ≤ (of y : β*) := of_rel₂ _ _ _ NT

lemma lt_def [K : preorder β] (U : is_ultrafilter φ) (x y : β*) : 
  (x < y) ↔ @lift_rel₂ _ _ φ K.lt x y := 
⟨ quotient.induction_on₂' x y $ λ a b ⟨hxy, hyx⟩,
  have hyx' : _ := (ultrafilter_iff_compl_mem_iff_not_mem.mp U _).mpr hyx,
  by filter_upwards [hxy, hyx'] λ i hi1 hi2, lt_iff_le_not_le.mpr ⟨hi1, hi2⟩, 
  quotient.induction_on₂' x y $ λ a b hab, 
  ⟨ by filter_upwards [hab] λ i, le_of_lt, λ hba, 
    have hc : ∀ i : α, a i < b i ∧ b i ≤ a i → false := λ i ⟨h1, h2⟩, not_lt_of_le h2 h1,
    have h0 : ∅ = {i : α | a i < b i} ∩ {i : α | b i ≤ a i} := 
    by simp only [set.inter_def, hc, set.set_of_false, eq_self_iff_true, set.mem_set_of_eq],
    U.1 $ empty_in_sets_eq_bot.mp $ by rw [h0]; exact inter_sets _ hab hba ⟩ ⟩

lemma lt_def' [K : preorder β] (U : is_ultrafilter φ) : 
  filter_product.preorder.lt = @lift_rel₂ _ _ φ K.lt := 
by ext x y; exact lt_def U x y

lemma of_lt_of_lt [preorder β] (U : is_ultrafilter φ) (x y : β) : 
  x < y → of x < (of y : β*) := 
by rw lt_def U; apply of_rel_of_rel₂

lemma of_lt [preorder β] (x y : β) (U : is_ultrafilter φ) : x < y ↔ of x < (of y : β*) := 
by rw lt_def U; exact of_rel₂ _ _ _ U.1

instance [ordered_comm_group β] (U : is_ultrafilter φ) : ordered_comm_group β* :=
{ add_le_add_left := λ x y hxy z, by revert hxy; exact quotient.induction_on₃' x y z 
    (λ a b c hab, by filter_upwards [hab] λ i hi, by simpa),
  add_lt_add_left := λ x y hxy z, by revert hxy; exact quotient.induction_on₃' x y z
    (λ a b c hab, by rw lt_def U at hab ⊢; filter_upwards [hab] λ i hi, add_lt_add_left hi (c i)),
  ..filter_product.partial_order, ..filter_product.add_comm_group }

instance [ordered_ring β] (U : is_ultrafilter φ) : ordered_ring β* :=
{ mul_nonneg := λ x y, quotient.induction_on₂' x y $
    λ a b ha hb, by filter_upwards [ha, hb] λ i, by simp only [set.mem_set_of_eq]; exact mul_nonneg,
  mul_pos := λ x y, quotient.induction_on₂' x y $
    λ a b ha hb, by rw lt_def U at ha hb ⊢; filter_upwards [ha, hb] λ i, mul_pos,
  ..filter_product.ring, ..filter_product.ordered_comm_group U, ..filter_product.zero_ne_one_class U.1 }

instance [linear_ordered_ring β] (U : is_ultrafilter φ) : linear_ordered_ring β* :=
{ zero_lt_one := by rw lt_def U; show {i | (0 : β) < 1} ∈ _; simp only [zero_lt_one, (set.univ_def).symm, univ_sets],
  ..filter_product.ordered_ring U, ..filter_product.linear_order U }

instance [linear_ordered_field β] (U : is_ultrafilter φ) : linear_ordered_field β* :=
{ ..filter_product.linear_ordered_ring U, ..filter_product.field U }

instance [linear_ordered_comm_ring β] (U : is_ultrafilter φ) : linear_ordered_comm_ring β* :=
{ ..filter_product.linear_ordered_ring U, ..filter_product.comm_monoid }

noncomputable instance [decidable_linear_order β] (U : is_ultrafilter φ) : decidable_linear_order β* :=
{ decidable_le := by apply_instance,
  ..filter_product.linear_order U }

noncomputable instance [decidable_linear_ordered_comm_group β] (U : is_ultrafilter φ) : decidable_linear_ordered_comm_group β* :=
{ ..filter_product.ordered_comm_group U, ..filter_product.decidable_linear_order U }

noncomputable instance [decidable_linear_ordered_comm_ring β] (U : is_ultrafilter φ) : decidable_linear_ordered_comm_ring β* :=
{ ..filter_product.linear_ordered_comm_ring U, ..filter_product.decidable_linear_ordered_comm_group U }

noncomputable instance [discrete_linear_ordered_field β] (U : is_ultrafilter φ) : discrete_linear_ordered_field β* :=
{ ..filter_product.linear_ordered_field U, ..filter_product.decidable_linear_ordered_comm_ring U, ..filter_product.discrete_field U }

end filter_product

end filter
