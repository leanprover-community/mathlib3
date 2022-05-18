/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group_with_zero.power
import data.list.big_operators
import data.multiset.basic

/-!
# Sums and products over multisets

In this file we define products and sums indexed by multisets. This is later used to define products
and sums indexed by finite sets.

## Main declarations

* `multiset.prod`: `s.prod f` is the product of `f i` over all `i ∈ s`. Not to be mistaken with
  the cartesian product `multiset.product`.
* `multiset.sum`: `s.sum f` is the sum of `f i` over all `i ∈ s`.
-/

variables {ι α β γ : Type*}

namespace multiset
section comm_monoid
variables [comm_monoid α] {s t : multiset α} {a : α} {m : multiset ι} {f g : ι → α}

/-- Product of a multiset given a commutative monoid structure on `α`.
  `prod {a, b, c} = a * b * c` -/
@[to_additive "Sum of a multiset given a commutative additive monoid structure on `α`.
  `sum {a, b, c} = a + b + c`"]
def prod : multiset α → α := foldr (*) (λ x y z, by simp [mul_left_comm]) 1

@[to_additive]
lemma prod_eq_foldr (s : multiset α) : prod s = foldr (*) (λ x y z, by simp [mul_left_comm]) 1 s :=
rfl

@[to_additive]
lemma prod_eq_foldl (s : multiset α) : prod s = foldl (*) (λ x y z, by simp [mul_right_comm]) 1 s :=
(foldr_swap _ _ _ _).trans (by simp [mul_comm])

@[simp, norm_cast, to_additive] lemma coe_prod (l : list α) : prod ↑l = l.prod := prod_eq_foldl _

@[simp, to_additive]
lemma prod_to_list (s : multiset α) : s.to_list.prod = s.prod :=
begin
  conv_rhs { rw ←coe_to_list s },
  rw coe_prod,
end

@[simp, to_additive] lemma prod_zero : @prod α _ 0 = 1 := rfl

@[simp, to_additive]
lemma prod_cons (a : α) (s) : prod (a ::ₘ s) = a * prod s := foldr_cons _ _ _ _ _

@[simp, to_additive]
lemma prod_erase [decidable_eq α] (h : a ∈ s) : a * (s.erase a).prod = s.prod :=
by rw [← s.coe_to_list, coe_erase, coe_prod, coe_prod, list.prod_erase ((s.mem_to_list a).2 h)]

@[simp, to_additive]
lemma prod_singleton (a : α) : prod {a} = a :=
by simp only [mul_one, prod_cons, singleton_eq_cons, eq_self_iff_true, prod_zero]

@[to_additive]
lemma prod_pair (a b : α) : ({a, b} : multiset α).prod = a * b :=
by rw [insert_eq_cons, prod_cons, prod_singleton]

@[simp, to_additive]
lemma prod_add (s t : multiset α) : prod (s + t) = prod s * prod t :=
quotient.induction_on₂ s t $ λ l₁ l₂, by simp

lemma prod_nsmul (m : multiset α) : ∀ (n : ℕ), (n • m).prod = m.prod ^ n
| 0       := by { rw [zero_nsmul, pow_zero], refl }
| (n + 1) :=
  by rw [add_nsmul, one_nsmul, pow_add, pow_one, prod_add, prod_nsmul n]

@[simp, to_additive] lemma prod_repeat (a : α) (n : ℕ) : (repeat a n).prod = a ^ n :=
by simp [repeat, list.prod_repeat]

@[to_additive]
lemma pow_count [decidable_eq α] (a : α) : a ^ s.count a = (s.filter (eq a)).prod :=
by rw [filter_eq, prod_repeat]

@[to_additive]
lemma prod_hom [comm_monoid β] (s : multiset α) {F : Type*} [monoid_hom_class F α β] (f : F) :
  (s.map f).prod = f s.prod :=
quotient.induction_on s $ λ l, by simp only [l.prod_hom f, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
lemma prod_hom' [comm_monoid β] (s : multiset ι) {F : Type*} [monoid_hom_class F α β] (f : F)
  (g : ι → α) : (s.map $ λ i, f $ g i).prod = f (s.map g).prod :=
by { convert (s.map g).prod_hom f, exact (map_map _ _ _).symm }

@[to_additive]
lemma prod_hom₂ [comm_monoid β] [comm_monoid γ] (s : multiset ι) (f : α → β → γ)
  (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → α) (f₂ : ι → β) :
  (s.map $ λ i, f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod :=
quotient.induction_on s $ λ l,
  by simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
lemma prod_hom_rel [comm_monoid β] (s : multiset ι) {r : α → β → Prop} {f : ι → α} {g : ι → β}
  (h₁ : r 1 1) (h₂ : ∀ ⦃a b c⦄, r b c → r (f a * b) (g a * c)) :
  r (s.map f).prod (s.map g).prod :=
quotient.induction_on s $ λ l,
  by simp only [l.prod_hom_rel h₁ h₂, quot_mk_to_coe, coe_map, coe_prod]

@[to_additive]
lemma prod_map_one : prod (m.map (λ i, (1 : α))) = 1 := by rw [map_const, prod_repeat, one_pow]

@[simp, to_additive]
lemma prod_map_mul : (m.map $ λ i, f i * g i).prod = (m.map f).prod * (m.map g).prod :=
m.prod_hom₂ (*) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
lemma prod_map_pow {n : ℕ} : (m.map $ λ i, f i ^ n).prod = (m.map f).prod ^ n :=
m.prod_hom' (pow_monoid_hom n : α →* α) f

@[to_additive]
lemma prod_map_prod_map (m : multiset β) (n : multiset γ) {f : β → γ → α} :
  prod (m.map $ λ a, prod $ n.map $ λ b, f a b) = prod (n.map $ λ b, prod $ m.map $ λ a, f a b) :=
multiset.induction_on m (by simp) (λ a m ih, by simp [ih])

@[to_additive]
lemma prod_induction (p : α → Prop) (s : multiset α) (p_mul : ∀ a b, p a → p b → p (a * b))
  (p_one : p 1) (p_s : ∀ a ∈ s, p a) :
  p s.prod :=
begin
  rw prod_eq_foldr,
  exact foldr_induction (*) (λ x y z, by simp [mul_left_comm]) 1 p s p_mul p_one p_s,
end

@[to_additive]
lemma prod_induction_nonempty (p : α → Prop) (p_mul : ∀ a b, p a → p b → p (a * b))
  (hs : s ≠ ∅) (p_s : ∀ a ∈ s, p a) :
  p s.prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { intro h,
    exfalso,
    simpa using h },
  intros a s hs hsa hpsa,
  rw prod_cons,
  by_cases hs_empty : s = ∅,
  { simp [hs_empty, hpsa a] },
  have hps : ∀ x, x ∈ s → p x, from λ x hxs, hpsa x (mem_cons_of_mem hxs),
  exact p_mul a s.prod (hpsa a (mem_cons_self a s)) (hs hs_empty hps),
end

lemma dvd_prod : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

lemma prod_dvd_prod_of_le (h : s ≤ t) : s.prod ∣ t.prod :=
begin
  obtain ⟨z, rfl⟩ := multiset.le_iff_exists_add.1 h,
  simp only [prod_add, dvd_mul_right],
end

end comm_monoid

lemma prod_dvd_prod_of_dvd [comm_monoid β] {S : multiset α} (g1 g2 : α → β)
  (h : ∀ a ∈ S, g1 a ∣ g2 a) :
  (multiset.map g1 S).prod ∣ (multiset.map g2 S).prod :=
begin
  apply multiset.induction_on' S, { simp },
  intros a T haS _ IH,
  simp [mul_dvd_mul (h a haS) IH]
end


section add_comm_monoid
variables [add_comm_monoid α]

/-- `multiset.sum`, the sum of the elements of a multiset, promoted to a morphism of
`add_comm_monoid`s. -/
def sum_add_monoid_hom : multiset α →+ α :=
{ to_fun := sum,
  map_zero' := sum_zero,
  map_add' := sum_add }

@[simp] lemma coe_sum_add_monoid_hom : (sum_add_monoid_hom : multiset α → α) = sum := rfl

end add_comm_monoid

section comm_monoid_with_zero
variables [comm_monoid_with_zero α]

lemma prod_eq_zero {s : multiset α} (h : (0 : α) ∈ s) : s.prod = 0 :=
begin
  rcases multiset.exists_cons_of_mem h with ⟨s', hs'⟩,
  simp [hs', multiset.prod_cons]
end

variables [no_zero_divisors α] [nontrivial α] {s : multiset α}

lemma prod_eq_zero_iff : s.prod = 0 ↔ (0 : α) ∈ s :=
quotient.induction_on s $ λ l, by { rw [quot_mk_to_coe, coe_prod], exact list.prod_eq_zero_iff }

lemma prod_ne_zero (h : (0 : α) ∉ s) : s.prod ≠ 0 := mt prod_eq_zero_iff.1 h

end comm_monoid_with_zero

section comm_group
variables [comm_group α] {m : multiset ι} {f g : ι → α}

@[simp, to_additive]
lemma prod_map_inv' : (m.map $ λ i, (f i)⁻¹).prod = (m.map f).prod ⁻¹ :=
by { convert (m.map f).prod_hom (comm_group.inv_monoid_hom : α →* α), rw map_map, refl }

@[simp, to_additive]
lemma prod_map_div : (m.map $ λ i, f i / g i).prod = (m.map f).prod / (m.map g).prod :=
m.prod_hom₂ (/) mul_div_mul_comm (div_one _) _ _

@[to_additive]
lemma prod_map_zpow {n : ℤ} : (m.map $ λ i, f i ^ n).prod = (m.map f).prod ^ n :=
by { convert (m.map f).prod_hom (zpow_group_hom _ : α →* α), rw map_map, refl }

@[simp] lemma coe_inv_monoid_hom : (comm_group.inv_monoid_hom : α → α) = has_inv.inv := rfl

@[simp, to_additive]
lemma prod_map_inv (m : multiset α) : (m.map has_inv.inv).prod = m.prod⁻¹ :=
m.prod_hom (comm_group.inv_monoid_hom : α →* α)

end comm_group

section comm_group_with_zero
variables [comm_group_with_zero α] {m : multiset ι} {f g : ι → α}

@[simp]
lemma prod_map_inv₀ : (m.map $ λ i, (f i)⁻¹).prod = (m.map f).prod ⁻¹ :=
by { convert (m.map f).prod_hom (inv_monoid_with_zero_hom : α →*₀ α), rw map_map, refl }

@[simp]
lemma prod_map_div₀ : (m.map $ λ i, f i / g i).prod = (m.map f).prod / (m.map g).prod :=
m.prod_hom₂ (/) (λ _ _ _ _, (div_mul_div_comm _ _ _ _).symm) (div_one _) _ _

lemma prod_map_zpow₀ {n : ℤ} : prod (m.map $ λ i, f i ^ n) = (m.map f).prod ^ n :=
by { convert (m.map f).prod_hom (zpow_group_hom _ : α →* α), rw map_map, refl }

end comm_group_with_zero

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α] {a : α} {s : multiset ι} {f : ι → α}

lemma _root_.commute.multiset_sum_right (s : multiset α) (a : α) (h : ∀ b ∈ s, commute a b) :
  commute a s.sum :=
begin
  induction s using quotient.induction_on,
  rw [quot_mk_to_coe, coe_sum],
  exact commute.list_sum_right _ _ h,
end

lemma _root_.commute.multiset_sum_left (s : multiset α) (b : α) (h : ∀ a ∈ s, commute a b) :
  commute s.sum b :=
(commute.multiset_sum_right _ _ $ λ a ha, (h _ ha).symm).symm

lemma sum_map_mul_left : sum (s.map (λ i, a * f i)) = a * sum (s.map f) :=
multiset.induction_on s (by simp) (λ i s ih, by simp [ih, mul_add])

lemma sum_map_mul_right : sum (s.map (λ i, f i * a)) = sum (s.map f) * a :=
multiset.induction_on s (by simp) (λ a s ih, by simp [ih, add_mul])

end non_unital_non_assoc_semiring

section semiring
variables [semiring α]

lemma dvd_sum {a : α} {s : multiset α} : (∀ x ∈ s, a ∣ x) → a ∣ s.sum :=
multiset.induction_on s (λ _, dvd_zero _)
  (λ x s ih h, by { rw sum_cons, exact dvd_add
    (h _ (mem_cons_self _ _)) (ih $ λ y hy, h _ $ mem_cons.2 $ or.inr hy) })

end semiring

/-! ### Order -/

section ordered_comm_monoid
variables [ordered_comm_monoid α] {s t : multiset α} {a : α}

@[to_additive sum_nonneg]
lemma one_le_prod_of_one_le : (∀ x ∈ s, (1 : α) ≤ x) → 1 ≤ s.prod :=
quotient.induction_on s $ λ l hl, by simpa using list.one_le_prod_of_one_le hl

@[to_additive]
lemma single_le_prod : (∀ x ∈ s, (1 : α) ≤ x) → ∀ x ∈ s, x ≤ s.prod :=
quotient.induction_on s $ λ l hl x hx, by simpa using list.single_le_prod hl x hx

@[to_additive sum_le_card_nsmul]
lemma prod_le_pow_card (s : multiset α) (n : α) (h : ∀ x ∈ s, x ≤ n) : s.prod ≤ n ^ s.card :=
begin
  induction s using quotient.induction_on,
  simpa using list.prod_le_pow_card _ _ h,
end

@[to_additive all_zero_of_le_zero_le_of_sum_eq_zero]
lemma all_one_of_le_one_le_of_prod_eq_one :
  (∀ x ∈ s, (1 : α) ≤ x) → s.prod = 1 → ∀ x ∈ s, x = (1 : α) :=
begin
  apply quotient.induction_on s,
  simp only [quot_mk_to_coe, coe_prod, mem_coe],
  exact λ l, list.all_one_of_le_one_le_of_prod_eq_one,
end

@[to_additive]
lemma prod_le_prod_of_rel_le (h : s.rel (≤) t) : s.prod ≤ t.prod :=
begin
  induction h with _ _ _ _ rh _ rt,
  { refl },
  { rw [prod_cons, prod_cons],
    exact mul_le_mul' rh rt }
end

@[to_additive]
lemma prod_map_le_prod (f : α → α) (h : ∀ x, x ∈ s → f x ≤ x) : (s.map f).prod ≤ s.prod :=
prod_le_prod_of_rel_le $ rel_map_left.2 $ rel_refl_of_refl_on h

@[to_additive]
lemma prod_le_sum_prod (f : α → α) (h : ∀ x, x ∈ s → x ≤ f x) : s.prod ≤ (s.map f).prod :=
@prod_map_le_prod αᵒᵈ _ _ f h

@[to_additive card_nsmul_le_sum]
lemma pow_card_le_prod (h : ∀ x ∈ s, a ≤ x) : a ^ s.card ≤ s.prod :=
by { rw [←multiset.prod_repeat, ←multiset.map_const], exact prod_map_le_prod _ h }

end ordered_comm_monoid

lemma prod_nonneg [ordered_comm_semiring α] {m : multiset α} (h : ∀ a ∈ m, (0 : α) ≤ a) :
  0 ≤ m.prod :=
begin
  revert h,
  refine m.induction_on _ _,
  { rintro -, rw prod_zero, exact zero_le_one },
  intros a s hs ih,
  rw prod_cons,
  exact mul_nonneg (ih _ $ mem_cons_self _ _) (hs $ λ a ha, ih _ $ mem_cons_of_mem ha),
end

@[to_additive]
lemma prod_eq_one_iff [canonically_ordered_monoid α] {m : multiset α} :
  m.prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
quotient.induction_on m $ λ l, by simpa using list.prod_eq_one_iff l

@[to_additive]
lemma le_prod_of_mem [canonically_ordered_monoid α] {m : multiset α} {a : α} (h : a ∈ m) :
  a ≤ m.prod :=
begin
  obtain ⟨m', rfl⟩ := exists_cons_of_mem h,
  rw [prod_cons],
  exact _root_.le_mul_right (le_refl a),
end

@[to_additive le_sum_of_subadditive_on_pred]
lemma le_prod_of_submultiplicative_on_pred [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (p : α → Prop) (h_one : f 1 = 1) (hp_one : p 1)
  (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
  (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : multiset α) (hps : ∀ a, a ∈ s → p a) :
  f s.prod ≤ (s.map f).prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { simp [le_of_eq h_one] },
  intros a s hs hpsa,
  have hps : ∀ x, x ∈ s → p x, from λ x hx, hpsa x (mem_cons_of_mem hx),
  have hp_prod : p s.prod, from prod_induction p s hp_mul hp_one hps,
  rw [prod_cons, map_cons, prod_cons],
  exact (h_mul a s.prod (hpsa a (mem_cons_self a s)) hp_prod).trans (mul_le_mul_left' (hs hps) _),
end

@[to_additive le_sum_of_subadditive]
lemma le_prod_of_submultiplicative [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (h_one : f 1 = 1) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : multiset α) :
  f s.prod ≤ (s.map f).prod :=
le_prod_of_submultiplicative_on_pred f (λ i, true) h_one trivial (λ x y _ _ , h_mul x y) (by simp)
  s (by simp)

@[to_additive le_sum_nonempty_of_subadditive_on_pred]
lemma le_prod_nonempty_of_submultiplicative_on_pred [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (p : α → Prop) (h_mul : ∀ a b, p a → p b → f (a * b) ≤ f a * f b)
  (hp_mul : ∀ a b, p a → p b → p (a * b)) (s : multiset α) (hs_nonempty : s ≠ ∅)
  (hs : ∀ a, a ∈ s → p a) :
  f s.prod ≤ (s.map f).prod :=
begin
  revert s,
  refine multiset.induction _ _,
  { intro h,
    exfalso,
    exact h rfl },
  rintros a s hs hsa_nonempty hsa_prop,
  rw [prod_cons, map_cons, prod_cons],
  by_cases hs_empty : s = ∅,
  { simp [hs_empty] },
  have hsa_restrict : (∀ x, x ∈ s → p x), from λ x hx, hsa_prop x (mem_cons_of_mem hx),
  have hp_sup : p s.prod,
    from prod_induction_nonempty p hp_mul hs_empty hsa_restrict,
  have hp_a : p a, from hsa_prop a (mem_cons_self a s),
  exact (h_mul a _ hp_a hp_sup).trans (mul_le_mul_left' (hs hs_empty hsa_restrict) _),
end

@[to_additive le_sum_nonempty_of_subadditive]
lemma le_prod_nonempty_of_submultiplicative [comm_monoid α] [ordered_comm_monoid β]
  (f : α → β) (h_mul : ∀ a b, f (a * b) ≤ f a * f b) (s : multiset α) (hs_nonempty : s ≠ ∅) :
  f s.prod ≤ (s.map f).prod :=
le_prod_nonempty_of_submultiplicative_on_pred f (λ i, true) (by simp [h_mul]) (by simp) s
  hs_nonempty (by simp)

@[simp] lemma sum_map_singleton (s : multiset α) : (s.map (λ a, ({a} : multiset α))).sum = s :=
multiset.induction_on s (by simp) (by simp [singleton_eq_cons])

lemma abs_sum_le_sum_abs [linear_ordered_add_comm_group α] {s : multiset α} :
  abs s.sum ≤ (s.map abs).sum :=
le_sum_of_subadditive _ abs_zero abs_add s

end multiset

@[to_additive]
lemma map_multiset_prod [comm_monoid α] [comm_monoid β] {F : Type*} [monoid_hom_class F α β]
  (f : F) (s : multiset α) : f s.prod = (s.map f).prod :=
(s.prod_hom f).symm

@[to_additive]
protected lemma monoid_hom.map_multiset_prod [comm_monoid α] [comm_monoid β] (f : α →* β)
  (s : multiset α) : f s.prod = (s.map f).prod :=
(s.prod_hom f).symm
