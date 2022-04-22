/-
Copyright (c) 2022 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import algebra.big_operators.order
import data.dfinsupp.order
import data.finsupp.order
import data.nat.interval
import data.set.intervals.ord_connected
import data.sigma.order
import data.sum.order
import order.grade
import .mathlib

/-!
# Graded preorders

In this file, we define graded preorders, also known as ranked preorders. The standard approach,
followed in e.g. ARP p.22, Stanley p. 99, Anderson p.14, is to define graded preorders as those
where all flags (maximal chains) have the same finite length - this then allows one to construct a
grade function. In practice, using grade functions directly is much easier. As such, we follow
Engel's p.7 approach of having the grade function as an intrinsic property. We prove the
correspondence between these definitions in [Todo(Vi): Actually prove this].

We define as many of the prerequisites for polytopes as we can, except for those that involve the
notion of flags. These are separated into `flag.lean`.

## Main definitions

* `grade_order`: graded preorders.
* `polytope.path`: a path between two elements in a graph.
* `polytope.total_connected`: connectedness of a bounded poset – see remark on nomenclature.
* `polytope.strong_connected`: strong connectedness of a bounded poset.

## Main results

* `graded.ex_unique_of_grade`: graded linear orders have a unique element of each possible grade.
-/

open finset function nat
open_locale big_operators

variables {ι 𝕆 α β : Type*} {σ : ι → Type*}

section preorder
variables [preorder α]

section order_bot
variables [order_bot α] [grade_order ℕ α] {a b : α}

/-- The grade ℕ as a strict order homomorphism. -/
def grade_order.rel_hom (α : Type*) [preorder α] [order_bot α] [grade_order ℕ α] :
  @rel_hom α ℕ (<) (<) :=
⟨_, grade_strict_mono⟩

end order_bot
end preorder

section partial_order
variables [partial_order α]

section order_bot
variables [order_bot α] [grade_min_order ℕ α] {a b : α}

/-- The grade ℕ as an order homomorphism. -/
def grade_order.order_hom : α →o ℕ := ⟨grade _, grade_mono⟩

/-- A closed non-empty interval of a graded poset is a graded poset. -/
def set.Icc.graded (h : a ≤ b) : grade_min_order ℕ (set.Icc a b) :=
{ grade := λ x, grade ℕ x.val - grade ℕ a,
  grade_strict_mono := λ x y h,
    nat.sub_mono_left_strict (grade_mono x.prop.left) (grade_strict_mono h),
  is_min_grade := λ c hc, begin
    letI := set.Icc.order_bot h,
    rw hc.eq_bot,
    convert is_min_bot,
    exact tsub_self _,
  end,
  covby_grade := begin
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨hxy, hcov⟩,
    sorry
    -- rw [←(covby.grade ⟨hxy, λ c ha hb, _⟩ : (grade ℕ x + 1 = grade ℕ y)), nat.sub_add_comm],
    -- exact grade_mono hx.left,
    -- simp at hcov, -- Todo(Vi): Remove this `simp`.
    -- exact hcov _ (hx.1.trans ha.le) (hb.le.trans hy.2) ha hb,
  end }

/-- An element has grade `0` iff it is the bottom element. -/
@[simp]
lemma grade_eq_zero_iff (a : α) : grade ℕ a = 0 ↔ a = ⊥ :=
begin
  refine ⟨λ h, _, _⟩,
  { by_contra ha,
    exact (h.le.trans grade_bot.ge).not_lt (grade_strict_mono $ bot_lt_iff_ne_bot.2 ha) },
  rintro rfl,
  exact grade_bot
end

end order_bot

section bounded_order
variables [bounded_order α] [grade_order ℕ α] {a b : α}

lemma grade_le_grade_top (a : α) : grade ℕ a ≤ grade ℕ (⊤ : α) := grade_mono le_top

lemma has_lt.lt.grade_lt_grade_top (h : a < b) : grade ℕ a < grade ℕ (⊤ : α) :=
grade_strict_mono $ h.trans_le le_top

@[simp] lemma grade_lt_grade_top_of_nonempty (h : (set.Ioi a).nonempty) :
  grade ℕ a < grade ℕ (⊤ : α) :=
has_lt.lt.grade_lt_grade_top h.some_mem

open order_dual

/-- An element has the top grade iff it is the top element. -/
@[simp] lemma eq_grade_top_iff_eq_top (a : α) : grade ℕ a = grade ℕ (⊤ : α) ↔ a = ⊤ :=
grade_strict_mono.apply_eq_top_iff

end bounded_order
end partial_order

section linear_order
variables [linear_order α]

section order_bot
variables [order_bot α] [grade_order ℕ α] {a b : α}

/-- `grade` as an order embedding into `ℕ` for a linear order `α`. -/
def order_embedding.grade : α ↪o ℕ := ⟨⟨_, grade_injective⟩, λ _ _, grade_le_grade_iff⟩

/-- The set of grades in a linear order has no gaps. -/
private lemma grade_ioo_lin {a b : α} {m n r : ℕ} (ha : grade ℕ a = m) (hb : grade ℕ b = n)
  (hrl : m < r) (hrr : r < n) : ∃ (s ∈ set.Ioo m n) (c : α), grade ℕ c = s :=
begin
  subst ha, subst hb,
  sorry
  -- obtain ⟨_, hac, hcb⟩ := exists_lt_lt_of_not_covby (grade_lt_grade_iff.1 (lt_trans hrl hrr))
  --   (λ h, (λ ⟨_, hmn⟩, hmn hrl hrr : ¬ _ ⋖ _)
  --   h.grade _),
  -- exact ⟨_, ⟨grade_strict_mono hac, grade_strict_mono hcb⟩, _, rfl⟩
end

variables [locally_finite_order α]

lemma card_Iio_eq_grade (a : α) : (Iio a).card = grade ℕ a := sorry
lemma card_Iic_eq_grade_add_one (a : α) : (Iic a).card = grade ℕ a + 1 := sorry
lemma card_Ico_eq_grade_sub_grade (a b : α) : (Ico a b).card = grade ℕ b - grade ℕ a :=  sorry
lemma card_Ioc_eq_grade_sub_grade (a b : α) : (Ioc a b).card = grade ℕ b - grade ℕ a := sorry

end order_bot

section bounded_order
variables [bounded_order α] [grade_min_order ℕ α]

/-- `grade` is an order embedding into `fin` for linearly ordered `α` with a top element. -/
def order_embedding.grade_fin : α ↪o fin (grade ℕ ⊤ + 1) :=
{ to_fun := λ x, ⟨grade ℕ x, by { rw nat.lt_add_one_iff, exact grade_le_grade_top _ }⟩,
  inj' := λ a b hab, grade_injective (subtype.mk.inj hab),
  map_rel_iff' := λ _ _, fin.le_iff_coe_le_coe.trans grade_le_grade_iff }

/-- A graded linear order has an element of grade `j` when `j ≤ grade ⊤`. This is generalized to a
partial order in `ex_of_grade`. -/
lemma ex_of_grade_lin {j : ℕ} (hj : j ≤ grade ℕ (⊤ : α)) : ∃ a : α, grade ℕ a = j :=
have hj' : grade ℕ (⊥ : α) ≤ j := by simp [grade_bot],
let S := {g | ∃ a : α, grade ℕ a = g} in
suffices h : _,
from @nat.all_icc_of_ex_ioo S h (grade ℕ (⊥ : α)) (grade ℕ (⊤ : α)) _ ⟨⊥, rfl⟩ ⟨⊤, rfl⟩ hj' hj,
begin
  rintro _ _ _ ⟨_, ha⟩ ⟨_, hb⟩ hac hcb,
  obtain ⟨_, hw, hw'⟩ := grade_ioo_lin ha hb hac hcb,
  exact ⟨_, hw', hw⟩,
end

/-- A graded linear order has a unique element of grade `j` when `j ≤ grade ⊤`. -/
lemma ex_unique_of_grade {j : ℕ} (hj : j ≤ grade ℕ (⊤ : α)) : ∃! a : α, grade ℕ a = j :=
by { cases ex_of_grade_lin hj with _ ha, exact ⟨_, ha, λ _ hb, grade_injective (by rw [ha, hb])⟩ }

end bounded_order
end linear_order

/-! ### Instances -/

/-! #### `subsingleton` -/

namespace subsingleton
variables (α) [subsingleton α] [preorder α]

/-- An order with one element is a graded order, aka a nullitope. -/
def to_grade_min_order : grade_min_order ℕ α :=
{ grade := λ _, 0,
  grade_strict_mono := subsingleton.strict_mono _,
  covby_grade := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim,
  is_min_grade := λ _ _, is_min_bot }

variables {α}

protected lemma grade [grade_min_order ℕ α] (a : α) : grade ℕ a = 0 :=
((subsingleton.is_min _).grade _).eq_bot

end subsingleton

/-! #### Simple orders -/

section is_simple_order
variables (α)

/-- A simple order is a graded order, aka a point. -/
def is_simple_order.to_grade_order [decidable_eq α] [partial_order α] [bounded_order α]
  [is_simple_order α] :
  grade_min_order ℕ α :=
{ grade := λ a, if a = ⊥ then 0 else 1,
  grade_strict_mono := λ a b h, begin
    convert zero_lt_one,
    { exact if_pos (is_simple_order.eq_bot_of_lt h) },
    { exact if_neg (ne_bot_of_lt h) },
    { apply_instance }
  end,
  covby_grade := λ a b h, nat.covby_iff_succ_eq.2 begin
    convert zero_add 1,
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) },
    { exact if_neg (ne_bot_of_lt h.1) }
  end,
  is_min_grade := λ a ha, by { rw [if_pos ha.eq_bot], exact is_min_bot } }

variables {α} [partial_order α] [bounded_order α] [is_simple_order α] [grade_min_order ℕ α]

lemma is_simple_order.grade_top : grade ℕ (⊤ : α) = 1 :=
by { rw [←(bot_covby_top.grade _).succ_eq, grade_bot], refl, apply_instance }

lemma is_simple_order.grade_le_one (a : α) : grade ℕ a ≤ 1 :=
by { convert grade_le_grade_top _, rw is_simple_order.grade_top }

end is_simple_order

/-! #### List -/

namespace list

lemma sublist_singleton : Π {l : list α} {a : α}, l <+ [a] → l = nil ∨ l = [a]
| _ _ (sublist.cons  _ _  _ _ ) := by apply or.inl; rwa ←sublist_nil_iff_eq_nil
| _ _ (sublist.cons2 a [] _ hl) := begin
  rw sublist_nil_iff_eq_nil at hl,
  rw hl,
  exact or.inr rfl
end

lemma sublist.singleton_iff (l : list α) (a : α) : l <+ [a] ↔ l = nil ∨ l = [a] :=
⟨sublist_singleton, begin
  rintros (h | h),
  all_goals { induction h },
    { exact sublist.cons _ _ _ (sublist.refl _) },
    { exact sublist.refl _ }
end⟩

end list

/-! #### Multiset -/

namespace multiset
variables {s t : multiset α} {a : α}

@[simp] lemma cons_zero (a : α) : a ::ₘ 0 = {a} := rfl

lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

lemma lt_singleton : s < {a} ↔ s = 0 :=
begin
  rcases s with ⟨s⟩,
  change (↑s < ↑[a]) ↔ ↑s = _,
  simp_rw [coe_eq_zero, lt_iff_cons_le, cons_coe, coe_le],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨w, w', hw'w, hw'a⟩,
    rw list.sublist.singleton_iff at hw'a,
    obtain rfl | rfl := hw'a,
    { rw list.nil_perm at hw'w, contradiction },
    { rw [list.singleton_perm, list.cons.inj_eq] at hw'w,
      rw hw'w.right } },
  { use a,
    induction h,
    refl }
end

lemma covby_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m := ⟨lt_cons_self _ _, begin
  simp_rw lt_iff_cons_le,
  rintros m' ⟨b, hbm'⟩ ⟨c, hcm'⟩,
  apply @irrefl _ (<) _ m,
  have h := lt_of_le_of_lt hbm' (lt_cons_self _ c),
  replace h := lt_of_lt_of_le h hcm',
  clear hbm' hcm',
  induction m using multiset.induction with d m hm,
  { rw [cons_zero a, lt_singleton] at h,
    exact (cons_ne_zero h).elim },
  { simp_rw cons_swap _ d at h,
    rw cons_lt_cons_iff at h ⊢,
    exact hm h }
end⟩

lemma _root_.covby.exists_cons_multiset (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
(lt_iff_cons_le.1 h.lt).imp $ λ a ha, ha.eq_of_not_gt $ h.2 $ lt_cons_self _ _

lemma _root_.covby.card_multiset (h : s ⋖ t) : s.card ⋖ t.card :=
begin
  obtain ⟨a, rfl⟩ := h.exists_cons_multiset,
  rw card_cons,
  exact order.covby_succ _,
end

lemma card_strict_mono : strict_mono (card : multiset α → ℕ) := λ _ _, card_lt_of_lt

instance (α : Type*) : grade_min_order ℕ (multiset α) :=
{ grade := card,
  grade_strict_mono := card_strict_mono,
  covby_grade := λ s t, covby.card_multiset,
  is_min_grade := λ s hs, by { rw hs.eq_bot, exact is_min_bot } }

@[simp] protected lemma grade (m : multiset α) : grade ℕ m = m.card := rfl

end multiset

/-! #### Finset -/

namespace finset
variables {s t : finset α}

-- golf using `image_covby_iff`
@[simp] lemma val_covby_iff : s.1 ⋖ t.1 ↔ s ⋖ t :=
begin
  split;
  rintro ⟨hlt, no_intermediate⟩;
  split;
  simp at *;
  rwa [←val_lt_iff] at *;
  intros c hsc hct;
  simp at *;
  rw [←val_lt_iff] at *,
  { apply @no_intermediate c.val; assumption },
  { apply @no_intermediate ⟨c, multiset.nodup_of_le hct.1 t.nodup⟩;
    rw ←val_lt_iff;
    assumption }
end

lemma _root_.covby.card_finset (h : s ⋖ t) : s.card ⋖ t.card := (val_covby_iff.2 h).card_multiset

lemma _root_.is_min.eq_empty : is_min s → s = ∅ := is_min.eq_bot

lemma card_strict_mono : strict_mono (card : finset α → ℕ) := λ _ _, card_lt_card

instance (α : Type*) : grade_min_order ℕ (finset α) :=
{ grade := card,
  grade_strict_mono := card_strict_mono,
  covby_grade := λ _ _, covby.card_finset,
  is_min_grade := λ s hs, by { rw hs.eq_empty, exact is_min_bot } }

@[simp] protected lemma grade (s : finset α) : grade ℕ s = s.card := rfl

end finset

/-! #### Finitely supported functions to a graded order -/

namespace finsupp
variables [canonically_ordered_add_monoid α] [canonically_ordered_add_monoid β] {f g : ι →₀ α}
  {m : ι → α → β}

lemma support_mono : monotone (support : (ι →₀ β) → finset ι) :=
λ f g h i hi, by { rw [mem_support_iff, ←bot_eq_zero] at ⊢ hi, exact ne_bot_of_le_ne_bot hi (h i) }

lemma sum_le_sum (h : f ≤ g) (hm : ∀ i, monotone (m i)) : f.sum m ≤ g.sum m :=
(finset.sum_le_sum_of_subset_of_nonneg (support_mono h) $ λ _ _ _, zero_le _).trans $
  sum_le_sum $ λ i _, hm i $ h i

instance [grade_order ℕ β] : grade_order ℕ (α →₀ β) :=
{ grade := λ f, f.sum (λ _, grade ℕ),
  grade_strict_mono := λ a b, begin
    sorry
  end,
  covby_grade := λ a b hab, begin
    sorry
  end }

instance [grade_min_order ℕ β] : grade_min_order ℕ (α →₀ β) :=
{ is_min_grade := sorry,
  ..finsupp.grade_order }

variables [grade_order ℕ β]

@[simp] protected lemma grade (f : α →₀ β) : grade ℕ f = f.sum (λ _, grade ℕ) := rfl

end finsupp

/-! #### Finitely supported dependent functions to graded orders -/

namespace dfinsupp
variables [decidable_eq ι] [Π i, canonically_ordered_add_monoid (σ i)]
  [Π i (x : σ i), decidable (x ≠ 0)] [canonically_ordered_add_monoid α] {f g : Π₀ i, σ i}
  {m : Π i, σ i → α}

lemma support_mono : monotone (support : (Π₀ i, σ i) → finset ι) :=
λ f g h i hi, by { rw [mem_support_iff, ←bot_eq_zero] at ⊢ hi, exact ne_bot_of_le_ne_bot hi (h i) }

lemma sum_le_sum (h : f ≤ g) (hm : ∀ i, monotone (m i)) : f.sum m ≤ g.sum m :=
(finset.sum_le_sum_of_subset_of_nonneg (support_mono h) $ λ _ _ _, zero_le _).trans $
  sum_le_sum $ λ i _, hm i $ h i

instance [Π i, grade_order ℕ (σ i)] :
  grade_order ℕ (Π₀ i, σ i) :=
{ grade := λ f, f.sum (λ _, grade ℕ),
  grade_strict_mono := λ a b, sorry,
  covby_grade := λ a b hab, begin
    sorry
  end }

instance [Π i, grade_min_order ℕ (σ i)] : grade_min_order ℕ (Π₀ i, σ i) :=
{ is_min_grade := sorry,
  ..dfinsupp.grade_order }

variables [Π i, grade_order ℕ (σ i)]

@[simp] protected lemma grade (f : Π₀ i, σ i) : grade ℕ f = f.sum (λ i, grade ℕ) := rfl

end dfinsupp

/-! #### Product of two graded orders -/

section
variables [has_lt α] [comm_group α] [covariant_class α α (*) (<)] {a b c : α}

@[to_additive] lemma covby.mul_left (h : b ⋖ c) (a : α) : a * b ⋖ a * c :=
⟨mul_lt_mul_left' h.lt _, λ d hb hc,
  h.2 (lt_div_iff_mul_lt.2 $ by rwa mul_comm) (_root_.div_lt_iff_lt_mul'.2 hc)⟩

@[to_additive] lemma covby.mul_right (h : b ⋖ c) (a : α) : b * a ⋖ c * a :=
⟨mul_lt_mul_right' h.lt _, λ d hb hc,
  h.2 (lt_div_iff_mul_lt.2 hb) (_root_.div_lt_iff_lt_mul'.2 $ by rwa mul_comm)⟩

end

section
variables [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
 [covariant_class α α (+) (<)] [contravariant_class α α (+) (≤)] {a b c : α}

lemma covby.add_left' (h : b ⋖ c) (a : α) : a + b ⋖ a + c :=
⟨add_lt_add_left h.lt _, λ d hb hc,
  h.2 (lt_tsub_iff_left.2 hb) ((tsub_lt_iff_left $ le_self_add.trans hb.le).2 hc)⟩

lemma covby.add_right' (h : b ⋖ c) (a : α) : b + a ⋖ c + a :=
⟨add_lt_add_right h.lt _, λ d hb hc,
  h.2 (lt_tsub_iff_right.2 hb) ((tsub_lt_iff_right $ le_add_self.trans hb.le).2 hc)⟩

end

namespace prod
variables [partial_order α] [order_bot α] [partial_order β] [order_bot β] {a a' : α} {b b' : β}
  {x y : α × β}

@[simp] lemma swap_le_swap_iff : x.swap ≤ y.swap ↔ x ≤ y := and_comm _ _

@[simp] lemma swap_lt_swap_iff : x.swap < y.swap ↔ x < y :=
lt_iff_lt_of_le_iff_le' swap_le_swap_iff swap_le_swap_iff

@[simp] lemma swap_covby_swap_iff : x.swap ⋖ y.swap ↔ x ⋖ y :=
apply_covby_apply_iff (order_iso.prod_comm : α × β ≃o β × α)

lemma mk_le_mk_iff_left : (a, b) ≤ (a', b) ↔ a ≤ a' := and_iff_left le_rfl
lemma mk_le_mk_iff_right : (a, b) ≤ (a, b') ↔ b ≤ b' := and_iff_right le_rfl

lemma mk_lt_mk_iff_left : (a, b) < (a', b) ↔ a < a' :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

lemma mk_lt_mk_iff_right : (a, b) < (a, b') ↔ b < b' :=
lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

lemma fst_eq_or_snd_eq_of_covby : (a, b) ⋖ (a', b') → a = a' ∨ b = b' :=
begin
  contrapose,
  push_neg,
  rintros ⟨ha, hb⟩ hcov,
  have h₁ : (a, b) < (a', b)   := mk_lt_mk.mpr (or.inl ⟨ha.le_iff_lt.mp hcov.1.1.1, le_rfl⟩),
  have h₂ : (a', b) < (a', b') := mk_lt_mk.mpr (or.inr ⟨le_rfl, hb.le_iff_lt.mp hcov.1.1.2⟩),
  exact hcov.2 h₁ h₂
end

lemma mk_covby_mk_iff_left : (a, b) ⋖ (a', b) ↔ a ⋖ a' :=
begin
  split;
  rintro ⟨hcov_left, hcov_right⟩;
  split;
  [ { skip },
    { intros c hac hca',
      apply @hcov_right (c, b) },
    { skip },
    { rintros ⟨c₁, c₂⟩ h h',
      apply @hcov_right c₁;
      have : c₂ = b := le_antisymm h'.1.2 h.1.2;
      rw this at *, } ];
  rw mk_lt_mk_iff_left at *;
  assumption,
end

lemma mk_covby_mk_iff_right : (a, b) ⋖ (a, b') ↔ b ⋖ b' :=
swap_covby_swap_iff.trans mk_covby_mk_iff_left

lemma mk_covby_mk_iff : (a, b) ⋖ (a', b') ↔ a ⋖ a' ∧ b = b' ∨ a = a' ∧ b ⋖ b' :=
begin
  split,
  { intro hcov,
    cases fst_eq_or_snd_eq_of_covby hcov with heq heq;
    rw [heq, eq_self_iff_true] at *,
    { rw [mk_covby_mk_iff_right] at *,
      tauto },
    { rw mk_covby_mk_iff_left at *,
      tauto } },
  { intro h,
    rcases h with ⟨acov, beq⟩ | ⟨aeq, bcov⟩,
    { rw beq at *,
      exact mk_covby_mk_iff_left.mpr acov },
    { rw aeq at *,
      exact mk_covby_mk_iff_right.mpr bcov } }
end

lemma _root_.is_min.prod_mk (ha : is_min a) (hb : is_min b) : is_min (a, b) :=
λ c hc, ⟨ha hc.1, hb hc.2⟩

lemma _root_.is_min.fst (hx : is_min x) : is_min x.1 :=
λ c hc, (hx ((and_iff_left le_rfl).2 hc : (c, x.2) ≤ x)).1

lemma _root_.is_min.snd (hx : is_min x) : is_min x.2 :=
λ c hc, (hx ((and_iff_right le_rfl).2 hc : (x.1, c) ≤ x)).2

lemma is_min_iff : is_min x ↔ is_min x.1 ∧ is_min x.2 :=
⟨λ hx, ⟨hx.fst, hx.snd⟩, λ h, h.1.prod_mk h.2⟩

instance [grade_order ℕ α] [grade_order ℕ β] : grade_order ℕ (α × β) :=
{ grade := λ a, grade ℕ a.1 + grade ℕ a.2,
  grade_strict_mono := λ a b h, begin
    obtain h | h := prod.lt_iff.1 h,
    { exact add_lt_add_of_lt_of_le (grade_strict_mono h.1) (grade_mono h.2) },
    { exact add_lt_add_of_le_of_lt (grade_mono h.1) (grade_strict_mono h.2) }
  end,
  covby_grade := λ a b h, match mk_covby_mk_iff.1 h with
    | or.inl ⟨h₁, h₂⟩ := by { rw h₂, exact (h₁.grade _).add_right' _ }
    | or.inr ⟨h₁, h₂⟩ := by { rw h₁, exact (h₂.grade _).add_left' _ }
    end }

instance [grade_min_order ℕ α] [grade_min_order ℕ β] : grade_min_order ℕ (α × β) :=
{ is_min_grade := λ a ha, begin
    change is_min (_ + _),
    rw [(ha.fst.grade _).eq_bot, (ha.snd.grade _).eq_bot],
    exact is_min_bot,
  end,
  ..prod.grade_order }

variables [grade_order ℕ α] [grade_order ℕ β]

@[simp] protected lemma grade (a : α × β) : grade ℕ a = grade ℕ a.1 + grade ℕ a.2 := rfl
lemma grade_mk (a : α) (b : β) : grade ℕ (a, b) = grade ℕ a + grade ℕ b := rfl

end prod

/-! #### Finite product of graded orders -/

namespace pi
variables [fintype ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)]

instance [Π i, grade_order ℕ (σ i)] : grade_order ℕ (Π i, σ i) :=
{ grade := λ f, ∑ i, grade ℕ (f i),
  grade_strict_mono := λ a b h, begin
    rw pi.lt_def at h,
    obtain ⟨h, i, hi⟩ := h,
    sorry
  end,
  covby_grade := sorry }

instance [Π i, grade_min_order ℕ (σ i)] : grade_min_order ℕ (Π i, σ i) :=
{ is_min_grade := λ a ha, begin
    change is_min (finset.sum _ _),
    rw sum_eq_zero (λ _ _, _),
    exact is_min_bot,
    refine (is_min.grade _ _).eq_bot,
    sorry
  end
  ..pi.grade_order }

variables [Π i, grade_order ℕ (σ i)]

@[simp] protected lemma grade (f : Π i, σ i) : grade ℕ f = ∑ i, grade ℕ (f i) := rfl

end pi

/-! #### Lexicographical sum of two graded orders -/

namespace sum
variables [preorder 𝕆] [preorder α] [preorder β]

instance [grade_order 𝕆 α] [grade_order 𝕆 β] : grade_order 𝕆 (α ⊕ β) :=
{ grade := elim (grade 𝕆) (grade 𝕆),
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

instance [grade_min_order ℕ α] [grade_min_order ℕ β] : grade_min_order 𝕆 (α ⊕ₗ β) :=
{ grade := λ a, a.elim (grade ℕ) (λ b, grade ℕ (⊤ : α) + grade ℕ b),
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

variables (a : α) (b : β) [grade_order ℕ α] [grade_order ℕ β]

@[simp] lemma grade_inl : grade 𝕆 (sum.inl a : α ⊕ₗ β) = grade 𝕆 a := rfl
@[simp] lemma grade_inr : grade 𝕆 (sum.inr b : α ⊕ₗ β) = grade 𝕆 b := rfl

end sum

/-! #### Lexicographical sum of two graded orders -/

namespace sum.lex
variables [preorder α] [bounded_order α] [preorder β] [order_bot β]

instance [grade_order ℕ α] [grade_order ℕ β] : grade_order ℕ (α ⊕ₗ β) :=
{ grade := elim (grade ℕ) (λ b, grade ℕ (⊤ : α) + grade ℕ b),
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

instance [grade_min_order ℕ α] [grade_min_order ℕ β] : grade_min_order ℕ (α ⊕ₗ β) :=
{ grade := λ a, a.elim (grade ℕ) (λ b, grade ℕ (⊤ : α) + grade ℕ b),
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

variables (a : α) (b : β) [grade_order ℕ α] [grade_order ℕ β]

@[simp] protected lemma grade_inlₗ : grade ℕ (sum.inlₗ a : α ⊕ₗ β) = grade ℕ a := rfl
@[simp] protected lemma grade_inrₗ : grade ℕ (sum.inrₗ b : α ⊕ₗ β) = grade (⊤ : α) + grade ℕ b := rfl

end sum.lex

/-! #### Finite lexicographical sum of graded orders -/

namespace sigma.lex
variables (ι σ) [fintype ι] [linear_order ι] [order_bot ι] [Π i, preorder (σ i)]
  [Π i, order_bot (σ i)] [Π i, grade_order ℕ (σ i)]

/-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
instance grade_order : grade_order ℕ (Σ i, σ i) :=
{ grade := sorry,
  grade_bot := sorry,
  strict_mono := λ a b h, sorry,
  covby_grade := sorry }

variables {ι σ}

--@[simp] protected lemma grade (f : Σ i, σ i) : grade f = sorry := rfl

end sigma.lex

namespace psigma.lex
variables (ι σ) [fintype ι] [linear_order ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)]
  [Π i, grade_order ℕ (σ i)]

open_locale lex

/-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
def grade_order : grade_order ℕ (Σ' i, σ i) :=
{ grade := sorry,
  grade_bot := sorry,
  strict_mono := λ a b h, sorry,
  covby_grade := sorry }

--localized "attribute [instance] psigma.lex.grade_order" in lex

variables {ι σ}

--@[simp] protected lemma grade (f : Σ' i, σ i) : grade f = sorry := rfl

end psigma.lex

/-! #### `with_bot`, `with_top` -/

namespace with_bot
variables (α) [preorder α] [order_bot α] [grade_order ℕ α]

instance : grade_order ℕ (with_bot α) :=
{ grade := @with_bot.rec_bot_coe α (λ _, ℕ) 0 (λ a, grade ℕ a + 1),
  grade_bot := rfl,
  strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact nat.zero_lt_succ _ },
    { exact (not_lt_bot h).elim },
    { exact nat.succ_lt_succ (grade_order.strict_mono (with_bot.some_lt_some.1 h)) }
  end,
  covby_grade := λ x y h, begin
    sorry
  end }

variables {α}

@[simp] protected lemma grade_coe (a : α) : grade (a : with_bot α) = grade ℕ a + 1 := rfl

end with_bot

namespace with_top
variables (α) [partial_order α] [bounded_order α] [grade_order ℕ α]

instance : grade_order ℕ (with_top α) :=
{ grade := @with_top.rec_top_coe α (λ _, ℕ) (grade (⊤ : α) + 1) grade,
  grade_bot := grade_bot,
  strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact (not_le_of_lt h le_top).elim },
    { exact nat.lt_succ_of_le (grade_le_grade_top _) },
    { exact grade_order.strict_mono (with_top.some_lt_some.1 h) }
  end,
  covby_grade := λ x y h, begin
    sorry
  end }

variables {α}

@[simp] protected lemma grade_coe (a : α) : grade (a : with_top α) = grade ℕ a := rfl
@[simp] protected lemma grade_top : grade (⊤ : with_top α) = grade (⊤ : α) + 1 := rfl

end with_top
