/-
Copyright (c) 2022 Grayson Burton, Yaël Dillies, Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import data.nat.interval
import data.set.intervals.ord_connected
import data.sigma.order
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

## Main results

* `graded.ex_unique_of_grade`: graded linear orders have a unique element of each possible grade.
-/

open finset function nat
open_locale big_operators

variables {ι 𝕆 α β : Type*} {σ : ι → Type*}

section partial_order
variables [partial_order α]

section order_bot
variables [order_bot α] [grade_min_order ℕ α] {a b : α}

/-- A closed non-empty interval of a graded order is a graded order. -/
def set.Icc.graded : grade_min_order ℕ (set.Icc a b) :=
{ grade := λ x, grade ℕ x.val - grade ℕ a,
  grade_strict_mono := λ x y h, tsub_lt_tsub_right_of_le (grade_mono x.2.1) $ grade_strict_mono h,
  is_min_grade := λ c hc, begin
    letI := set.Icc.order_bot (c.2.1.trans c.2.2),
    rw hc.eq_bot,
    convert is_min_bot,
    exact tsub_self _,
  end,
  covby_grade := λ x y hxy, begin
    have : x.1 ⋖ y.1 := sorry,
    exact (this.grade _).tsub_right (grade_mono x.2.1),
  end }

@[simp] lemma grade_eq_zero_iff (a : α) : grade ℕ a = 0 ↔ a = ⊥ :=
by simp_rw [←bot_eq_zero, ←is_min_iff_eq_bot, is_min_grade_iff]

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
  obtain ⟨_, hac, hcb⟩ := exists_lt_lt_of_not_covby (grade_lt_grade_iff.1 $ hrl.trans  hrr)
    (λ h, (h.grade _).2 hrl hrr),
  exact ⟨_, ⟨grade_strict_mono hac, grade_strict_mono hcb⟩, _, rfl⟩,
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
  inj' := λ a b hab, grade_injective (fin.coe_inj.2 hab),
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
variables [subsingleton α] [preorder α]

/-- An order with one element is a graded order, aka a nullitope. -/
def to_grade_min_order : grade_min_order ℕ α :=
{ grade := λ _, 0,
  grade_strict_mono := subsingleton.strict_mono _,
  covby_grade := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim,
  is_min_grade := λ _ _, is_min_bot }

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
    all_goals { apply_instance },
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

/- We could put either the prefix, suffix, infix, sublist, subset order on `list` and show that it
is graded by `list.length` -/

/-! #### Multiset -/

namespace multiset
variables {s t : multiset α} {a : α}

instance : grade_min_order ℕ (multiset α) :=
{ grade := card,
  grade_strict_mono := card_strict_mono,
  covby_grade := λ s t, covby.card_multiset,
  is_min_grade := λ s hs, by { rw hs.eq_bot, exact is_min_bot } }

@[simp] protected lemma grade (m : multiset α) : grade ℕ m = m.card := rfl

end multiset

/-! #### Finset -/

namespace finset
variables {s t : finset α}

instance grade_min_order_multiset : grade_min_order (multiset α) (finset α) :=
{ grade := val,
  grade_strict_mono := val_strict_mono,
  covby_grade := λ _ _, covby.finset_val,
  is_min_grade := λ s hs, by { rw hs.eq_empty, exact is_min_bot } }

@[simp] lemma grade_multiset (s : finset α) : grade (multiset α) s = s.1 := rfl

instance grade_min_order_nat : grade_min_order ℕ (finset α) :=
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

instance [Π i, grade_order ℕ (σ i)] : grade_order ℕ (Π₀ i, σ i) :=
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

namespace prod
variables [partial_order α] [order_bot α] [partial_order β] [order_bot β] {a a' : α} {b b' : β}
  {x y : α × β}

instance [grade_order ℕ α] [grade_order ℕ β] : grade_order ℕ (α × β) :=
{ grade := λ a, grade ℕ a.1 + grade ℕ a.2,
  grade_strict_mono := λ a b h, begin
    obtain h | h := prod.lt_iff.1 h,
    { exact add_lt_add_of_lt_of_le (grade_strict_mono h.1) (grade_mono h.2) },
    { exact add_lt_add_of_le_of_lt (grade_mono h.1) (grade_strict_mono h.2) }
  end,
  covby_grade := λ a b h, match mk_covby_mk_iff.1 h with
    | or.inl ⟨h₁, h₂⟩ := by { rw h₂, exact (h₁.grade _).add_right' _ }
    | or.inr ⟨h₁, h₂⟩ := by { rw h₂, exact (h₁.grade _).add_left' _ }
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
    dsimp [grade_order.grade],
    rw sum_eq_zero (λ _ _, _),
    exact is_min_bot,
    exact ((ha.apply' _).grade _).eq_bot,
  end
  ..pi.grade_order }

variables [Π i, grade_order ℕ (σ i)]

@[simp] protected lemma grade (f : Π i, σ i) : grade ℕ f = ∑ i, grade ℕ (f i) := rfl

end pi

/-! #### Lexicographical sum of two graded orders -/

section
variables [preorder α] [preorder β]

open sum

/-- `sum.inl` as an order embedding. -/
@[simps] protected def order_embedding.inl : α ↪o α ⊕ β :=
{ to_fun := inl,
  inj' := inl_injective,
  map_rel_iff' := λ _ _, inl_le_inl_iff }

/-- `sum.inr` as an order embedding. -/
@[simps] protected def order_embedding.inr : β ↪o α ⊕ β :=
{ to_fun := inr,
  inj' := inr_injective,
  map_rel_iff' := λ _ _, inr_le_inr_iff }

end

namespace sum
variables [preorder 𝕆] [preorder α] [preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α ⊕ β}

@[simp] lemma inl_covby_inl : (inl a₁ : α ⊕ β) ⋖ inl a₂ ↔ a₁ ⋖ a₂ :=
begin
  refine ⟨covby.of_image (order_embedding.inl : _ ↪o α ⊕ β), _⟩,
  sorry
end

@[simp] lemma inr_covby_inr : (inr b₁ : α ⊕ β) ⋖ inr b₂ ↔ b₁ ⋖ b₂ :=
begin
  refine ⟨covby.of_image (order_embedding.inr : _ ↪o α ⊕ β), _⟩,
  sorry
end

@[simp] lemma not_inl_covby_inr : ¬ inl a ⋖ inr b := λ h, not_inl_lt_inr h.lt
@[simp] lemma not_inr_covby_inl : ¬ inr a ⋖ inl b := λ h, not_inr_lt_inl h.lt

lemma covby_iff :
  x ⋖ y ↔
    (∃ a₁ a₂, a₁ ⋖ a₂ ∧ x = inl a₁ ∧ y = inl a₂) ∨ ∃ b₁ b₂, b₁ ⋖ b₂ ∧ x = inr b₁ ∧ y = inr b₂ :=
by cases x; cases y; simp

instance [grade_order 𝕆 α] [grade_order 𝕆 β] : grade_order 𝕆 (α ⊕ β) :=
{ grade := sum.elim (grade 𝕆) (grade 𝕆),
  grade_strict_mono := grade_strict_mono.sum_elim grade_strict_mono,
  covby_grade := λ x y, begin
    rw covby_iff,
    rintro (⟨a₁, a₂, h, rfl, rfl⟩ | ⟨b₁, b₂, h, rfl, rfl⟩); exact h.grade _,
  end }

instance [grade_min_order 𝕆 α] [grade_min_order 𝕆 β] : grade_min_order 𝕆 (α ⊕ β) :=
{ is_min_grade := λ x hx, begin
    cases x,
    { exact (is_min_inl_iff.1 hx).grade _ },
    { exact (is_min_inr_iff.1 hx).grade _ }
  end,
  ..sum.grade_order }

instance [grade_max_order 𝕆 α] [grade_max_order 𝕆 β] : grade_max_order 𝕆 (α ⊕ β) :=
{ is_max_grade := λ x hx, begin
    cases x,
    { exact (is_max_inl_iff.1 hx).grade _ },
    { exact (is_max_inr_iff.1 hx).grade _ }
  end,
  ..sum.grade_order }

instance [grade_bounded_order 𝕆 α] [grade_bounded_order 𝕆 β] : grade_bounded_order 𝕆 (α ⊕ β) :=
{ ..sum.grade_min_order, ..sum.grade_max_order }

variables (a b) [grade_order 𝕆 α] [grade_order 𝕆 β]

@[simp] lemma grade_inl : grade 𝕆 (sum.inl a : α ⊕ β) = grade 𝕆 a := rfl
@[simp] lemma grade_inr : grade 𝕆 (sum.inr b : α ⊕ β) = grade 𝕆 b := rfl

end sum

/-! #### Lexicographical sum of two graded orders -/

namespace sum.lex
variables [preorder α] [bounded_order α] [preorder β] [order_bot β]

instance grade_order [grade_order ℕ α] [grade_order ℕ β] : grade_order ℕ (α ⊕ₗ β) :=
{ grade := sum.elim (grade ℕ) (λ b, grade ℕ (⊤ : α) + grade ℕ b),
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

instance grade_min_order [grade_min_order ℕ α] [grade_min_order ℕ β] : grade_min_order ℕ (α ⊕ₗ β) :=
{ is_min_grade := sorry,
  ..sum.lex.grade_order }

variables (a : α) (b : β) [grade_order ℕ α] [grade_order ℕ β]

@[simp] protected lemma grade_inlₗ : grade ℕ (sum.inlₗ a : α ⊕ₗ β) = grade ℕ a := rfl
@[simp] protected lemma grade_inrₗ : grade ℕ (sum.inrₗ b : α ⊕ₗ β) = grade ℕ (⊤ : α) + grade ℕ b :=
rfl

end sum.lex

/-! #### Finite lexicographical sum of graded orders -/

namespace sigma.lex
variables [fintype ι] [linear_order ι] [order_bot ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)]

/-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
instance grade_order [Π i, grade_order ℕ (σ i)] : grade_order ℕ (Σₗ i, σ i) :=
{ grade := sorry,
  grade_strict_mono := λ a b h, sorry,
  covby_grade := sorry }

instance grade_min_order [Π i, grade_min_order ℕ (σ i)] : grade_min_order ℕ (Σₗ i, σ i) :=
{ is_min_grade := sorry,
  ..sigma.lex.grade_order }

-- @[simp] protected lemma grade (f : Σ i, σ i) : grade f = sorry := rfl

end sigma.lex

namespace psigma.lex
variables [fintype ι] [linear_order ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)]
  [Π i, grade_order ℕ (σ i)]

-- /-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
-- def grade_order : grade_order ℕ (Σₗ' i, σ i) :=
-- { grade := sorry,
--   grade_strict_mono := λ a b h, sorry,
--   covby_grade := sorry }

-- instance grade_min_order [Π i, grade_min_order ℕ (σ i)] : grade_min_order ℕ (Σₗ' i, σ i) :=
-- { is_min_grade := sorry,
--   ..psigma.lex.grade_order }

--@[simp] protected lemma grade (f : Σ' i, σ i) : grade f = sorry := rfl

end psigma.lex

/-! #### `with_bot`, `with_top` -/

namespace with_bot
variables [preorder α] [order_bot α] [grade_min_order ℕ α]

instance : grade_min_order ℕ (with_bot α) :=
{ grade := @with_bot.rec_bot_coe α (λ _, ℕ) 0 (λ a, grade ℕ a + 1),
  is_min_grade := sorry,
  grade_strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact nat.zero_lt_succ _ },
    { exact (not_lt_bot h).elim },
    { exact nat.succ_lt_succ (grade_strict_mono (with_bot.some_lt_some.1 h)) }
  end,
  covby_grade := λ x y h, begin
    sorry
  end }

@[simp] protected lemma grade_coe (a : α) : grade ℕ (a : with_bot α) = grade ℕ a + 1 := rfl

end with_bot

namespace with_top
variables [partial_order α] [bounded_order α] [grade_min_order ℕ α]

instance : grade_min_order ℕ (with_top α) :=
{ grade := @with_top.rec_top_coe α (λ _, ℕ) (grade ℕ (⊤ : α) + 1) (grade ℕ),
  is_min_grade := sorry,
  grade_strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact (not_le_of_lt h le_top).elim },
    { exact nat.lt_succ_of_le (grade_le_grade_top _) },
    { exact grade_strict_mono (with_top.some_lt_some.1 h) }
  end,
  covby_grade := λ x y h, begin
    sorry
  end }

@[simp] protected lemma grade_coe (a : α) : grade ℕ (a : with_top α) = grade ℕ a := rfl
@[simp] protected lemma grade_top : grade ℕ (⊤ : with_top α) = grade ℕ (⊤ : α) + 1 := rfl

end with_top
