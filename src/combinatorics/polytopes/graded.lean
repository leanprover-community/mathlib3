/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import category_theory.category.basic
import data.finsupp.basic
import data.dfinsupp
import data.sigma.order
import .cover

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

open category_theory nat
open_locale big_operators

variables {ι α β : Type*} {σ : ι → Type*}

/-- A graded order is an order homomorphism into ℕ such that:
    * `⊥` has grade 0
    * the homomorphism respects covering. -/
class grade_order (α : Type*) [preorder α] [order_bot α] :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(grade_of_covers (a b : α) : a ⋖ b → grade b = grade a + 1)

section preorder
variables [preorder α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

/-- The grade function of a graded order. -/
def grade : α → ℕ := grade_order.grade

lemma grade_strict_mono : strict_mono (grade : α → ℕ) := grade_order.strict_mono

lemma grade_bot : grade (⊥ : α) = 0 := grade_order.grade_bot

lemma covers.grade (h : a ⋖ b) : grade b = grade a + 1 := grade_order.grade_of_covers _ _ h

lemma covers.grade_succ (h : a ⋖ b) : grade a + 1 = grade b := h.grade.symm

/-- A natural number that is the grade of some element. -/
def is_grade (α : Type*) [preorder α] [order_bot α] [grade_order α] (n : ℕ) : Prop :=
∃ a : α, grade a = n

/-- The grade as a strict order homomorphism. -/
def grade_order.rel_hom (α : Type*) [preorder α] [order_bot α] [grade_order α] :
  @rel_hom α ℕ (<) (<) :=
⟨_, grade_order.strict_mono⟩

end order_bot
end preorder

section partial_order
variables [partial_order α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

lemma grade_mono : monotone (grade : α → ℕ) := grade_strict_mono.monotone

/-- The grade as an order homomorphism. -/
def grade_order.order_hom : α →ₘ ℕ := ⟨grade, grade_mono⟩

/-- A closed non-empty interval of a graded poset is a graded poset. -/
def set.Icc.graded (h : a ≤ b) : @grade_order (set.Icc a b) _ (set.Icc.order_bot h) :=
{ grade := λ x, grade x.val - grade a,
  strict_mono := λ x y h,
    nat.sub_mono_left_strict (grade_mono x.prop.left) (grade_strict_mono h),
  grade_bot := tsub_eq_zero_of_le le_rfl,
  grade_of_covers := begin
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨hxy, hcov⟩,
    rw [(covers.grade ⟨hxy, λ c ha hb, _⟩ : (grade y = grade x + 1)), nat.sub_add_comm],
    exact grade_mono hx.left,
    simp at hcov, -- Todo(Vi): Remove this `simp`.
    exact hcov _ (hx.1.trans ha.le) (hb.le.trans hy.2) ha hb,
  end }

/-- An element has grade `0` iff it is the bottom element. -/
@[simp]
lemma grade_eq_zero_iff (a : α) : grade a = 0 ↔ a = ⊥ :=
begin
  refine ⟨λ h, _, _⟩,
    { by_contra ha,
      exact (h.le.trans grade_bot.ge).not_lt (grade_strict_mono $ bot_lt_iff_ne_bot.2 ha) },
  rintro rfl,
  exact grade_bot
end

/-- If two elements in a graded partial order cover each other, so do their grades. This is just a
restatement of the covering condition. -/
lemma covers.grade_covers {a b : α} (h : a ⋖ b) : grade a ⋖ grade b :=
nat.covers_iff_eq_succ.2 h.grade

/-- A minor strengthening of `grade_of_covers`. -/
lemma covers_iff_lt_and_grade_succ_eq [preorder α] [order_bot α] [grade_order α] {a b : α} :
  a ⋖ b ↔ a < b ∧ grade a + 1 = grade b :=
⟨λ h, ⟨h.lt, h.grade.symm⟩, λ h, ⟨h.1, λ c ha hb,
  (nat.covers_iff_succ_eq.2 h.2).2 (grade_strict_mono ha) $ grade_strict_mono hb⟩⟩

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α] {a b : α}

lemma grade_le_grade_top (a : α) : grade a ≤ grade (⊤ : α) := grade_mono le_top

lemma has_lt.lt.grade_lt_grade_top (h : a < b) : grade a < grade (⊤ : α) :=
grade_strict_mono $ h.trans_le le_top

@[simp] lemma grade_lt_grade_top_of_nonempty (h : (set.Ioi a).nonempty) :
  grade a < grade (⊤ : α) :=
has_lt.lt.grade_lt_grade_top h.some_mem

variables (α)

open order_dual

instance : grade_order (order_dual α) :=
{ grade := λ a, grade (⊤ : α) - grade (of_dual a),
  grade_bot := nat.sub_self _,
  strict_mono := λ (a b : α) hab,
    (tsub_lt_tsub_iff_left_of_le $ grade_le_grade_top a).2 (grade_strict_mono hab),
  grade_of_covers := λ a b h, begin
    rw [h.of_dual.grade, ←tsub_tsub],
    exact (tsub_add_cancel_of_le $ nat.succ_le_iff.2 $ nat.sub_pos_of_lt $
      h.1.of_dual.grade_lt_grade_top).symm,
  end }

/-- Duals have the same top grade as the posets they come from. -/
lemma grade_top_dual : grade (⊤ : order_dual α) = grade (⊤ : α) :=
by { change grade ⊤ - grade ⊥ = grade ⊤, rw [grade_bot, nat.sub_zero] }

variables {α}

/-- An element has the top grade iff it is the top element. -/
@[simp]
lemma eq_grade_top_iff_eq_top (a : α) : grade a = grade (⊤ : α) ↔ a = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by rw h⟩,
  by_contra ha,
  exact not_le_of_lt (grade_strict_mono $ lt_top_iff_ne_top.2 ha) h.ge,
end

/-- A grade function into `fin` for `α` with a top element. -/
def grade_fin (x : α) : fin (grade (⊤ : α) + 1) :=
⟨grade x, by rw nat.lt_add_one_iff; exact grade_le_grade_top _⟩

@[simp]
lemma grade_fin.val_eq (x : α) : (grade_fin x).val = grade x := rfl

lemma grade_fin.strict_mono : strict_mono (grade_fin : α → fin (grade ⊤ + 1)) :=
grade_strict_mono

end bounded_order
end partial_order

section linear_order
variables [linear_order α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

/-- `grade` is injective for linearly ordered `α`. -/
lemma grade_injective : function.injective (grade : α → ℕ) := grade_strict_mono.injective

lemma grade_le_iff_le (x y : α) : grade x ≤ grade y ↔ x ≤ y := grade_strict_mono.le_iff_le

/-- `grade` as an order embedding into `ℕ` for a linear order `α`. -/
def order_embedding.grade : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade_injective,
  map_rel_iff' := grade_le_iff_le }

lemma grade_lt_iff_lt (x y : α) : grade x < grade y ↔ x < y := grade_strict_mono.lt_iff_lt

lemma grade_eq_iff_eq (x y : α) : grade x = grade y ↔ x = y := grade_strict_mono.injective.eq_iff

lemma grade_ne_iff_ne (x y : α) : grade x ≠ grade y ↔ x ≠ y := grade_strict_mono.injective.ne_iff

/-- In linear orders, `grade_of_covers` is an equivalence. -/
lemma covers_iff_grade_succ_eq : a ⋖ b ↔ grade a + 1 = grade b :=
⟨covers.grade_succ, λ h, covers_iff_lt_and_grade_succ_eq.2
  ⟨(grade_lt_iff_lt _ _).1 $ nat.succ_le_iff.1 h.le, h⟩⟩

/-- Two elements in a linear order cover each other iff their grades do. -/
lemma cover_iff_nat_cover (a b : α) : a ⋖ b ↔ grade a ⋖ grade b :=
⟨covers.grade_covers, λ h, covers_iff_grade_succ_eq.2 $ nat.covers_iff_succ_eq.1 h⟩

/-- The set of grades in a linear order has no gaps. -/
private lemma grade_ioo_lin (m n : ℕ) :
  is_grade α m → is_grade α n → nonempty (set.Ioo m n) → ∃ r ∈ set.Ioo m n, is_grade α r :=
begin
  rintro ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨_, hrl, hrr⟩,
  obtain ⟨_, hac, hcb⟩ := exists_lt_lt_of_not_covers (λ h, (λ ⟨_, hmn⟩, hmn hrl hrr : ¬_ ⋖ _)
    h.grade_covers) ((grade_lt_iff_lt _ _).1 (lt_trans hrl hrr)),
  exact ⟨_, ⟨grade_strict_mono hac, grade_strict_mono hcb⟩, _, rfl⟩,
end

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α]

lemma grade_fin_injective : function.injective (grade_fin : α → fin (grade ⊤ + 1)) :=
grade_fin.strict_mono.injective

/-- `grade_fin` is an order embedding into `fin` for linearly ordered `α` with a top element. -/
def order_embedding.grade_fin : α ↪o fin (grade ⊤ + 1) :=
{ to_fun := grade_fin,
  inj' := grade_fin_injective,
  map_rel_iff' := grade_le_iff_le }

/-- A graded linear order has an element of grade `j` when `j ≤ grade ⊤`. This is generalized to a
partial order in `ex_of_grade`. -/
lemma ex_of_grade_lin (j : fin (grade (⊤ : α) + 1)) : is_grade α j :=
(nat.all_icc_of_ex_ioo grade_ioo_lin) _ _ ⟨⊥, grade_bot⟩ ⟨⊤, rfl⟩ _
  ⟨zero_le _, nat.le_of_lt_succ j.prop⟩

/-- A linear order has a unique element of grade `j` when `j ≤ grade ⊤`. -/
lemma ex_unique_of_grade (j : fin (grade (⊤ : α) + 1)) :
  ∃! a : α, grade a = j :=
by { cases ex_of_grade_lin j with _ ha, exact ⟨_, ha, λ _ hb, grade_injective (by rw [ha, hb])⟩ }

end bounded_order
end linear_order

/-! ### Instances -/

/-! #### Natural numbers -/

namespace nat

/-- Natural numbers are graded. -/
instance : grade_order ℕ :=
{ grade := id,
  grade_bot := rfl,
  strict_mono := strict_mono_id,
  grade_of_covers := λ a b, nat.covers_iff_eq_succ.1 }

protected lemma grade (n : ℕ) : grade n = n := rfl

end nat

/-! #### `fin` -/

namespace fin

/-- `fin (n + 1)` is graded. -/
instance (n : ℕ) : grade_order (fin (n + 1)) :=
{ grade := λ k, k,
  grade_bot := rfl,
  strict_mono := strict_mono_id,
  grade_of_covers := λ _ _ h, nat.covers_iff_eq_succ.1 $ (fin.val_covers_iff _ _).2 h }

protected lemma grade {n : ℕ} (k : fin (n + 1)) : grade k = k := rfl

end fin

/-! #### `unique` -/

section unique
variables (α) [unique α] [preorder α]

/-- An order with one element is a graded order, aka a nullitope. -/
def unique.to_grade_order [order_bot α] : grade_order α :=
{ grade := λ _, 0,
  grade_bot := rfl,
  strict_mono := subsingleton.strict_mono,
  grade_of_covers := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim }

variables {α}

lemma unique.grade_top [bounded_order α] [grade_order α] : grade (⊤ : α) = 0 :=
(congr_arg _ $ subsingleton.elim _ _).trans grade_bot

end unique

/-! #### Simple orders -/

section is_simple_order
variables (α)

/-- A simple order is a graded order, aka a point. -/
def is_simple_order.to_grade_order [decidable_eq α] [preorder α] [bounded_order α]
  [is_simple_order α] :
  grade_order α :=
{ grade := λ a, if a = ⊥ then 0 else 1,
  grade_bot := if_pos rfl,
  strict_mono := λ a b h, begin
    convert zero_lt_one,
    { exact if_pos (is_simple_order.eq_bot_of_lt h) },
    { exact if_neg (ne_bot_of_lt h) },
    { apply_instance }
  end,
  grade_of_covers := λ a b h, begin
    convert (zero_add 1).symm,
    { exact if_neg (ne_bot_of_lt h.1) },
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) }
  end }

variables {α}

lemma is_simple_order.grade_top [partial_order α] [bounded_order α] [is_simple_order α]
  [grade_order α] :
  grade (⊤ : α) = 1 :=
bot_covers_top.grade.trans $ by rw [grade_bot, zero_add]

end is_simple_order

/-! #### Multiset -/

namespace multiset

private lemma cons_lt_cons (a : α) {s t : multiset α} (hlt : s < t) : a ::ₘ s < a ::ₘ t :=
⟨cons_le_cons _ hlt.1, hlt.2 ∘ (cons_le_cons_iff _).mp⟩

private lemma lt_cons_of_le (a : α) {s t : multiset α} : s ≤ t → s < a ::ₘ t :=
λ hle, lt_of_lt_of_le (lt_cons_self _ _) (cons_le_cons _ hle)

lemma covers.exists_cons_multiset [decidable_eq α] {s t : multiset α} (hcovers : s ⋖ t) :
  ∃ a, t = a ::ₘ s :=
begin
  cases hcovers with hlt no_intermediate,
  rcases hdiff : (t - s) with ⟨diff⟩,
  cases diff,
  { exfalso,
    simp at hdiff,
    exact hlt.2 hdiff },
  cases diff_tl,
  { use diff_hd,
    rw [←(eq_union_left hlt.1), union_def, hdiff],
    refl },
  { exfalso,
    apply @no_intermediate (diff_hd ::ₘ s),
    { apply lt_cons_self },
    { rw [←(eq_union_left hlt.1), union_def, hdiff],
      simp,
      rw [←cons_coe, ←cons_coe, cons_add, cons_add],
      apply cons_lt_cons,
      apply lt_cons_of_le,
      exact le_add_self } }
end

instance (α : Type*) : grade_order (multiset α) :=
{ grade := card,
  grade_bot := card_zero,
  strict_mono := λ a b, card_lt_of_lt,
  grade_of_covers := λ a b hab, begin
    have ab_cons : ∃ x, b = x ::ₘ a := sorry,
    -- `covers.exists_cons_multiset hab` doesn't work here because it requires `decidable_eq α`.
    -- I don't know how to `include` ... `omit` an instance, please help me!
    cases ab_cons with _ hcons,
    have hcard := congr_arg card hcons,
    rwa card_cons at hcard
  end }

@[simp] protected lemma grade (m : multiset α) : grade m = m.card := rfl

end multiset

/-! #### Finset -/

namespace finset

@[simp] lemma finset.val_covers_iff {s t : finset α} : s.1 ⋖ t.1 ↔ s ⋖ t :=
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

instance (α : Type*) : grade_order (finset α) :=
{ grade := card,
  grade_bot := card_empty,
  strict_mono := λ s t, card_lt_card,
  grade_of_covers := λ s t hst,
    grade_order.grade_of_covers s.val t.val (finset.val_covers_iff.mpr hst) }

@[simp] protected lemma grade (s : finset α) : grade s = s.card := rfl

end finset

/-! #### Finitely supported functions to a graded order -/

namespace finsupp
variables (α β) [canonically_ordered_add_monoid β] [grade_order β]

instance : grade_order (α →₀ β) :=
{ grade := λ f, f.sum (λ _, grade),
  grade_bot := sorry,
  strict_mono := λ a b, begin
    sorry
  end,
  grade_of_covers := λ a b hab, begin
    sorry
  end }

variables {α β}

@[simp] protected lemma grade (f : α →₀ β) : grade f = f.sum (λ _, grade) := rfl

end finsupp

/-! #### Finitely supported dependent functions to graded orders -/

namespace dfinsupp
variables (ι σ) [decidable_eq ι] [Π i, canonically_ordered_add_monoid (σ i)]
  [Π i (x : σ i), decidable (x ≠ 0)] [Π i, grade_order (σ i)]

instance : grade_order (Π₀ i, σ i) :=
{ grade := λ f, f.sum (λ i, grade),
  grade_bot := sorry,
  strict_mono := λ a b, sorry,
  grade_of_covers := λ a b hab, begin
    sorry
  end }

variables {ι σ}

@[simp] protected lemma grade (f : Π₀ i, σ i) : grade f = f.sum (λ i, grade) := rfl

end dfinsupp

/-! #### Product of two graded orders -/

namespace prod
variables (α β) [preorder α] [order_bot α] [grade_order α] [preorder β] [order_bot β]
  [grade_order β]

instance : grade_order (α × β) :=
{ grade := λ a, grade a.1 + grade a.2,
  grade_bot := begin
    convert (zero_add _).trans grade_bot,
    exact grade_bot,
  end,
  strict_mono := λ a b h, begin
    rw prod.lt_iff at h,
    cases h,
    {
      sorry,
    },
    {
      sorry
    }
  end,
  grade_of_covers := sorry }

variables {α β}

@[simp] protected lemma grade (a : α × β) : grade a = grade a.1 + grade a.2 := rfl

end prod

/-! #### Finite product of graded orders -/

namespace pi
variables (ι σ) [fintype ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)] [Π i, grade_order (σ i)]

instance : grade_order (Π i, σ i) :=
{ grade := λ f, ∑ i, grade (f i),
  grade_bot := by simp_rw [bot_apply, grade_bot, finset.sum_const_zero],
  strict_mono := λ a b h, begin
    rw pi.lt_def at h,
    obtain ⟨h, i, hi⟩ := h,
    sorry
  end,
  grade_of_covers := sorry }

variables {ι σ}

@[simp] protected lemma grade (f : Π i, σ i) : grade f = ∑ i, grade (f i) := rfl

end pi

/-! #### Lexicographical sum of two graded orders -/

section sum
variables (α β) [preorder α] [bounded_order α] [grade_order α] [preorder β] [order_bot β]
  [grade_order β]

def grade_order : grade_order (α ⊕ β) :=
{ grade := λ a, a.elim grade (λ b, grade (⊤ : α) + grade b),
  grade_bot := grade_bot,
  strict_mono := λ a b h, sorry,
  grade_of_covers := sorry }

variables {α β}

@[simp] protected lemma grade_inl (a : α) : grade (sum.inl a : α ⊕ β) = grade a := rfl

@[simp] protected lemma grade_inr (b : β) : grade (sum.inr b : α ⊕ β) = grade (⊤ : α) + grade b :=
rfl

end sum

/-! #### Finite lexicographical sum of graded orders -/

namespace sigma.lex
variables (ι σ) [fintype ι] [linear_order ι] [order_bot ι] [Π i, preorder (σ i)]
  [Π i, order_bot (σ i)] [Π i, grade_order (σ i)]

open_locale lex

/-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
def grade_order : grade_order (Σ i, σ i) :=
{ grade := sorry,
  grade_bot := sorry,
  strict_mono := λ a b h, sorry,
  grade_of_covers := sorry }

localized "attribute [instance] sigma.lex.grade_order" in lex

variables {ι σ}

@[simp] protected lemma grade (f : Σ i, σ i) : grade f = sorry := rfl

end sigma.lex

namespace psigma.lex
variables (ι σ) [fintype ι] [linear_order ι] [Π i, preorder (σ i)] [Π i, order_bot (σ i)]
  [Π i, grade_order (σ i)]

open_locale lex

/-- The lexicographical grading on a sigma type. Turn this on by opening locale `lex`. -/
def grade_order : grade_order (Σ' i, σ i) :=
{ grade := sorry,
  grade_bot := sorry,
  strict_mono := λ a b h, sorry,
  grade_of_covers := sorry }

localized "attribute [instance] psigma.lex.grade_order" in lex

variables {ι σ}

@[simp] protected lemma grade (f : Σ' i, σ i) : grade f = sorry := rfl

end psigma.lex

/-! #### `with_bot`, `with_top` -/

namespace with_bot
variables (α) [preorder α] [order_bot α] [grade_order α]

instance : grade_order (with_bot α) :=
{ grade := @with_bot.rec_bot_coe α (λ _, ℕ) 0 (λ a, grade a + 1),
  grade_bot := rfl,
  strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact nat.zero_lt_succ _ },
    { exact (not_lt_bot h).elim },
    { exact nat.succ_lt_succ (grade_order.strict_mono (with_bot.some_lt_some.1 h)) }
  end,
  grade_of_covers := λ x y h, begin
    sorry
  end }

variables {α}

@[simp] protected lemma grade_coe (a : α) : grade (a : with_bot α) = grade a + 1 := rfl

end with_bot

namespace with_top
variables (α) [partial_order α] [bounded_order α] [grade_order α]

instance : grade_order (with_top α) :=
{ grade := @with_top.rec_top_coe α (λ _, ℕ) (grade (⊤ : α) + 1) grade,
  grade_bot := grade_bot,
  strict_mono := λ x y h, begin
    cases x; cases y,
    { exact (h.ne rfl).elim },
    { exact (not_le_of_lt h le_top).elim },
    { exact nat.lt_succ_of_le (grade_le_grade_top _) },
    { exact grade_order.strict_mono (with_top.some_lt_some.1 h) }
  end,
  grade_of_covers := λ x y h, begin
    sorry
  end }

variables {α}

@[simp] protected lemma grade_coe (a : α) : grade (a : with_top α) = grade a := rfl
@[simp] protected lemma grade_top : grade (⊤ : with_top α) = grade (⊤ : α) + 1 := rfl

end with_top

/-! ### More stuff -/

namespace polytope
variable [has_lt α]

/-- Proper elements are those that are neither maximal nor minimal. -/
def is_proper (b : α) : Prop := ∃ a c, a < b ∧ b < c

/-- The subtype of proper elements. -/
@[reducible]
def proper (α : Type*) [has_lt α] : Type* := {a : α // is_proper a}

/-- Proper elements are incident when they're comparable. -/
def incident (a b : proper α) : Prop := a.val ≠ b.val → a.val < b.val ∨ b.val < a.val

end polytope

open polytope

section preorder
variables [preorder α]

section order_bot
variables [order_bot α]

/-- The bottom element is improper. -/
lemma not_proper_bot : ¬ is_proper (⊥ : α) := λ ⟨_, _, h, _⟩, not_lt_bot h

lemma polytope.is_proper.ne_bot {a : α} (h : polytope.is_proper a) : a ≠ ⊥ :=
by { rintro rfl, exact not_proper_bot h }

end order_bot

section order_top
variables [order_top α]

/-- The top element is improper. -/
lemma not_proper_top : ¬ is_proper (⊤ : α) := λ ⟨_, _, _, h⟩, not_top_lt h

lemma polytope.is_proper.ne_top {a : α} (h : polytope.is_proper a) : a ≠ ⊤ :=
by { rintro rfl, exact not_proper_top h }

end order_top
end preorder

section partial_order
variables [partial_order α]

section bounded_order
variables [bounded_order α]

/-- The improper elements are exactly the bottom and top ones. -/
lemma proper_iff_ne_bot_top (a : α) : polytope.is_proper a ↔ a ≠ ⊥ ∧ a ≠ ⊤ :=
⟨λ h, ⟨h.ne_bot, h.ne_top⟩, λ ⟨hl, hr⟩, ⟨⊥, ⊤, bot_lt_iff_ne_bot.2 hl, lt_top_iff_ne_top.2 hr⟩⟩

variables [grade_order α]

/-- An element is proper iff it has a grade between the bottom and top element. -/
lemma proper_iff_grade_iio (a : α) : is_proper a ↔ grade a ∈ set.Ioo 0 (grade (⊤ : α)) :=
begin
  rw proper_iff_ne_bot_top,
  split,
    { intro ha,
      cases ha with hal har,
      cases eq_or_lt_of_le (zero_le (grade a)) with h hl,
        { replace h := eq.symm h,
          rw grade_eq_zero_iff at h,
          exact (hal h).elim },
      cases eq_or_lt_of_le (grade_le_grade_top a) with h hr,
        { rw eq_grade_top_iff_eq_top at h,
          exact (har h).elim },
      exact ⟨hl, hr⟩ },
  rintro ⟨hl, hr⟩,
  split,
    { intro ha,
      rw ←grade_eq_zero_iff at ha,
      exact hl.ne' ha },
  intro ha,
  rw ←eq_grade_top_iff_eq_top at ha,
  exact hr.ne ha
end

/-- A `graded` with top grade 1 or less has no proper elements. -/
lemma proper.empty : grade (⊤ : α) ≤ 1 → is_empty (polytope.proper α) :=
begin
  intro h,
  split,
  rintro ⟨a, ha⟩,
  rw proper_iff_grade_iio at ha,
  refine (not_le_of_lt (lt_of_le_of_lt _ ha.right)) h,
  exact ha.left
end

/-- A `graded` with top grade 2 or more has some proper element. -/
lemma proper.nonempty (h : 2 ≤ grade (⊤ : α)) : nonempty (polytope.proper α) :=
begin
  have hbt : ¬ ⊥ ⋖ ⊤ := begin
    intro hbt,
    have := hbt.grade,
    rw grade_bot at this,
    rw this at h,
    exact nat.lt_asymm h h,
  end,

  have hbt' : (⊥ : α) < ⊤ := begin
    rw bot_lt_iff_ne_bot,
    intro hbt',
    rw [hbt', grade_bot] at h,
    exact (not_le_of_lt zero_lt_two) h,
  end,

  obtain ⟨z, hz⟩ := exists_lt_lt_of_not_covers hbt hbt',
  exact ⟨⟨z, ⊥, ⊤, hz⟩⟩,
end

end bounded_order
end partial_order

/-- Two elements of a type are connected by a relation when there exists a path of related
elements. This is essentially an inductive version of an equivalence closure. -/
 -- Todo(Vi): If someone comes up with connected graphs sometime, we might want to rework this.
inductive polytope.path (r : α → α → Prop) : α → α → Prop
| start (x : α) : polytope.path x x
| next (x y z : α) : polytope.path x y → r y z → polytope.path x z

namespace path
section

variables {r : α → α → Prop} {a b c : α}

/-- Connectivity is reflexive. -/
@[refl]
lemma refl : path r a a := path.start a

/-- Related elements are connected. -/
lemma from_rel : r a b → path r a b := (path.next a a b) (path.refl)

/-- If `a` and `b` are related, and `b` and `c` are connected, then `a` and `c` are connected. -/
lemma append_left (hab : r a b) (hbc : path r b c) : path r a c :=
begin
  induction hbc with _ _ _ _ _ hcd h,
    { exact path.from_rel hab },
    { exact path.next _ _ _ (h hab) hcd }
end

/-- Connectedness with a symmetric relation is symmetric. -/
@[symm]
lemma symm [is_symm α r] (hab : path r a b) : path r b a :=
begin
  induction hab with _ _ _ _ _ hbc hba,
    { exact path.refl },
    { exact path.append_left (is_symm.symm _ _ hbc) hba, }
end

/-- Connectedness is transitive. -/
lemma trans (hab : path r a b) (hbc : path r b c) : path r a c :=
by { induction hab with _ _ _ _ _ hdb h, exact hbc, exact h (path.append_left hdb hbc) }

/-- If `a` and `b` are connected, and `b` and `c` are related, then `a` and `c` are connected. -/
lemma append_right (hab : path r a b) (hbc : r b c) : path r a c :=
trans hab (from_rel hbc)

end
end path

/-- Proper elements are connected when they're related by a sequence of pairwise incident proper
elements. -/
def polytope.connected [preorder α] (a b : polytope.proper α) : Prop :=
path polytope.incident a b

open polytope

namespace graded

/-- A `graded` is totally connected' when any two proper elements are connected. Note that this
definition requires nothing more than a preorder. -/
def total_connected' (α : Type*) [preorder α] : Prop :=
∀ a b : proper α, connected a b

/-- A `graded` is totally connected when it's of grade 2, or any two proper elements are connected.

Here we deviate from standard nomenclature: mathematicians would just call this connectedness.
However, by doing this, it makes it unambiguous when we're talking about two elements being
connected, and when we're talking about a polytope being totally connected. -/
def total_connected (α : Type*) [preorder α] [bounded_order α] [grade_order α] : Prop :=
grade (⊤ : α) = 2 ∨ total_connected' α

/-- Order isomorphisms preserve proper elements. -/
private lemma proper_order_iso_of_proper [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x : proper α) :
  is_proper (oiso x) :=
begin
  rw proper_iff_ne_bot_top (oiso x),
  have := x.prop,
  split, {
    intro h,
    apply @not_proper_bot α,
    rw ←oiso.map_bot at h,
    rwa oiso.injective h at this },
  intro h,
  apply @not_proper_top α,
  rw ←oiso.map_top at h,
  rwa oiso.injective h at this,
end

/-- Order isomorphisms preserve proper elements. -/
lemma proper_order_iso_iff_proper [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x : α) :
  is_proper x ↔ is_proper (oiso x) :=
begin
  refine ⟨λ hx, proper_order_iso_of_proper oiso ⟨x, hx⟩, λ hx, _⟩,
  have := proper_order_iso_of_proper oiso.symm ⟨oiso x, hx⟩,
  simp at this,
  exact this,
end

end graded

namespace order_iso

variables [partial_order α] [partial_order β] (oiso : α ≃o β)

/-- Order isomorphisms preserve covering. -/
private lemma covers' (a b : α) : a ⋖ b → oiso a ⋖ oiso b :=
begin
  refine λ h, ⟨oiso.strict_mono h.left, λ c ha hb, h.2 (_ : a < oiso.symm c) _⟩,
  { have := oiso.symm.strict_mono ha,
    simp at this,
    exact this },
  { have := oiso.symm.strict_mono hb,
    simp at this,
    exact this }
end

/-- Order isomorphisms preserve covering. -/
protected lemma covers (x y : α) : x ⋖ y ↔ oiso x ⋖ oiso y :=
begin
  use covers' oiso x y,
  have := covers' oiso.symm (oiso x) (oiso y),
  simp at this,
  exact this,
end

/-- An isomorphism between posets, one of which is graded, is enough to give a grade function for
the other. -/
protected def grade_order [order_bot α] [order_bot β] [grade_order β] : grade_order α :=
{ grade := λ a, @grade β _ _ _ (oiso a),
  grade_bot := begin
    rw oiso.map_bot,
    exact grade_bot,
  end,
  strict_mono := λ _ _ hab, grade_strict_mono (oiso.strict_mono hab),
  grade_of_covers := begin
    intros x y hxy,
    apply covers.grade,
    rwa ←oiso.covers x y,
  end }

/-- An isomorphism between graded posets extends to an isomorphism between sections. -/
protected def Icc (x y : α) : set.Icc x y ≃o set.Icc (oiso x) (oiso y) :=
{ to_fun := λ a, ⟨oiso.to_fun a.1, (le_iff_le oiso).2 a.prop.left, (le_iff_le oiso).2 a.prop.right⟩,
  inv_fun := λ a, ⟨oiso.inv_fun a, begin
    split,
    { have H : oiso.inv_fun (oiso.to_fun x) ≤ oiso.inv_fun a,
      { change oiso.inv_fun with oiso.symm,
        rw le_iff_le oiso.symm,
        exact a.prop.left },
      simp at H,
      exact H },
    have H : oiso.inv_fun a ≤ oiso.inv_fun (oiso.to_fun y),
    { change oiso.inv_fun with oiso.symm,
      rw le_iff_le oiso.symm,
      exact a.prop.right },
    simp at H,
    exact H,
  end⟩,
  left_inv := λ _, subtype.eq (by simp),
  right_inv := λ _, subtype.eq (by simp),
  map_rel_iff' := by simp }

variables [bounded_order α] [grade_order α] [bounded_order β] [grade_order β]

/-- The map from proper elements to proper elements given by an order isomorphism. -/
private def proper_aux : proper α → proper β :=
λ x, ⟨oiso x, (graded.proper_order_iso_iff_proper oiso x).1 x.prop⟩

/-- An isomorphism between graded posets extends to an isomorphism between proper elements. -/
def proper : proper α ≃o proper β :=
{ to_fun := proper_aux oiso,
  inv_fun := proper_aux oiso.symm,
  left_inv := λ x, subtype.eq (oiso.symm_apply_apply x),
  right_inv := λ x, subtype.eq (oiso.apply_symm_apply x),
  map_rel_iff' := λ _ _, le_iff_le oiso }

end order_iso

namespace graded

/-- If two elements are connected, so are their maps under an isomorphism. -/
private lemma con_order_iso_of_con [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x y : proper α) :
  connected x y → connected (oiso.proper x) (oiso.proper y) :=
begin
  intro hxy,
  induction hxy with _ x y z hxy hyz hxy',
    { exact path.refl },
  apply path.append_right hxy',
  intro hne,
  cases hyz (λ h, hne (congr_arg oiso h : oiso y = oiso z)) with hyz hyz,
    { exact or.inl (oiso.lt_iff_lt.2 hyz) },
  exact or.inr (oiso.lt_iff_lt.2 hyz),
end

/-- Two elements are connected iff their maps under an isomorphism are. -/
lemma con_order_iso_iff_con [partial_order α] [bounded_order α] [grade_order α]
  [partial_order β] [bounded_order β] [grade_order β] (oiso : α ≃o β) (x y : proper α) :
  connected x y ↔ connected (oiso.proper x) (oiso.proper y) :=
begin
  refine ⟨con_order_iso_of_con oiso x y, _⟩,
  have := con_order_iso_of_con oiso.symm (oiso.proper x) (oiso.proper y),
  rwa [(subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper x)) = x),
       (subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper y)) = y)] at this
end

/-- Any `graded` of top grade less or equal to 2 is connected. -/
lemma tcon_of_grade_le_two (α : Type*) [partial_order α] [bounded_order α] [grade_order α] :
  grade (⊤ : α) ≤ 2 → total_connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with ha ha, { exact or.inl ha },
  exact or.inr (λ a, (((proper.empty (nat.le_of_lt_succ ha)).false : proper α → false) a).elim)
end

/-- Asserts that a section of a graded poset is connected'. -/
def section_connected' [preorder α] (x y : α) : Prop :=
total_connected' (set.Icc x y)

/-- Asserts that a section of a graded poset is connected. -/
def section_connected [partial_order α] [order_bot α] [grade_order α] {x y : α} (hxy : x ≤ y) :
  Prop :=
@total_connected _ _ (set.Icc.bounded_order hxy) (set.Icc.graded hxy)

/-- A graded poset is strongly connected when all sections are connected. -/
def strong_connected (α : Type*) [partial_order α] [order_bot α] [grade_order α] : Prop :=
∀ {x y : α} (hxy : x ≤ y), section_connected hxy

/-- Any `graded` of top grade less or equal to 2 is strongly connected. -/
lemma scon_of_grade_le_two [partial_order α] [bounded_order α] [grade_order α]
  (h : grade (⊤ : α) ≤ 2) :
  strong_connected α :=
begin
  intros a b hab,
  apply tcon_of_grade_le_two,
  exact (le_trans tsub_le_self (le_trans (grade_le_grade_top b) h)),
end

end graded
