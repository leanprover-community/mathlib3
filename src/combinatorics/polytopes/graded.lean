/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import category_theory.category.basic
import data.finsupp.order
import data.dfinsupp
import data.nat.interval
import data.set.intervals.ord_connected
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

open category_theory finset nat
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
def grade_order.order_hom : α →o ℕ := ⟨grade, grade_mono⟩

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

/-- Constructs a locally finite from a grade function. -/
noncomputable def grade_order.to_locally_finite_order : locally_finite_order α :=
{ finset_Icc := λ a b, (Icc (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ico := λ a b, (Ico (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ioc := λ a b, (Ioc (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_Ioo := λ a b, (Ioo (grade a) (grade b)).preimage grade (grade_injective.inj_on _),
  finset_mem_Icc := λ a b x,
    by rw [mem_preimage, mem_Icc, grade_strict_mono.le_iff_le, grade_strict_mono.le_iff_le],
  finset_mem_Ico := λ a b x,
    by rw [mem_preimage, mem_Ico, grade_strict_mono.le_iff_le, grade_strict_mono.lt_iff_lt],
  finset_mem_Ioc := λ a b x,
    by rw [mem_preimage, mem_Ioc, grade_strict_mono.le_iff_le, grade_strict_mono.lt_iff_lt],
  finset_mem_Ioo := λ a b x,
    by rw [mem_preimage, mem_Ioo, grade_strict_mono.lt_iff_lt, grade_strict_mono.lt_iff_lt] }

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
  strict_mono := subsingleton.strict_mono _,
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

/-! #### Lifting a graded order -/

section lift
variables [preorder α] [order_bot α] [preorder β] [order_bot β] [grade_order β] {a b : α}
  {f : α ↪o β}

lemma covers.of_image (h : f a ⋖ f b) : a ⋖ b :=
begin
  refine ⟨_, λ c hac hcb, _⟩,
  { rw ←order_embedding.lt_iff_lt f,
    exact h.1 },
  rw ←order_embedding.lt_iff_lt f at hac hcb,
  exact h.2 hac hcb,
end

lemma covers.image_covers_of_ord_connected (h : (set.range f).ord_connected) (hab : a ⋖ b) :
  f a ⋖ f b :=
begin
  sorry
end

lemma image_covers_iff (h : (set.range f).ord_connected) : f a ⋖ f b ↔ a ⋖ b :=
⟨covers.of_image, covers.image_covers_of_ord_connected h⟩

/-- Lifts a graded order along an order embedding. -/
def grade_order.lift (hbot : f ⊥ = ⊥) (h : (set.range f).ord_connected) : grade_order α :=
{ grade := λ a, grade (f a),
  grade_bot := by rw [hbot, grade_bot],
  strict_mono := grade_strict_mono.comp f.strict_mono,
  grade_of_covers := λ a b h, begin
    sorry
  end }

end lift

/-! #### Multiset -/

namespace multiset
variables {s t : multiset α} {a : α}

lemma cons_lt_cons_iff : a ::ₘ s < a ::ₘ t ↔ s < t :=
lt_iff_lt_of_le_iff_le' (cons_le_cons_iff _) (cons_le_cons_iff _)

lemma cons_lt_cons (a : α) (h : s < t) : a ::ₘ s < a ::ₘ t := cons_lt_cons_iff.2 h

lemma covers_cons (m : multiset α) (a : α) : m ⋖ a ::ₘ m := ⟨lt_cons_self _ _, begin
  sorry
end⟩

lemma exists_cons_le_of_lt (h : s < t) : ∃ a, a ::ₘ s ≤ t :=
begin
  sorry
end

lemma _root_.covers.exists_cons_multiset (h : s ⋖ t) : ∃ a, t = a ::ₘ s :=
begin
  obtain ⟨a, ha⟩ := exists_cons_le_of_lt h.lt,
  refine ⟨a, ha.eq_of_not_gt _⟩,
  sorry
  -- cases hcovers with hlt no_intermediate,
  -- rcases hdiff : (t - s) with ⟨diff⟩,
  -- cases diff,
  -- { exfalso,
  --   simp at hdiff,
  --   exact hlt.2 hdiff },
  -- cases diff_tl,
  -- { use diff_hd,
  --   rw [←(eq_union_left hlt.1), union_def, hdiff],
  --   refl },
  -- { exfalso,
  --   apply @no_intermediate (diff_hd ::ₘ s),
  --   { apply lt_cons_self },
  --   { rw [←(eq_union_left hlt.1), union_def, hdiff],
  --     simp,
  --     rw [←cons_coe, ←cons_coe, cons_add, cons_add],
  --     apply cons_lt_cons,
  --     apply lt_cons_of_le,
  --     exact le_add_self } }
end

lemma covers_iff_exists_cons : s ⋖ t ↔ ∃ a, t = a ::ₘ s :=
begin
  refine ⟨covers.exists_cons_multiset, _⟩,
  rintro ⟨a, rfl⟩,
  exact covers_cons _ _,
end

instance (α : Type*) : grade_order (multiset α) :=
{ grade := card,
  grade_bot := card_zero,
  strict_mono := λ a b, card_lt_of_lt,
  grade_of_covers := λ a b hab, begin
    have ab_cons : ∃ x, b = x ::ₘ a := hab.exists_cons_multiset,
    cases ab_cons with _ hcons,
    have hcard := congr_arg card hcons,
    rwa card_cons at hcard,
  end }

@[simp] protected lemma grade (m : multiset α) : grade m = m.card := rfl

end multiset

/-! #### Finset -/

namespace finset

-- golf using `image_covers_iff`
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
