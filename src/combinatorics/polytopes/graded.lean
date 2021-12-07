/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import category_theory.category.basic
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

variables {α β : Type*}

/-- A graded order is an order homomorphism into ℕ such that:
    * `⊥` has grade 0
    * the homomorphism respects covering. -/
class grade_order (α : Type*) [preorder α] [order_bot α] :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ {x y}, x ⋖ y → grade y = grade x + 1)

section preorder
variables [preorder α]

section order_bot
variables [order_bot α] [grade_order α] {a b : α}

/-- The grade function of a graded order. -/
def grade : α → ℕ := grade_order.grade

lemma grade_strict_mono : strict_mono (grade : α → ℕ) := grade_order.strict_mono

lemma grade_bot : grade (⊥ : α) = 0 := grade_order.grade_bot

lemma covers.grade (h : a ⋖ b) : grade b = grade a + 1 := grade_order.hcovers h

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

lemma grade_mono : monotone (grade : α → ℕ) := by convert grade_strict_mono.monotone

/-- The grade as an order homomorphism. -/
def grade_order.preorder_hom : α →ₘ ℕ := ⟨grade, grade_mono⟩

/-- A closed non-empty interval of a graded poset is a graded poset. -/
def set.Icc.graded (h : a ≤ b) : @grade_order (set.Icc a b) _ (set.Icc.order_bot h) :=
{ grade := λ x, grade x.val - grade a,
  strict_mono := λ x y h,
    nat.sub_mono_left_strict (grade_mono x.prop.left) (grade_strict_mono h),
  grade_bot := tsub_eq_zero_of_le le_rfl,
  hcovers := begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩ ⟨hxy, hcov⟩,
    suffices this : ∀ z, z ∉ set.Ioo x y,
      { rw [(covers.grade ⟨hxy, this⟩ : (grade y = grade x + 1)), nat.sub_add_comm],
        exact grade_mono hx.left },
    rintros _ ⟨hl, hr⟩,
    simp at hcov, -- Todo(Vi): Remove this `simp`.
    exact hcov _ (hx.left.trans (le_of_lt hl)) ((le_of_lt hr).trans hy.right) hl hr,
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
lemma nat_cover_of_cover {a b : α} : a ⋖ b → grade a ⋖ grade b :=
by { rw nat.cover_iff_succ, exact covers.grade }

/-- A minor strengthening of `hcovers`. -/
lemma covers_iff_grade_succ_and_lt [preorder α] [order_bot α] [grade_order α] {x y : α} :
  x < y ∧ grade y = grade x + 1 ↔ x ⋖ y :=
⟨λ ⟨hxy, h⟩, ⟨hxy, (λ z ⟨hzl, hzr⟩, (nat.cover_iff_succ.2 h).right (grade z)
  ⟨grade_strict_mono hzl, grade_strict_mono hzr⟩)⟩, λ h, ⟨h.left, h.grade⟩⟩

end order_bot

section bounded_order
variables [bounded_order α] [grade_order α]

lemma grade_le_grade_top (a : α) : grade a ≤ grade (⊤ : α) := grade_mono le_top

variables (α)

instance : grade_order (order_dual α) :=
{ grade := λ a : α, grade (⊤ : α) - grade a,
  grade_bot := nat.sub_self _,
  strict_mono := begin
    refine λ (a b : α) hab, _,
    exact (tsub_lt_tsub_iff_left_of_le $ grade_le_grade_top a).2 (grade_strict_mono hab),
  end,
  hcovers := begin
    refine λ (x y : α) hxy, _,
    rw ←dual_cover_iff_cover at hxy,
    rw [hxy.grade, ←nat.sub_sub,
        nat.sub_add_cancel (tsub_pos_of_lt (grade_strict_mono (hxy.left.trans_le le_top)))],
  end }

/-- Duals have the same top grade as the posets they come from. -/
lemma grade_top_dual : grade (⊤ : order_dual α) = grade (⊤ : α) :=
by { change grade ⊤ - grade ⊥ = grade ⊤, rw [grade_bot, nat.sub_zero] }

variables {α}

/-- An element has the top grade iff it is the top element. -/
@[simp]
lemma eq_grade_top_iff_eq_top (a : α) : grade a = grade (⊤ : α) ↔ a = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by cases h; { refl }⟩,
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
variables [order_bot α] [grade_order α]

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

/-- In linear orders, `hcovers` is an equivalence. -/
lemma covers_iff_grade_eq_succ_grade (a b : α) : a ⋖ b ↔ grade b = grade a + 1 :=
⟨covers.grade, λ hba, covers_iff_grade_succ_and_lt.1
  ⟨(grade_lt_iff_lt _ _).1 (nat.lt_of_succ_le (le_of_eq hba.symm)), hba⟩⟩

/-- Two elements in a linear order cover each other iff their grades do. -/
lemma cover_iff_nat_cover (a b : α) : a ⋖ b ↔ grade a ⋖ grade b :=
begin
  split,
    { rw nat.cover_iff_succ,
      exact covers.grade },
  intro hab,
  rw nat.cover_iff_succ at hab,
  rwa covers_iff_grade_eq_succ_grade,
end

/-- The set of grades in a linear order has no gaps. -/
private lemma grade_ioo_lin (m n : ℕ) :
  is_grade α m → is_grade α n → nonempty (set.Ioo m n) → ∃ r ∈ set.Ioo m n, is_grade α r :=
begin
  rintros ⟨a, ham⟩ ⟨b, hbn⟩ ⟨r, hr⟩,

  have hnab : ¬a ⋖ b := begin
    have : ¬m ⋖ n := λ hmn, (hmn.right r) hr,
    rwa [←ham, ←hbn] at this,
    exact λ hab, this (nat_cover_of_cover hab),
  end,

  have hab : a < b := begin
    rw [←grade_lt_iff_lt, ham, hbn],
    exact lt_trans hr.left hr.right,
  end,

  obtain ⟨c, hac, hcb⟩ := exists_lt_lt_of_not_cover hnab hab,
  refine ⟨grade c, ⟨_, _⟩, c, rfl⟩,
  { rw ←ham,
    exact grade_strict_mono hac },
  { rw ←hbn,
    exact grade_strict_mono hcb }
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
begin
  cases ex_of_grade_lin j with a ha,
  use [a, ha],
  intros b hb,
  refine grade_injective _,
  rw [ha, hb]
end

end bounded_order
end linear_order

/-! ### Instances -/

/-! #### Natural numbers -/

namespace nat

/-- Natural numbers are graded. -/
instance : grade_order ℕ :=
⟨id, rfl, strict_mono_id, λ _ _, nat.cover_iff_succ.1⟩

protected lemma grade (n : ℕ) : grade n = n := rfl

end nat

/-! #### `fin` -/

namespace fin

/-- `fin (n + 1)` is graded. -/
instance (n : ℕ) : grade_order (fin (n + 1)) :=
{ grade := λ k, k,
  grade_bot := rfl,
  strict_mono := strict_mono_id,
  hcovers := λ _ _ h, nat.cover_iff_succ.1 ((fin.cover_iff_cover _ _).1 h) }

protected lemma grade {n : ℕ} (k : fin (n + 1)) : grade k = k := rfl

end fin

/-! #### `unique` -/

section unique
variables (α) [unique α] [preorder α]

/-- An order with one element is a graded order, aka a nullitope. -/
def unique.to_graded_order [order_bot α] : grade_order α :=
{ grade := λ _, 0,
  grade_bot := rfl,
  strict_mono := subsingleton.strict_mono,
  hcovers := λ a b h, (h.1.ne $ subsingleton.elim _ _).elim }

variables {α}

lemma unique.grade_top [bounded_order α] [grade_order α] : grade (⊤ : α) = 0 :=
(congr_arg _ $ subsingleton.elim _ _).trans grade_bot

end unique

/-! #### Simple orders -/

section is_simple_order
variables (α)

/-- A simple order is a graded order, aka a point. -/
def is_simple_order.to_graded_order [decidable_eq α] [preorder α] [bounded_order α]
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
  hcovers := λ a b h, begin
    convert (zero_add 1).symm,
    { exact if_neg (ne_bot_of_lt h.1) },
    { exact if_pos (is_simple_order.eq_bot_of_lt h.1) }
  end }

variables {α}

lemma is_simple_order.grade_top [partial_order α] [bounded_order α] [is_simple_order α]
  [grade_order α] :
  grade (⊤ : α) = 1 :=
is_simple_order.bot_covers_top.grade.trans $ by rw [grade_bot, zero_add]

end is_simple_order

/-! #### Product of two graded orders -/

namespace prod

instance [preorder α] [order_bot α] [grade_order α] [preorder β] [order_bot β] [grade_order β] :
  grade_order (α × β) :=
{ grade := λ a, grade a.fst + grade a.snd,
  grade_bot := begin
    convert (zero_add _).trans grade_bot,
    exact grade_bot,
  end,
  strict_mono := λ a b h, begin
    sorry
  end,
  hcovers := sorry }

protected lemma grade [preorder α] [order_bot α] [grade_order α] [preorder β] [order_bot β]
  [grade_order β] [grade_order (α × β)] (a : α × β) :
  grade a = grade a.1 + grade a.2 :=
sorry

end prod

/-! #### `with_bot`, `with_top` -/

instance (α : Type*) [preorder α] [order_bot α] [grade_order α] : grade_order (with_bot α) :=
{ grade := @with_bot.rec_bot_coe α (λ _, ℕ) 0 (λ a, grade a + 1),
  grade_bot := rfl,
  strict_mono := λ a b h, begin
    sorry
  end,
  hcovers := sorry }

instance (α : Type*) [preorder α] [bounded_order α] [grade_order α] : grade_order (with_top α) :=
{ grade := @with_top.rec_top_coe α (λ _, ℕ) (grade (⊤ : α) + 1) grade,
  grade_bot := grade_bot,
  strict_mono := λ a b h, begin
    sorry
  end,
  hcovers := sorry }

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
lemma not_proper_bot : ¬ is_proper (⊥ : α) := λ ⟨_, _, ⟨h, _⟩⟩, not_le_of_gt h bot_le

end order_bot

section bounded_order
variables [bounded_order α]

/-- The top element is improper. -/
lemma not_proper_top : ¬ is_proper (⊤ : α) := λ ⟨_, _, ⟨_, h⟩⟩, not_le_of_gt h le_top

/-- Elements other than the bottom and top ones are proper. -/
lemma proper.ne_bot_top (a : α) : polytope.is_proper a → a ≠ ⊥ ∧ a ≠ ⊤ :=
begin
  intro ha,
  split,
  repeat { intro h, rw h at ha, swap },
  exact not_proper_bot ha,
  exact not_proper_top ha,
end

end bounded_order
end preorder

section partial_order
variables [partial_order α]

section bounded_order
variables [bounded_order α]

/-- The improper elements are exactly the bottom and top ones. -/
lemma proper_iff_ne_bot_top (a : α) : polytope.is_proper a ↔ a ≠ ⊥ ∧ a ≠ ⊤ :=
⟨proper.ne_bot_top a, λ ⟨hl, hr⟩, ⟨⊥, ⊤, bot_lt_iff_ne_bot.2 hl, lt_top_iff_ne_top.2 hr⟩⟩

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

  obtain ⟨z, hz⟩ := exists_lt_lt_of_not_cover hbt hbt',
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
begin
  induction hab with a a d b had hdb h,
    { exact hbc },
    { exact h (path.append_left hdb hbc) }
end

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
  split, {
    intro h,
    apply @not_proper_bot α,
    have := x.prop,
    rw ←oiso.map_bot at h,
    rwa oiso.injective h at this },
  intro h,
  apply @not_proper_top α,
  have := x.prop,
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
private lemma covers' (x y : α) : x ⋖ y → oiso x ⋖ oiso y :=
begin
  intro hxy,
  use oiso.strict_mono hxy.left,
  intros z hz,
  have : oiso.symm z ∈ set.Ioo x y,
  { split,
    { have := oiso.symm.strict_mono hz.left,
      simp at this,
      exact this },
    have := oiso.symm.strict_mono hz.right,
    simp at this,
    exact this },
  exact hxy.right _ this
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
  hcovers := begin
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
