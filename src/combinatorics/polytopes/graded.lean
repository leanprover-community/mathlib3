/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Violeta Hernández Palacios.
-/

import tactic
import order.lattice_intervals
import order.zorn
import category_theory.conj
import data.fin.basic

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

* `polytope.graded`: graded preorders.
* `polytope.path`: a path between two elements in a graph.
* `polytope.total_connected`: connectedness of a bounded poset – see remark on nomenclature.
* `polytope.strong_connected`: strong connectedness of a bounded poset.

## Main results

* `graded.ex_unique_of_grade`: graded linear orders have a unique element of each possible grade.
-/

open category_theory

universe u

/-- One element covers another when there's no other element strictly in between. -/
def polytope.covers {α : Type u} [preorder α] (y x : α) : Prop :=
x < y ∧ ∀ z, ¬ z ∈ set.Ioo x y

notation x ` ⋗ `:50 y:50 := polytope.covers x y
notation x ` ⋖ `:50 y:50 := polytope.covers y x

/-- If `x < y` but `y` does not cover `x`, then there's an element in between. -/
private lemma between_of_ncover {α : Type u} [preorder α] {x y : α} (hnxy : ¬x ⋖ y) (hxy : x < y) :
  ∃ z, x < z ∧ z < y :=
by by_contra hne; push_neg at hne; exact hnxy ⟨hxy, λ z ⟨hl, hr⟩, hne z hl hr⟩

/-- If an element covers another, they define an empty open interval. -/
theorem set.Ioo_is_empty_of_covers {α : Type u} [preorder α] {x y : α} : x ⋖ y → set.Ioo x y = ∅ :=
λ ⟨_, hr⟩, set.eq_empty_iff_forall_not_mem.mpr hr

/-- A natural covers another iff it's a successor. -/
lemma nat.cover_iff_succ {m n : ℕ} : m ⋖ n ↔ n = m + 1 :=
begin
  split,
  { rintro ⟨hmnl, hmnr⟩,
    cases le_or_gt n (m + 1) with hnm hnm,
    exact antisymm hnm (nat.succ_le_of_lt hmnl),
    exact (hmnr _ ⟨lt_add_one m, hnm⟩).elim },
  intro hnm,
  split,
  { rw hnm,
    exact lt_add_one m },
  rintros r ⟨hrl, hrr⟩,
  rw hnm at hrr,
  exact nat.lt_irrefl _ (lt_of_le_of_lt (nat.succ_le_of_lt hrl) hrr),
end

/-- Two `fin`s cover each other iff their values do. -/
lemma fin.cover_iff_cover {n : ℕ} (a b : fin n) : a ⋖ b ↔ a.val ⋖ b.val :=
  ⟨ λ ⟨hl, hr⟩, ⟨hl, λ c hc, (hr ⟨c, lt_trans hc.right b.prop⟩) hc⟩,
  λ ⟨hl, hr⟩, ⟨hl, λ c hc, hr c hc⟩ ⟩

/-- Covering is irreflexive. -/
instance covers.is_irrefl {α : Type u} [preorder α] : is_irrefl α polytope.covers :=
⟨ λ _ ha, ne_of_lt ha.left (refl _) ⟩

/-- A graded order is an order homomorphism into ℕ such that:
    * `⊥` has grade 0
    * the homomorphism respects covering. -/
@[protect_proj]
class polytope.graded (α : Type u) [preorder α] extends order_bot α : Type u :=
(grade : α → ℕ)
(grade_bot : grade ⊥ = 0)
(strict_mono : strict_mono grade)
(hcovers : ∀ {x y}, x ⋖ y → grade y = grade x + 1)

/-- An abbreviation for the grade function of a graded order. -/
abbreviation polytope.grade {α : Type u} [preorder α] [polytope.graded α] : α → ℕ :=
polytope.graded.grade

/-- A natural number that is the grade of some element. -/
abbreviation is_grade (α : Type u) [preorder α] [polytope.graded α] (n : ℕ) : Prop :=
∃ a : α, polytope.grade a = n

/-- Grade is a relation homomorphism. -/
def polytope.graded.rel_hom (α : Type u) [preorder α] [polytope.graded α] : @rel_hom α ℕ (<) (<) :=
⟨_, polytope.graded.strict_mono⟩

/-- Natural numbers are graded. -/
instance : polytope.graded ℕ :=
⟨id, rfl, strict_mono_id, λ _ _, nat.cover_iff_succ.mp⟩

/-- Natural numbers smaller than `n + 1` are graded. -/
instance (n : ℕ) : polytope.graded (fin (n + 1)) :=
{ grade := λ n, n,
  grade_bot := refl _,
  strict_mono := strict_mono_id,
  hcovers := λ _ _ h, nat.cover_iff_succ.mp ((fin.cover_iff_cover _ _).mp h) }

open polytope

namespace nat

/-- A point subdivides an interval into three. -/
private lemma ioo_tricho {a b c : ℕ} (hc : c ∈ set.Ioo a b) (d : ℕ) :
  c = d ∨ c ∈ set.Ioo a d ∨ c ∈ set.Ioo d b :=
begin
  cases eq_or_ne c d with hcd hcd,
    { exact or.inl hcd },
  cases ne.lt_or_lt hcd with ha hb,
    { exact or.inr (or.inl ⟨and.left hc, ha⟩) },
    { exact or.inr (or.inr ⟨hb, and.right hc⟩) }
end

/-- A set of nats without gaps is an interval. The sizes of the gaps and intervals we consider are
    bounded by `n`, so that we may induct on it. -/
private lemma all_ioo_of_ex_ioo {P : ℕ → Prop} (n : ℕ)
  (hP : ∀ a b, b ≤ a + n → P a → P b → nonempty (set.Ioo a b) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) :
  b ≤ a + n → P a → P b → ∀ c ∈ set.Ioo a b, P c :=
begin
  revert a b,
  induction n with n hP',
    { exact λ _ _ hba _ _ _ hci, ((not_lt_of_ge hba) (lt_trans hci.left hci.right)).elim },
  intros a b hba ha hb _ hci,
  rcases hP a b hba ha hb (nonempty.intro ⟨_, hci⟩) with ⟨d, ⟨hdil, hdir⟩, hd⟩,
  cases ioo_tricho hci d with hcd hdb, { rwa ←hcd at hd },
  have hxy : ∃ x y, P x ∧ P y ∧ c ∈ set.Ioo x y ∧ y ≤ x + n := begin
    cases hdb with hcad hcdb,
      { refine ⟨a, d, ha, hd, hcad, _⟩,
        have := lt_of_lt_of_le hdir hba,
        rw nat.add_succ at this,
        exact nat.le_of_lt_succ this },
      { refine ⟨d, b, hd, hb, hcdb, _⟩,
        have := nat.add_le_add hdil rfl.le,
        rw nat.succ_add a n at this,
        exact le_trans hba this }
  end,
  rcases hxy with ⟨x, y, hx, hy, hxy, hyx⟩,
  exact hP' (λ _ _ hba, hP _ _ (hba.trans (nat.le_succ _))) x y hyx hx hy c hxy,
end

/-- A set of nats without gaps is an interval. -/
lemma all_icc_of_ex_ioo {P : ℕ → Prop}
(hP : ∀ a b, P a → P b → (nonempty (set.Ioo a b)) → ∃ c ∈ set.Ioo a b, P c) (a b : ℕ) (ha : P a)
(hb : P b) :
  ∀ c ∈ set.Icc a b, P c :=
begin
  rintros c ⟨hac, hcb⟩,
  cases eq_or_lt_of_le hac with hac hac,
    { rwa ←hac },
  cases eq_or_lt_of_le hcb with hcb hcb,
    { rwa  hcb },
  exact all_ioo_of_ex_ioo b (λ c d _, hP c d) _ _ le_add_self ha hb _ ⟨hac, hcb⟩
end

end nat

/-- A closed non-empty interval of a graded poset is a graded poset. -/
def set.Icc.graded {α : Type u} [partial_order α] [graded α] {x y : α} (h : x ≤ y) :
  graded (set.Icc x y) :=
{ grade := λ a, grade a.val - grade x,
  strict_mono := λ a b h,
    nat.sub_mono_left_strict (graded.strict_mono.monotone a.prop.left) (graded.strict_mono h),
  grade_bot := tsub_eq_zero_iff_le.mpr (refl _),
  hcovers := begin
    rintros ⟨a, ha⟩ ⟨b, hb⟩ ⟨hab, hcov⟩,
    suffices this : ∀ z, z ∉ set.Ioo a b,
      { have : grade b = grade a + 1 := graded.hcovers ⟨hab, this⟩,
        change grade b - grade x = grade a - grade x + 1,
        rw [this, nat.sub_add_comm],
        exact graded.strict_mono.monotone ha.left },
    rintros _ ⟨hl, hr⟩,
    simp at hcov, -- Todo(Vi): Remove this `simp`.
    exact hcov _ (ha.left.trans (le_of_lt hl)) ((le_of_lt hr).trans hb.right) hl hr,
  end,
  ..set.Icc.order_bot h }

/-- A preorder is isomorphic to the section from bottom to top. -/
def set.Icc.self_order_iso_bot_top (α : Type u) [preorder α] [order_bot α] [order_top α] :
  α ≃o set.Icc ⊥ (⊤ : α) :=
{ to_fun := λ x, ⟨x, bot_le, le_top⟩,
  inv_fun := subtype.val,
  left_inv := λ _, rfl,
  right_inv := λ _, subtype.eq rfl,
  map_rel_iff' := by simp }

namespace graded

instance (α : Type u) [preorder α] [ot : order_top α] [g : graded α] : bounded_order α :=
{ ..ot, ..g }

/-- An abbreviation for the grade of `⊤`. -/
abbreviation grade_top (α : Type u) [preorder α] [order_top α] [graded α] : ℕ :=
grade (⊤ : α)

lemma grade_le_grade_top {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
  grade a ≤ grade_top α :=
graded.strict_mono.monotone le_top

lemma dual_cover_iff_cover {α : Type u} [preorder α] (a b : α) :
  a ⋖ b ↔ @polytope.covers (order_dual α) _ a b :=
by split; repeat { exact λ ⟨habl, habr⟩, ⟨habl, λ c ⟨hcl, hcr⟩, habr c ⟨hcr, hcl⟩⟩ }

/-- A partial converse to `hcovers`. -/
lemma covers_of_grade_succ_of_lt {α : Type u} [preorder α] [graded α] {x y : α} :
  x < y → grade y = grade x + 1 → x ⋖ y :=
λ hxy h, ⟨hxy, (λ z ⟨hzl, hzr⟩, (nat.cover_iff_succ.mpr h).right (grade z)
  ⟨graded.strict_mono hzl, graded.strict_mono hzr⟩)⟩

section partial_order

instance (α : Type u) [partial_order α] [order_top α] [graded α] : graded (order_dual α) :=
{ grade := λ a : α, grade_top α - grade a,
  grade_bot := nat.sub_self _,
  strict_mono := begin
    refine λ (a b : α) hab, _,
    have : grade a > grade b := graded.strict_mono hab,
    have := grade_le_grade_top a,
    have := grade_le_grade_top b,
    linarith,
  end,
  hcovers := begin
    refine λ (x y : α) hxy, _,
    change grade x with graded.grade x,
    rw ←dual_cover_iff_cover at hxy,
    rw [graded.hcovers hxy, ←nat.sub_sub,
        nat.sub_add_cancel (tsub_pos_of_lt (graded.strict_mono (lt_of_lt_of_le hxy.left le_top)))]
  end }

variables {α : Type u} [partial_order α] [graded α]

/-- An element has grade 0 iff it is the bottom element. -/
@[simp]
theorem eq_zero_iff_eq_bot (x : α) : grade x = 0 ↔ x = ⊥ :=
begin
  refine ⟨λ h, _, λ h, by cases h; exact graded.grade_bot⟩,
  rw ←@graded.grade_bot α at h,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←bot_lt_iff_ne_bot at hx,
  exact not_le_of_lt (graded.strict_mono hx) (le_of_eq h)
end

/-- If two elements in a graded partial order cover each other, so do their grades. This is just a
    restatement of the covering condition. -/
lemma nat_cover_of_cover {a b : α} : a ⋖ b → grade a ⋖ grade b :=
by rw nat.cover_iff_succ; exact graded.hcovers

variable [order_top α]

/-- An element has the top grade iff it is the top element. -/
@[simp]
theorem eq_grade_top_iff_eq_top (x : α) : grade x = grade_top α ↔ x = ⊤ :=
begin
  refine ⟨λ h, _, λ h, by cases h; refl⟩,
  by_contra hx,
  change _ ≠ _ at hx,
  rw ←lt_top_iff_ne_top at hx,
  exact not_le_of_lt (graded.strict_mono hx) (ge_of_eq h)
end

/-- A grade function into `fin` for `α` with a top element. -/
def grade_fin (x : α) : fin (grade_top α + 1) :=
⟨grade x, by rw nat.lt_add_one_iff; exact grade_le_grade_top _⟩

@[simp]
theorem grade_fin.val_eq (x : α) : (grade_fin x).val = grade x :=
rfl

theorem grade_fin.strict_mono : strict_mono (grade_fin : α → fin (grade_top α + 1)) :=
graded.strict_mono

end partial_order

section linear_order

/-- `grade` is injective for linearly ordered `α`. -/
theorem grade.inj (α : Type u) [linear_order α] [graded α] : function.injective (grade : α → ℕ) :=
graded.strict_mono.injective

variables {α : Type u} [linear_order α] [graded α]

lemma grade_le_iff_le (x y : α) : grade x ≤ grade y ↔ x ≤ y :=
begin
  split,
    { contrapose,
      exact λ hxy, not_le_of_gt (graded.strict_mono (lt_of_not_ge hxy)), },
  exact λ hxy, graded.strict_mono.monotone hxy,
end

/-- `grade` is an order embedding into ℕ for linearly ordered `α`. -/
def oem_nat : α ↪o ℕ :=
{ to_fun := _,
  inj' := grade.inj α,
  map_rel_iff' := grade_le_iff_le }

lemma grade_lt_iff_lt (x y : α) : grade x < grade y ↔ x < y :=
order_embedding.lt_iff_lt oem_nat

lemma grade_eq_iff_eq (x y : α) : grade x = grade y ↔ x = y :=
order_embedding.eq_iff_eq oem_nat

lemma grade_ne_iff_ne (x y : α) : grade x ≠ grade y ↔ x ≠ y :=
not_congr (grade_eq_iff_eq x y)

/-- In linear orders, `hcovers` is an equivalence. -/
lemma covers_iff_grade_eq_succ_grade (a b : α) : a ⋖ b ↔ grade b = grade a + 1 :=
begin
  refine ⟨graded.hcovers, λ hba, _⟩,
  have := nat.lt_of_succ_le (le_of_eq hba.symm),
  rw graded.grade_lt_iff_lt at this,
  exact covers_of_grade_succ_of_lt this hba,
end

/-- Two elements in a linear order cover each other iff their grades do. -/
theorem cover_iff_nat_cover (a b : α) : a ⋖ b ↔ grade a ⋖ grade b :=
begin
  split, { rw nat.cover_iff_succ, exact graded.hcovers },
  intro hab,
  rw nat.cover_iff_succ at hab,
  rwa graded.covers_iff_grade_eq_succ_grade
end

theorem grade_fin.inj [order_top α] : function.injective (grade_fin : α → fin (grade_top α + 1)) :=
grade_fin.strict_mono.injective

/-- `grade_fin` is an order embedding into `fin` for linearly ordered `α` with a top element. -/
def oem_fin [order_top α] : α ↪o fin (grade_top α + 1) :=
{ to_fun := grade_fin,
  inj' := grade_fin.inj,
  map_rel_iff' := grade_le_iff_le }

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
    rw [←graded.grade_lt_iff_lt, ham, hbn],
    exact lt_trans hr.left hr.right,
  end,

  rcases between_of_ncover hnab hab with ⟨c, hac, hcb⟩,
  refine ⟨grade c, ⟨_, ⟨c, rfl⟩⟩⟩,
  split,
    { rw ←ham,
      exact graded.strict_mono hac },
  rw ←hbn,
  exact graded.strict_mono hcb
end

/-- A graded linear order has an element of grade `j` when `j ≤ grade ⊤`. This is generalized to a
    partial order in `ex_of_grade`. -/
lemma ex_of_grade_lin [order_top α] (j : fin (graded.grade_top α + 1)) : is_grade α j :=
(nat.all_icc_of_ex_ioo grade_ioo_lin) _ _ ⟨⊥, graded.grade_bot⟩ ⟨⊤, rfl⟩ _
  ⟨zero_le _, nat.le_of_lt_succ j.prop⟩

/-- A linear order has a unique element of grade `j` when `j ≤ grade ⊤`. -/
theorem ex_unique_of_grade [order_top α] (j : fin (graded.grade_top α + 1)) :
  ∃! a : α, grade a = j :=
begin
  cases ex_of_grade_lin j with a ha,
  use [a, ha],
  intros b hb,
  apply graded.grade.inj _,
  rw [ha, hb]
end

end linear_order

end graded

namespace polytope

/-- Proper elements are those that are maximal nor minimal. -/
def is_proper {α : Type u} [has_lt α] (b : α) : Prop :=
∃ a c, a < b ∧ b < c

/-- The subtype of proper elements. -/
@[reducible]
def proper (α : Type u) [has_lt α] : Type u :=
{a : α // is_proper a}

/-- Proper elements are incident when they're comparable. -/
abbreviation incident {α : Type u} [has_lt α] (a b : proper α) : Prop :=
a.val ≠ b.val → a.val < b.val ∨ b.val < a.val

end polytope

open polytope

namespace graded

/-- The bottom element is improper. -/
lemma bot_improper {α : Type u} [preorder α] [order_bot α] : ¬ is_proper (⊥ : α) :=
λ ⟨_, _, ⟨h, _⟩⟩, not_le_of_gt h bot_le

/-- The top element is improper. -/
lemma top_improper {α : Type u} [preorder α] [order_top α] : ¬ is_proper (⊤ : α) :=
λ ⟨_, _, ⟨_, h⟩⟩, not_le_of_gt h le_top

/-- Elements other than the bottom and top ones are proper. -/
theorem proper_of_ne_bot_top {α : Type u} [preorder α] [bounded_order α] (a : α) :
  polytope.is_proper a → a ≠ ⊥ ∧ a ≠ ⊤ :=
begin
  intro ha,
  split,
  repeat { intro h, rw h at ha, swap },
  exact bot_improper ha,
  exact top_improper ha,
end

/-- The improper elements are exactly the bottom and top ones. -/
theorem proper_iff_ne_bot_top {α : Type u} [partial_order α] [bounded_order α] (a : α) :
  polytope.is_proper a ↔ a ≠ ⊥ ∧ a ≠ ⊤ :=
⟨proper_of_ne_bot_top a, λ ⟨hl, hr⟩, ⟨⊥, ⊤, bot_lt_iff_ne_bot.mpr hl, lt_top_iff_ne_top.mpr hr⟩⟩

/-- An element is proper iff it has a grade between the bottom and top element. -/
theorem proper_iff_grade_iio {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
  is_proper a ↔ grade a ∈ set.Ioo 0 (grade_top α) :=
begin
  rw proper_iff_ne_bot_top,
  split,
    { intro ha,
      cases ha with hal har,
      cases eq_or_lt_of_le (zero_le (grade a)) with h hl,
        { replace h := eq.symm h,
          rw eq_zero_iff_eq_bot at h,
          exact (hal h).elim },
      cases eq_or_lt_of_le (grade_le_grade_top a) with h hr,
        { rw eq_grade_top_iff_eq_top at h,
          exact (har h).elim },
      exact ⟨hl, hr⟩ },
  rintro ⟨hl, hr⟩,
  split,
    { intro ha,
      rw ←eq_zero_iff_eq_bot at ha,
      exact (ne_of_lt hl) (eq.symm ha) },
  intro ha,
  rw ←eq_grade_top_iff_eq_top at ha,
  exact (ne_of_lt hr) ha
end

/-- A `graded` with top grade 1 or less has no proper elements. -/
theorem proper.empty {α : Type u} [partial_order α] [order_top α] [graded α] :
  grade_top α ≤ 1 → is_empty (polytope.proper α) :=
begin
  intro h,
  split,
  rintro ⟨a, ha⟩,
  rw proper_iff_grade_iio at ha,
  refine (not_le_of_lt (lt_of_le_of_lt _ ha.right)) h,
  exact ha.left
end

/-- A `graded` with top grade 2 or more has some proper element. -/
lemma proper.nonempty (α : Type u) [partial_order α] [order_top α] [graded α]
(h : 2 ≤ graded.grade_top α) :
  nonempty (polytope.proper α) :=
begin
  change grade_top α with graded.grade ⊤ at h,

  have hbt : ¬ ⊥ ⋖ ⊤ := begin
    intro hbt,
    have := graded.hcovers hbt,
    rw graded.grade_bot at this,
    rw this at h,
    exact nat.lt_asymm h h,
  end,

  have hbt' : (⊥ : α) < ⊤ := begin
    rw bot_lt_iff_ne_bot,
    intro hbt',
    rw [hbt', graded.grade_bot] at h,
    exact (not_le_of_lt zero_lt_two) h,
  end,

  cases between_of_ncover hbt hbt' with z hz,
  exact ⟨⟨z, ⊥, ⊤, hz⟩⟩,
end

end graded

/-- Two elements of a type are connected by a relation when there exists a path of connected
    elements. This is essentially an inductive version of an equivalence closure. -/
 -- Todo(Vi): If someone else comes up with connected graphs sometime, we might want to rework this.
inductive polytope.path {α : Type u} (r : α → α → Prop) : α → α → Prop
| start (x : α) : polytope.path x x
| next (x y z : α) : polytope.path x y → r y z → polytope.path x z

namespace path
section

variables {α : Type u} {r : α → α → Prop} {a b c : α}

/-- Connectivity is reflexive. -/
@[refl]
theorem refl : path r a a :=
path.start a

/-- Comparable proper elements are connected. -/
theorem from_rel : r a b → path r a b :=
(path.next a a b) (path.refl)

/-- If `a` and `b` are related, and `b` and `c` are connected, then `a` and `c` are connected. -/
lemma append_left (hab : r a b) (hbc : path r b c) : path r a c :=
begin
  induction hbc with _ _ _ _ _ hcd h,
    { exact path.from_rel hab },
    { exact path.next _ _ _ (h hab) hcd }
end

/-- Connectedness with a symmetric relation is symmetric. -/
@[symm]
theorem symm [is_symm α r] (hab : path r a b) : path r b a :=
begin
  induction hab with _ _ _ _ _ hbc hba,
    { exact path.refl },
    { exact path.append_left (is_symm.symm _ _ hbc) hba, }
end

/-- Connectedness is transitive. -/
theorem trans (hab : path r a b) (hbc : path r b c) : path r a c :=
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
abbreviation polytope.connected {α : Type u} [preorder α] (a b : polytope.proper α) : Prop :=
path polytope.incident a b

open polytope

namespace graded

/-- A `graded` is totally connected' when any two proper elements are connected. Note that this
definition requires nothing more than a preorder. -/
def total_connected' (α : Type u) [preorder α] : Prop :=
∀ a b : proper α, connected a b

/-- A `graded` is totally connected when it's of grade 2, or any two proper elements are connected.

Here we deviate from standard nomenclature: mathematicians would just call this connectedness.
However, by doing this, it makes it unambiguous when we're talking about two elements being
connected, and when we're talking about a polytope being totally connected. -/
def total_connected (α : Type u) [preorder α] [order_top α] [graded α] : Prop :=
grade_top α = 2 ∨ total_connected' α

/-- Order isomorphisms preserve proper elements. -/
private lemma proper_order_iso_of_proper {α : Type u} [partial_order α] [order_top α] [graded α]
{β : Type u} [partial_order β] [order_top β] [graded β] (oiso : α ≃o β) (x : proper α) :
  is_proper (oiso x) :=
begin
  rw proper_iff_ne_bot_top (oiso x),
  split, {
    intro h,
    apply @bot_improper α,
    have := x.prop,
    rw ←oiso.map_bot at h,
    rwa oiso.injective h at this,
  },
  intro h,
  apply @top_improper α,
  have := x.prop,
  rw ←oiso.map_top at h,
  rwa oiso.injective h at this,
end

/-- Order isomorphisms preserve proper elements. -/
theorem proper_order_iso_iff_proper {α : Type u} [partial_order α] [order_top α] [graded α]
{β : Type u} [partial_order β] [order_top β] [graded β] (oiso : α ≃o β) (x : α) :
  is_proper x ↔ is_proper (oiso x) :=
begin
  split, {
    exact λ hx, proper_order_iso_of_proper oiso ⟨x, hx⟩,
  },
  intro hx,
  have := proper_order_iso_of_proper oiso.symm ⟨oiso x, hx⟩,
  simp at this,
  exact this,
end

end graded

namespace order_iso

variables {α : Type u} [partial_order α] {β : Type u} [partial_order β] (oiso : α ≃o β)

/-- Order isomorphisms preserve covering. -/
private lemma cover' (x y : α) : x ⋖ y → oiso x ⋖ oiso y :=
begin
  intro hxy,
  use oiso.strict_mono hxy.left,
  intros z hz,
  have : oiso.symm z ∈ set.Ioo x y := begin
    split, {
      have := oiso.symm.strict_mono hz.left,
      simp at this,
      exact this,
    },
    have := oiso.symm.strict_mono hz.right,
    simp at this,
    exact this,
  end,
  exact hxy.right _ this
end

/-- Order isomorphisms preserve covering. -/
theorem cover (x y : α) : x ⋖ y ↔ oiso x ⋖ oiso y :=
begin
  use cover' oiso x y,
  have := cover' oiso.symm (oiso x) (oiso y),
  simp at this,
  exact this,
end

/-- An isomorphism between posets, one of which is graded, is enough to give a grade function for
the other. -/
def graded [order_bot α] [graded β] : graded α :=
{ grade := λ a, @grade β _ _ (oiso a),
  grade_bot := begin
    rw oiso.map_bot,
    exact graded.grade_bot,
  end,
  strict_mono := λ _ _ hab, graded.strict_mono (oiso.strict_mono hab),
  hcovers := begin
    intros x y hxy,
    apply graded.hcovers,
    rwa ←oiso.cover x y,
  end }

/-- An isomorphism between graded posets extends to an isomorphism between sections. -/
def Icc (x y : α) : set.Icc x y ≃o set.Icc (oiso x) (oiso y) :=
{ to_fun := λ a, ⟨oiso.to_fun a.val, (le_iff_le oiso).mpr a.prop.left, (le_iff_le oiso).mpr a.prop.right⟩,
  inv_fun := λ a, ⟨oiso.inv_fun a, begin
    split, {
      have H : oiso.inv_fun (oiso.to_fun x) ≤ oiso.inv_fun a := begin
        change oiso.inv_fun with oiso.symm,
        rw le_iff_le oiso.symm,
        exact a.prop.left,
      end,
      simp at H,
      exact H,
    },
    have H : oiso.inv_fun a ≤ oiso.inv_fun (oiso.to_fun y) := begin
      change oiso.inv_fun with oiso.symm,
      rw le_iff_le oiso.symm,
      exact a.prop.right,
    end,
    simp at H,
    exact H,
  end⟩,
  left_inv := λ _, subtype.eq (by simp),
  right_inv := λ _, subtype.eq (by simp),
  map_rel_iff' := by simp }

variables [order_top α] [polytope.graded α] [order_top β] [polytope.graded β]

/-- The map from proper elements to proper elements given by an order isomorphism. -/
private abbreviation proper_aux : proper α → proper β :=
λ x, ⟨oiso x, (graded.proper_order_iso_iff_proper oiso x).mp x.prop⟩

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
private lemma con_order_iso_of_con {α : Type u} [partial_order α] [order_top α] [graded α]
{β : Type u} [partial_order β] [order_top β] [graded β] (oiso : α ≃o β) (x y : proper α) :
  connected x y → connected (oiso.proper x) (oiso.proper y) :=
begin
  intro hxy,
  induction hxy with _ x y z hxy hyz hxy',
    { exact path.refl },
  apply path.append_right hxy',
  intro hne,
  cases hyz (λ h, hne (congr_arg oiso h : oiso y = oiso z)) with hyz hyz,
    { exact or.inl (oiso.lt_iff_lt.mpr hyz) },
  exact or.inr (oiso.lt_iff_lt.mpr hyz),
end

/-- Two elements are connected iff their maps under an isomorphism are. -/
lemma con_order_iso_iff_con {α : Type u} [partial_order α] [order_top α] [graded α]
{β : Type u} [partial_order β] [order_top β] [graded β] (oiso : α ≃o β) (x y : proper α) :
  connected x y ↔ connected (oiso.proper x) (oiso.proper y) :=
begin
  refine ⟨con_order_iso_of_con oiso x y, _⟩,
  have := con_order_iso_of_con oiso.symm (oiso.proper x) (oiso.proper y),
  rwa [(subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper x)) = x),
       (subtype.eq (oiso.left_inv _) : (oiso.symm.proper (oiso.proper y)) = y)] at this
end

/-- Any `graded` of top grade less or equal to 2 is connected. -/
theorem tcon_of_grade_le_two (α : Type u) [partial_order α] [order_top α] [graded α] :
  grade_top α ≤ 2 → total_connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with ha ha, { exact or.inl ha },
  exact or.inr (λ a, (((proper.empty (nat.le_of_lt_succ ha)).false : proper α → false) a).elim)
end

/-- Asserts that a section of a graded poset is connected'. -/
abbreviation section_connected' {α : Type u} [preorder α] (x y : α) : Prop :=
total_connected' (set.Icc x y)

/-- Asserts that a section of a graded poset is connected. -/
abbreviation section_connected {α : Type u} [partial_order α] [graded α] {x y : α} (hxy : x ≤ y) :
  Prop :=
@total_connected _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy)

/-- A graded poset is strongly connected when all sections are connected. -/
abbreviation strong_connected (α : Type u) [partial_order α] [graded α] : Prop :=
∀ {x y : α} (hxy : x ≤ y), section_connected hxy

end graded
