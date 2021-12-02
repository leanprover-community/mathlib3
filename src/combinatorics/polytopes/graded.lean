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
# Flags of polytopes

In this file we define flags, which are maximal chains of a partial order. We prove that
automorphisms of posets induces a group action on flags. We also prove that flags contain elements
of each possible grade.

Todo(Vi): We have done so much since I wrote this three or so days ago! We need to update this.
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
  ⟨ λ ⟨hl, hr⟩, ⟨hl, λ c hc, (hr ⟨c, lt_trans hc.right b.property⟩) hc⟩,
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
def polytope.graded.rel_hom (α : Type u) [preorder α] [bg : polytope.graded α] :
  @rel_hom α ℕ (<) (<) :=
⟨_, bg.strict_mono⟩

instance : polytope.graded ℕ :=
⟨id, rfl, strict_mono_id, λ _ _, nat.cover_iff_succ.mp⟩

instance (n : ℕ) : polytope.graded (fin (n + 1)) :=
{ grade := λ n, n,
  grade_bot := refl _,
  strict_mono := strict_mono_id,
  hcovers := begin
    intros x y,
    rw fin.cover_iff_cover,
    exact nat.cover_iff_succ.mp,
  end }

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
theorem set.Icc.self_order_iso_bot_top {α : Type u} [preorder α] [order_bot α] [order_top α] :
  α ≃o set.Icc ⊥ (⊤ : α) :=
begin
  split,
  swap,
  exact ⟨(λ x, ⟨x, bot_le, le_top⟩), (λ x, x.val), (λ _, rfl), (λ _, subtype.eq rfl)⟩,
  simp,
end

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
  refine ⟨this, λ z, _⟩,
  rintros ⟨hzl, hzr⟩,
  rw ←nat.cover_iff_succ at hba,
  rw ←graded.grade_lt_iff_lt at hzl,
  rw ←graded.grade_lt_iff_lt at hzr,
  exact hba.right _ ⟨hzl, hzr⟩,
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
theorem ex_of_grade_lin [order_top α] (j : fin (graded.grade_top α + 1)) : is_grade α j :=
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
def is_proper {α : Type u} [preorder α] (b : α) : Prop :=
∃ a c, a < b ∧ b < c

/-- The subtype of proper elements. -/
@[reducible]
def proper (α : Type u) [preorder α] : Type u :=
{a : α // is_proper a}

/-- Proper elements are incident when they're comparable. -/
abbreviation incident {α : Type u} [preorder α] (a b : proper α) : Prop :=
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

/-- The improper elements are exactly the bottom and top ones. -/
theorem proper_iff_ne_bot_top {α : Type u} [partial_order α] [bounded_order α] (a : α) :
  polytope.is_proper a ↔ a ≠ ⊥ ∧ a ≠ ⊤ :=
begin
  split,
  { intro ha,
    split,
    { intro h,
      rw h at ha,
      exact bot_improper ha },
    intro h,
    rw h at ha,
    exact top_improper ha },
  exact λ ⟨hal, har⟩, ⟨⊥, ⊤, bot_lt_iff_ne_bot.mpr hal, lt_top_iff_ne_top.mpr har⟩,
end

/-- An element is proper iff it has a grade between the bottom and top element. -/
lemma proper_iff_grade_iio {α : Type u} [partial_order α] [order_top α] [graded α] (a : α) :
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
abbreviation polytope.connected {α : Type u} [preorder α]
  (a b : polytope.proper α) : Prop :=
path polytope.incident a b

open polytope

namespace graded

/-- A `graded` is connected' when any two proper elements are connected. Note that this definition
    requires nothing more than a preorder. -/
protected def connected' (α : Type u) [preorder α] : Prop :=
∀ a b : proper α, connected a b

/-- A `graded` is connected when it's of grade 2, or any two proper elements are connected. -/
protected def connected (α : Type u) [preorder α] [order_top α] [graded α] : Prop :=
grade_top α = 2 ∨ graded.connected' α

/-- Any `graded` of top grade less or equal to 2 is connected. -/
theorem connected_of_grade_le_two (α : Type u) [partial_order α] [order_top α] [graded α] :
  grade_top α ≤ 2 → graded.connected α :=
begin
  intro h,
  cases eq_or_lt_of_le h with ha ha, { exact or.inl ha },
  have := (proper.empty (nat.le_of_lt_succ ha)).false,
  exact or.inr (λ a, (this a).elim)
end

/-- Asserts that a section of a graded poset is connected'. -/
abbreviation section_connected' {α : Type u} [preorder α] (x y : α) : Prop :=
graded.connected' (set.Icc x y)

/-- Asserts that a section of a graded poset is connected. -/
abbreviation section_connected {α : Type u} [partial_order α] [graded α] {x y : α} (hxy : x ≤ y) :
  Prop :=
@graded.connected _ _ (set.Icc.order_top hxy) (set.Icc.graded hxy)

/-- A graded poset is strongly connected when all sections are connected. -/
abbreviation strong_connected (α : Type u) [partial_order α] [graded α] : Prop :=
∀ {x y : α} (hxy : x ≤ y), section_connected hxy

/-- Strong connectedness implies connectedness. -/
theorem connected_of_strong_connected (α : Type u) [partial_order α] [order_top α] [graded α] :
  strong_connected α → graded.connected α :=
begin
  intro h,
  have hs := h (bot_le : ⊥ ≤ ⊤),
  cases hs with hs hs, {
    left,
    rw ←hs,
    change grade_top α with graded.grade ⊤,
    sorry,
  },
  sorry
end

end graded
