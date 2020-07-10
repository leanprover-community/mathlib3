/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import data.set.basic

/-!
# Unbundled relation classes

In this file we prove some properties of `is_*` classes defined in `init.algebra.classes`. The main
difference between these classes and the usual order classes (`preorder` etc) is that usual classes
extend `has_le` and/or `has_lt` while these classes take a relation as an explicit argument.

-/

universes u v

variables {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open function

theorem is_refl.swap (r) [is_refl α r] : is_refl α (swap r) := ⟨refl_of r⟩
theorem is_irrefl.swap (r) [is_irrefl α r] : is_irrefl α (swap r) := ⟨irrefl_of r⟩
theorem is_trans.swap (r) [is_trans α r] : is_trans α (swap r) :=
⟨λ a b c h₁ h₂, trans_of r h₂ h₁⟩
theorem is_antisymm.swap (r) [is_antisymm α r] : is_antisymm α (swap r) :=
⟨λ a b h₁ h₂, antisymm h₂ h₁⟩
theorem is_asymm.swap (r) [is_asymm α r] : is_asymm α (swap r) :=
⟨λ a b h₁ h₂, asymm_of r h₂ h₁⟩
theorem is_total.swap (r) [is_total α r] : is_total α (swap r) :=
⟨λ a b, (total_of r a b).swap⟩
theorem is_trichotomous.swap (r) [is_trichotomous α r] : is_trichotomous α (swap r) :=
⟨λ a b, by simpa [swap, or.comm, or.left_comm] using trichotomous_of r a b⟩
theorem is_preorder.swap (r) [is_preorder α r] : is_preorder α (swap r) :=
{..@is_refl.swap α r _, ..@is_trans.swap α r _}
theorem is_strict_order.swap (r) [is_strict_order α r] : is_strict_order α (swap r) :=
{..@is_irrefl.swap α r _, ..@is_trans.swap α r _}
theorem is_partial_order.swap (r) [is_partial_order α r] : is_partial_order α (swap r) :=
{..@is_preorder.swap α r _, ..@is_antisymm.swap α r _}
theorem is_total_preorder.swap (r) [is_total_preorder α r] : is_total_preorder α (swap r) :=
{..@is_preorder.swap α r _, ..@is_total.swap α r _}
theorem is_linear_order.swap (r) [is_linear_order α r] : is_linear_order α (swap r) :=
{..@is_partial_order.swap α r _, ..@is_total.swap α r _}

protected theorem is_asymm.is_antisymm (r) [is_asymm α r] : is_antisymm α r :=
⟨λ x y h₁ h₂, (asymm h₁ h₂).elim⟩
protected theorem is_asymm.is_irrefl [is_asymm α r] : is_irrefl α r :=
⟨λ a h, asymm h h⟩

/- Convert algebraic structure style to explicit relation style typeclasses -/
instance [preorder α] : is_refl α (≤) := ⟨le_refl⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_refl α (≥) := is_refl.swap _
instance [preorder α] : is_trans α (≤) := ⟨@le_trans _ _⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_trans α (≥) := is_trans.swap _
instance [preorder α] : is_preorder α (≤) := {}
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_preorder α (≥) := {}
instance [preorder α] : is_irrefl α (<) := ⟨lt_irrefl⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_irrefl α (>) := is_irrefl.swap _
instance [preorder α] : is_trans α (<) := ⟨@lt_trans _ _⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_trans α (>) := is_trans.swap _
instance [preorder α] : is_asymm α (<) := ⟨@lt_asymm _ _⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_asymm α (>) := is_asymm.swap _
instance [preorder α] : is_antisymm α (<) := is_asymm.is_antisymm _
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_antisymm α (>) := is_asymm.is_antisymm _
instance [preorder α] : is_strict_order α (<) := {}
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [preorder α] : is_strict_order α (>) := {}
instance preorder.is_total_preorder [preorder α] [is_total α (≤)] : is_total_preorder α (≤) := {}
instance [partial_order α] : is_antisymm α (≤) := ⟨@le_antisymm _ _⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [partial_order α] : is_antisymm α (≥) := is_antisymm.swap _
instance [partial_order α] : is_partial_order α (≤) := {}
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [partial_order α] : is_partial_order α (≥) := {}
instance [linear_order α] : is_total α (≤) := ⟨le_total⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [linear_order α] : is_total α (≥) := is_total.swap _
instance linear_order.is_total_preorder [linear_order α] : is_total_preorder α (≤) :=
  by apply_instance
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [linear_order α] : is_total_preorder α (≥) := {}
instance [linear_order α] : is_linear_order α (≤) := {}
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [linear_order α] : is_linear_order α (≥) := {}
instance [linear_order α] : is_trichotomous α (<) := ⟨lt_trichotomy⟩
@[nolint ge_or_gt] -- see Note [nolint_ge]
instance [linear_order α] : is_trichotomous α (>) := is_trichotomous.swap _

lemma trans_trichotomous_left [is_trans α r] [is_trichotomous α r] {a b c : α} :
  ¬r b a → r b c → r a c :=
begin
  intros h₁ h₂, rcases trichotomous_of r a b with h₃|h₃|h₃,
  exact trans h₃ h₂, rw h₃, exact h₂, exfalso, exact h₁ h₃
end

lemma trans_trichotomous_right [is_trans α r] [is_trichotomous α r] {a b c : α} :
  r a b → ¬r c b → r a c :=
begin
  intros h₁ h₂, rcases trichotomous_of r b c with h₃|h₃|h₃,
  exact trans h₁ h₃, rw ←h₃, exact h₁, exfalso, exact h₂ h₃
end

/-- Construct a partial order from a `is_strict_order` relation -/
def partial_order_of_SO (r) [is_strict_order α r] : partial_order α :=
{ le := λ x y, x = y ∨ r x y,
  lt := r,
  le_refl := λ x, or.inl rfl,
  le_trans := λ x y z h₁ h₂,
    match y, z, h₁, h₂ with
    | _, _, or.inl rfl, h₂ := h₂
    | _, _, h₁, or.inl rfl := h₁
    | _, _, or.inr h₁, or.inr h₂ := or.inr (trans h₁ h₂)
    end,
  le_antisymm := λ x y h₁ h₂,
    match y, h₁, h₂ with
    | _, or.inl rfl, h₂ := rfl
    | _, h₁, or.inl rfl := rfl
    | _, or.inr h₁, or.inr h₂ := (asymm h₁ h₂).elim
    end,
  lt_iff_le_not_le := λ x y,
    ⟨λ h, ⟨or.inr h, not_or
      (λ e, by rw e at h; exact irrefl _ h)
      (asymm h)⟩,
    λ ⟨h₁, h₂⟩, h₁.resolve_left (λ e, h₂ $ e ▸ or.inl rfl)⟩ }

section prio
set_option default_priority 100 -- see Note [default priority]
/-- This is basically the same as `is_strict_total_order`, but that definition is
  in Type (probably by mistake) and also has redundant assumptions. -/
@[algebra] class is_strict_total_order' (α : Type u) (lt : α → α → Prop)
  extends is_trichotomous α lt, is_strict_order α lt : Prop.
end prio

/-- Construct a linear order from a `is_strict_total_order'` relation -/
def linear_order_of_STO' (r) [is_strict_total_order' α r] : linear_order α :=
{ le_total := λ x y,
    match y, trichotomous_of r x y with
    | y, or.inl h := or.inl (or.inr h)
    | _, or.inr (or.inl rfl) := or.inl (or.inl rfl)
    | _, or.inr (or.inr h) := or.inr (or.inr h)
    end,
  ..partial_order_of_SO r }

/-- Construct a decidable linear order from a `is_strict_total_order'` relation -/
def decidable_linear_order_of_STO' (r) [is_strict_total_order' α r] [decidable_rel r] :
  decidable_linear_order α :=
by letI LO := linear_order_of_STO' r; exact
{ decidable_le := λ x y, decidable_of_iff (¬ r y x) (@not_lt _ _ y x),
  ..LO }

theorem is_strict_total_order'.swap (r) [is_strict_total_order' α r] :
  is_strict_total_order' α (swap r) :=
{..is_trichotomous.swap r, ..is_strict_order.swap r}

instance [linear_order α] : is_strict_total_order' α (<) := {}

/-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`.
  This is recognizable as an intuitionistic substitute for `a ≤ b ∨ b ≤ a` on
  the constructive reals, and is also known as negative transitivity,
  since the contrapositive asserts transitivity of the relation `¬ a < b`.  -/
@[algebra] class is_order_connected (α : Type u) (lt : α → α → Prop) : Prop :=
(conn : ∀ a b c, lt a c → lt a b ∨ lt b c)

theorem is_order_connected.neg_trans {r : α → α → Prop} [is_order_connected α r]
  {a b c} (h₁ : ¬ r a b) (h₂ : ¬ r b c) : ¬ r a c :=
mt (is_order_connected.conn a b c) $ by simp [h₁, h₂]

theorem is_strict_weak_order_of_is_order_connected [is_asymm α r]
  [is_order_connected α r] : is_strict_weak_order α r :=
{ trans := λ a b c h₁ h₂, (is_order_connected.conn _ c _ h₁).resolve_right (asymm h₂),
  incomp_trans := λ a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩,
    ⟨is_order_connected.neg_trans h₁ h₃, is_order_connected.neg_trans h₄ h₂⟩,
  ..@is_asymm.is_irrefl α r _ }

@[priority 100] -- see Note [lower instance priority]
instance is_order_connected_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_order_connected α r :=
⟨λ a b c h, (trichotomous _ _).imp_right (λ o,
  o.elim (λ e, e ▸ h) (λ h', trans h' h))⟩

@[priority 100] -- see Note [lower instance priority]
instance is_strict_total_order_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_strict_total_order α r :=
{..is_strict_weak_order_of_is_order_connected}

instance [linear_order α] : is_strict_total_order α (<) := by apply_instance
instance [linear_order α] : is_order_connected α (<) := by apply_instance
instance [linear_order α] : is_incomp_trans α (<) := by apply_instance
instance [linear_order α] : is_strict_weak_order α (<) := by apply_instance

/-- An extensional relation is one in which an element is determined by its set
  of predecessors. It is named for the `x ∈ y` relation in set theory, whose
  extensionality is one of the first axioms of ZFC. -/
@[algebra] class is_extensional (α : Type u) (r : α → α → Prop) : Prop :=
(ext : ∀ a b, (∀ x, r x a ↔ r x b) → a = b)

@[priority 100] -- see Note [lower instance priority]
instance is_extensional_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_extensional α r :=
⟨λ a b H, ((@trichotomous _ r _ a b)
  .resolve_left $ mt (H _).2 (irrefl a))
  .resolve_right $ mt (H _).1 (irrefl b)⟩

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A well order is a well-founded linear order. -/
@[algebra] class is_well_order (α : Type u) (r : α → α → Prop)
  extends is_strict_total_order' α r : Prop :=
(wf : well_founded r)
end prio

@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_strict_total_order {α} (r : α → α → Prop) [is_well_order α r] :
  is_strict_total_order α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_extensional {α} (r : α → α → Prop) [is_well_order α r] :
  is_extensional α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_trichotomous {α} (r : α → α → Prop) [is_well_order α r] :
  is_trichotomous α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_trans {α} (r : α → α → Prop) [is_well_order α r] :
  is_trans α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_irrefl {α} (r : α → α → Prop) [is_well_order α r] :
  is_irrefl α r := by apply_instance
@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_asymm {α} (r : α → α → Prop) [is_well_order α r] :
  is_asymm α r := by apply_instance

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def is_well_order.decidable_linear_order (r : α → α → Prop) [is_well_order α r] :
  decidable_linear_order α :=
by { haveI := linear_order_of_STO' r, exact classical.DLO α }

instance empty_relation.is_well_order [subsingleton α] : is_well_order α empty_relation :=
{ trichotomous := λ a b, or.inr $ or.inl $ subsingleton.elim _ _,
  irrefl       := λ a, id,
  trans        := λ a b c, false.elim,
  wf           := ⟨λ a, ⟨_, λ y, false.elim⟩⟩ }

instance nat.lt.is_well_order : is_well_order ℕ (<) := ⟨nat.lt_wf⟩

instance sum.lex.is_well_order [is_well_order α r] [is_well_order β s] :
  is_well_order (α ⊕ β) (sum.lex r s) :=
{ trichotomous := λ a b, by cases a; cases b; simp; apply trichotomous,
  irrefl       := λ a, by cases a; simp; apply irrefl,
  trans        := λ a b c, by cases a; cases b; simp; cases c; simp; apply trans,
  wf           := sum.lex_wf is_well_order.wf is_well_order.wf }

instance prod.lex.is_well_order [is_well_order α r] [is_well_order β s] :
  is_well_order (α × β) (prod.lex r s) :=
{ trichotomous := λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
    match @trichotomous _ r _ a₁ b₁ with
    | or.inl h₁ := or.inl $ prod.lex.left _ _ h₁
    | or.inr (or.inr h₁) := or.inr $ or.inr $ prod.lex.left _ _ h₁
    | or.inr (or.inl e) := e ▸  match @trichotomous _ s _ a₂ b₂ with
      | or.inl h := or.inl $ prod.lex.right _ h
      | or.inr (or.inr h) := or.inr $ or.inr $ prod.lex.right _ h
      | or.inr (or.inl e) := e ▸ or.inr $ or.inl rfl
      end
    end,
  irrefl := λ ⟨a₁, a₂⟩ h, by cases h with _ _ _ _ h _ _ _ h;
     [exact irrefl _ h, exact irrefl _ h],
  trans := λ a b c h₁ h₂, begin
    cases h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab;
    cases h₂ with _ _ c₁ c₂ bc _ _ c₂ bc,
    { exact prod.lex.left _ _ (trans ab bc) },
    { exact prod.lex.left _ _ ab },
    { exact prod.lex.left _ _ bc },
    { exact prod.lex.right _ (trans ab bc) }
  end,
  wf := prod.lex_wf is_well_order.wf is_well_order.wf }

/-- An unbounded or cofinal set -/
def unbounded (r : α → α → Prop) (s : set α) : Prop := ∀ a, ∃ b ∈ s, ¬ r b a
/-- A bounded or final set -/
def bounded (r : α → α → Prop) (s : set α) : Prop := ∃a, ∀ b ∈ s, r b a

@[simp] lemma not_bounded_iff {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s :=
begin
  classical,
  simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]
end

@[simp] lemma not_unbounded_iff {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
by { classical, rw [not_iff_comm, not_bounded_iff] }

namespace well_founded
/-- If `r` is a well-founded relation, then any nonempty set has a minimal element
with respect to `r`. -/
theorem has_min {α} {r : α → α → Prop} (H : well_founded r)
  (s : set α) : s.nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬ r x a
| ⟨a, ha⟩ := (acc.rec_on (H.apply a) $ λ x _ IH, classical.not_imp_not.1 $ λ hne hx, hne $
  ⟨x, hx, λ y hy hyx, hne $ IH y hyx hy⟩) ha

/-- A minimal element of a nonempty set in a well-founded order -/
noncomputable def min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : α :=
classical.some (H.has_min p h)

theorem min_mem {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) : H.min p h ∈ p :=
let ⟨h, _⟩ := classical.some_spec (H.has_min p h) in h

theorem not_lt_min {α} {r : α → α → Prop} (H : well_founded r)
  (p : set α) (h : p.nonempty) {x} (xp : x ∈ p) : ¬ r x (H.min p h) :=
let ⟨_, h'⟩ := classical.some_spec (H.has_min p h) in h' _ xp

open set
/-- The supremum of a bounded, well-founded order -/
protected noncomputable def sup {α} {r : α → α → Prop} (wf : well_founded r) (s : set α)
  (h : bounded r s) : α :=
wf.min { x | ∀a ∈ s, r a x } h

protected lemma lt_sup {α} {r : α → α → Prop} (wf : well_founded r) {s : set α} (h : bounded r s)
  {x} (hx : x ∈ s) : r x (wf.sup s h) :=
min_mem wf { x | ∀a ∈ s, r a x } h x hx

section
open_locale classical
/-- A successor of an element `x` in a well-founded order is a minimal element `y` such that
`x < y` if one exists. Otherwise it is `x` itself. -/
protected noncomputable def succ {α} {r : α → α → Prop} (wf : well_founded r) (x : α) : α :=
if h : ∃y, r x y then wf.min { y | r x y } h else x

protected lemma lt_succ {α} {r : α → α → Prop} (wf : well_founded r) {x : α} (h : ∃y, r x y) :
  r x (wf.succ x) :=
by { rw [well_founded.succ, dif_pos h], apply min_mem }
end

protected lemma lt_succ_iff {α} {r : α → α → Prop} [wo : is_well_order α r] {x : α} (h : ∃y, r x y)
  (y : α) : r y (wo.wf.succ x) ↔ r y x ∨ y = x :=
begin
  split,
  { intro h', have : ¬r x y,
    { intro hy, rw [well_founded.succ, dif_pos] at h',
      exact wo.wf.not_lt_min _ h hy h' },
    rcases trichotomous_of r x y with hy | hy | hy,
    exfalso, exact this hy,
    right, exact hy.symm,
    left, exact hy },
  rintro (hy | rfl), exact trans hy (wo.wf.lt_succ h), exact wo.wf.lt_succ h
end

end well_founded
