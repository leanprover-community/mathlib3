/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import data.sum.basic
import order.basic

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
protected theorem is_total.is_trichotomous (r) [is_total α r] : is_trichotomous α r :=
⟨λ a b, or.left_comm.1 (or.inr $ total_of r a b)⟩

/- Convert algebraic structure style to explicit relation style typeclasses -/
instance [preorder α] : is_refl α (≤) := ⟨le_refl⟩
instance [preorder α] : is_refl α (≥) := is_refl.swap _
instance [preorder α] : is_trans α (≤) := ⟨@le_trans _ _⟩
instance [preorder α] : is_trans α (≥) := is_trans.swap _
instance [preorder α] : is_preorder α (≤) := {}
instance [preorder α] : is_preorder α (≥) := {}
instance [preorder α] : is_irrefl α (<) := ⟨lt_irrefl⟩
instance [preorder α] : is_irrefl α (>) := is_irrefl.swap _
instance [preorder α] : is_trans α (<) := ⟨@lt_trans _ _⟩
instance [preorder α] : is_trans α (>) := is_trans.swap _
instance [preorder α] : is_asymm α (<) := ⟨@lt_asymm _ _⟩
instance [preorder α] : is_asymm α (>) := is_asymm.swap _
instance [preorder α] : is_antisymm α (<) := is_asymm.is_antisymm _
instance [preorder α] : is_antisymm α (>) := is_asymm.is_antisymm _
instance [preorder α] : is_strict_order α (<) := {}
instance [preorder α] : is_strict_order α (>) := {}
instance [partial_order α] : is_antisymm α (≤) := ⟨@le_antisymm _ _⟩
instance [partial_order α] : is_antisymm α (≥) := is_antisymm.swap _
instance [partial_order α] : is_partial_order α (≤) := {}
instance [partial_order α] : is_partial_order α (≥) := {}
instance [linear_order α] : is_total α (≤) := ⟨le_total⟩
instance [linear_order α] : is_total α (≥) := is_total.swap _
instance linear_order.is_total_preorder [linear_order α] : is_total_preorder α (≤) :=
  by apply_instance
instance [linear_order α] : is_total_preorder α (≥) := {}
instance [linear_order α] : is_linear_order α (≤) := {}
instance [linear_order α] : is_linear_order α (≥) := {}
instance [linear_order α] : is_trichotomous α (<) := ⟨lt_trichotomy⟩
instance [linear_order α] : is_trichotomous α (>) := is_trichotomous.swap _
instance [linear_order α] : is_trichotomous α (≤) := is_total.is_trichotomous _
instance [linear_order α] : is_trichotomous α (≥) := is_total.is_trichotomous _

instance order_dual.is_total_le [has_le α] [is_total α (≤)] : is_total (order_dual α) (≤) :=
@is_total.swap α _ _

lemma ne_of_irrefl {r} [is_irrefl α r] : ∀ {x y : α}, r x y → x ≠ y
| _ _ h rfl := irrefl _ h

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

/-- Construct a partial order from a `is_strict_order` relation.

See note [reducible non-instances]. -/
@[reducible] def partial_order_of_SO (r) [is_strict_order α r] : partial_order α :=
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

/-- This is basically the same as `is_strict_total_order`, but that definition has a redundant
assumption `is_incomp_trans α lt`. -/
@[algebra] class is_strict_total_order' (α : Type u) (lt : α → α → Prop)
  extends is_trichotomous α lt, is_strict_order α lt : Prop.

/-- Construct a linear order from an `is_strict_total_order'` relation.

See note [reducible non-instances]. -/
@[reducible]
def linear_order_of_STO' (r) [is_strict_total_order' α r] [Π x y, decidable (¬ r x y)] :
  linear_order α :=
{ le_total := λ x y,
    match y, trichotomous_of r x y with
    | y, or.inl h := or.inl (or.inr h)
    | _, or.inr (or.inl rfl) := or.inl (or.inl rfl)
    | _, or.inr (or.inr h) := or.inr (or.inr h)
    end,
  decidable_le := λ x y, decidable_of_iff (¬ r y x)
    ⟨λ h, ((trichotomous_of r y x).resolve_left h).imp eq.symm id,
      λ h, h.elim (λ h, h ▸ irrefl_of _ _) (asymm_of r)⟩,
  ..partial_order_of_SO r }

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

/-- A well order is a well-founded linear order. -/
@[algebra] class is_well_order (α : Type u) (r : α → α → Prop)
  extends is_strict_total_order' α r : Prop :=
(wf : well_founded r)

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
noncomputable def is_well_order.linear_order (r : α → α → Prop) [is_well_order α r] :
  linear_order α :=
by { letI := λ x y, classical.dec (¬r x y), exact linear_order_of_STO' r }

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

namespace prod

instance is_refl_preimage_fst {r : α → α → Prop} [h : is_refl α r] :
  is_refl (α × α) (prod.fst ⁻¹'o r) := ⟨λ a, refl_of r a.1⟩

instance is_refl_preimage_snd {r : α → α → Prop} [h : is_refl α r] :
  is_refl (α × α) (prod.snd ⁻¹'o r) := ⟨λ a, refl_of r a.2⟩

instance is_trans_preimage_fst {r : α → α → Prop} [h : is_trans α r] :
  is_trans (α × α) (prod.fst ⁻¹'o r) := ⟨λ _ _ _, trans_of r⟩

instance is_trans_preimage_snd {r : α → α → Prop} [h : is_trans α r] :
  is_trans (α × α) (prod.snd ⁻¹'o r) := ⟨λ _ _ _, trans_of r⟩

end prod
