/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury G. Kudryashov
-/
import order.basic
import logic.is_empty

/-!
# Unbundled relation classes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove some properties of `is_*` classes defined in `init.algebra.classes`. The main
difference between these classes and the usual order classes (`preorder` etc) is that usual classes
extend `has_le` and/or `has_lt` while these classes take a relation as an explicit argument.

-/

universes u v

variables {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

open function

lemma of_eq [is_refl α r] : ∀ {a b}, a = b → r a b | _ _ ⟨h⟩ := refl _

lemma comm [is_symm α r] {a b : α} : r a b ↔ r b a := ⟨symm, symm⟩
lemma antisymm' [is_antisymm α r] {a b : α} : r a b → r b a → b = a := λ h h', antisymm h' h

lemma antisymm_iff [is_refl α r] [is_antisymm α r] {a b : α} : r a b ∧ r b a ↔ a = b :=
⟨λ h, antisymm h.1 h.2, by { rintro rfl, exact ⟨refl _, refl _⟩ }⟩

/-- A version of `antisymm` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
@[elab_simple]
lemma antisymm_of (r : α → α → Prop) [is_antisymm α r] {a b : α} : r a b → r b a → a = b := antisymm

/-- A version of `antisymm'` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
@[elab_simple]
lemma antisymm_of' (r : α → α → Prop) [is_antisymm α r] {a b : α} : r a b → r b a → b = a :=
antisymm'

/-- A version of `comm` with `r` explicit.

This lemma matches the lemmas from lean core in `init.algebra.classes`, but is missing there.  -/
lemma comm_of (r : α → α → Prop) [is_symm α r] {a b : α} : r a b ↔ r b a := comm

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

@[priority 100]  -- see Note [lower instance priority]
instance is_total.to_is_refl (r) [is_total α r] : is_refl α r :=
⟨λ a, (or_self _).1 $ total_of r a a⟩

lemma ne_of_irrefl {r} [is_irrefl α r] : ∀ {x y : α}, r x y → x ≠ y | _ _ h rfl := irrefl _ h
lemma ne_of_irrefl' {r} [is_irrefl α r] : ∀ {x y : α}, r x y → y ≠ x | _ _ h rfl := irrefl _ h

lemma not_rel_of_subsingleton (r) [is_irrefl α r] [subsingleton α] (x y) : ¬ r x y :=
subsingleton.elim x y ▸ irrefl x

lemma rel_of_subsingleton (r) [is_refl α r] [subsingleton α] (x y) : r x y :=
subsingleton.elim x y ▸ refl x

@[simp] lemma empty_relation_apply (a b : α) : empty_relation a b ↔ false := iff.rfl

lemma eq_empty_relation (r) [is_irrefl α r] [subsingleton α] : r = empty_relation :=
funext₂ $ by simpa using not_rel_of_subsingleton r

instance : is_irrefl α empty_relation := ⟨λ a, id⟩

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

lemma transitive_of_trans (r : α → α → Prop) [is_trans α r] : transitive r := λ _ _ _, trans

/-- In a trichotomous irreflexive order, every element is determined by the set of predecessors. -/
lemma extensional_of_trichotomous_of_irrefl (r : α → α → Prop) [is_trichotomous α r] [is_irrefl α r]
  {a b : α} (H : ∀ x, r x a ↔ r x b) : a = b :=
((@trichotomous _ r _ a b)
  .resolve_left $ mt (H _).2 $ irrefl a)
  .resolve_right $ mt (H _).1 $ irrefl b

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

/-- Construct a linear order from an `is_strict_total_order` relation.

See note [reducible non-instances]. -/
@[reducible]
def linear_order_of_STO (r) [is_strict_total_order α r] [Π x y, decidable (¬ r x y)] :
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

theorem is_strict_total_order.swap (r) [is_strict_total_order α r] :
  is_strict_total_order α (swap r) :=
{..is_trichotomous.swap r, ..is_strict_order.swap r}

/-! ### Order connection -/

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
instance is_order_connected_of_is_strict_total_order
  [is_strict_total_order α r] : is_order_connected α r :=
⟨λ a b c h, (trichotomous _ _).imp_right (λ o,
  o.elim (λ e, e ▸ h) (λ h', trans h' h))⟩

@[priority 100] -- see Note [lower instance priority]
instance is_strict_weak_order_of_is_strict_total_order
  [is_strict_total_order α r] : is_strict_weak_order α r :=
{ ..is_strict_weak_order_of_is_order_connected }

/-! ### Well-order -/

/-- A well-founded relation. Not to be confused with `is_well_order`. -/
@[algebra, mk_iff] class is_well_founded (α : Type u) (r : α → α → Prop) : Prop :=
(wf : well_founded r)

instance has_well_founded.is_well_founded [h : has_well_founded α] :
  is_well_founded α has_well_founded.r := { ..h }

namespace is_well_founded
variables (r) [is_well_founded α r]

/-- Induction on a well-founded relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, r y x → C y) → C x) → C a :=
wf.induction

/-- All values are accessible under the well-founded relation. -/
theorem apply : ∀ a, acc r a := wf.apply

/-- Creates data, given a way to generate a value from all that compare as less under a well-founded
relation. See also `is_well_founded.fix_eq`. -/
def fix {C : α → Sort*} : (Π (x : α), (Π (y : α), r y x → C y) → C x) → Π (x : α), C x := wf.fix

/-- The value from `is_well_founded.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : Π (x : α), (Π (y : α), r y x → C y) → C x) :
  ∀ x, fix r F x = F x (λ y h, fix r F y) :=
wf.fix_eq F

/-- Derive a `has_well_founded` instance from an `is_well_founded` instance. -/
def to_has_well_founded : has_well_founded α := ⟨r, is_well_founded.wf⟩

end is_well_founded

theorem well_founded.asymmetric {α : Sort*} {r : α → α → Prop} (h : well_founded r) :
  ∀ ⦃a b⦄, r a b → ¬ r b a
| a := λ b hab hba, well_founded.asymmetric hba hab
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, h⟩],
                     dec_tac := tactic.assumption }

@[priority 100] -- see Note [lower instance priority]
instance is_well_founded.is_asymm (r : α → α → Prop) [is_well_founded α r] : is_asymm α r :=
⟨is_well_founded.wf.asymmetric⟩

@[priority 100] -- see Note [lower instance priority]
instance is_well_founded.is_irrefl (r : α → α → Prop) [is_well_founded α r] : is_irrefl α r :=
is_asymm.is_irrefl

/-- A class for a well founded relation `<`. -/
@[reducible] def well_founded_lt (α : Type*) [has_lt α] : Prop := is_well_founded α (<)

/-- A class for a well founded relation `>`. -/
@[reducible] def well_founded_gt (α : Type*) [has_lt α] : Prop := is_well_founded α (>)

@[priority 100] -- See note [lower instance priority]
instance (α : Type*) [has_lt α] [h : well_founded_lt α] : well_founded_gt αᵒᵈ := h
@[priority 100] -- See note [lower instance priority]
instance (α : Type*) [has_lt α] [h : well_founded_gt α] : well_founded_lt αᵒᵈ := h

theorem well_founded_gt_dual_iff (α : Type*) [has_lt α] : well_founded_gt αᵒᵈ ↔ well_founded_lt α :=
⟨λ h, ⟨h.wf⟩, λ h, ⟨h.wf⟩⟩
theorem well_founded_lt_dual_iff (α : Type*) [has_lt α] : well_founded_lt αᵒᵈ ↔ well_founded_gt α :=
⟨λ h, ⟨h.wf⟩, λ h, ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
@[algebra] class is_well_order (α : Type u) (r : α → α → Prop)
  extends is_trichotomous α r, is_trans α r, is_well_founded α r : Prop

@[priority 100] -- see Note [lower instance priority]
instance is_well_order.is_strict_total_order {α} (r : α → α → Prop) [is_well_order α r] :
  is_strict_total_order α r := { }
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

namespace well_founded_lt
variables [has_lt α] [well_founded_lt α]

/-- Inducts on a well-founded `<` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, y < x → C y) → C x) → C a :=
is_well_founded.induction _

/-- All values are accessible under the well-founded `<`. -/
theorem apply : ∀ a : α, acc (<) a := is_well_founded.apply _

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`well_founded_lt.fix_eq`. -/
def fix {C : α → Sort*} : (Π (x : α), (Π (y : α), y < x → C y) → C x) → Π (x : α), C x :=
is_well_founded.fix (<)

/-- The value from `well_founded_lt.fix` is built from the previous ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : Π (x : α), (Π (y : α), y < x → C y) → C x) :
  ∀ x, fix F x = F x (λ y h, fix F y) :=
is_well_founded.fix_eq _ F

/-- Derive a `has_well_founded` instance from a `well_founded_lt` instance. -/
def to_has_well_founded : has_well_founded α := is_well_founded.to_has_well_founded (<)

end well_founded_lt

namespace well_founded_gt
variables [has_lt α] [well_founded_gt α]

/-- Inducts on a well-founded `>` relation. -/
theorem induction {C : α → Prop} : ∀ a, (∀ x, (∀ y, x < y → C y) → C x) → C a :=
is_well_founded.induction _

/-- All values are accessible under the well-founded `>`. -/
theorem apply : ∀ a : α, acc (>) a := is_well_founded.apply _

/-- Creates data, given a way to generate a value from all that compare as greater. See also
`well_founded_gt.fix_eq`. -/
def fix {C : α → Sort*} : (Π (x : α), (Π (y : α), x < y → C y) → C x) → Π (x : α), C x :=
is_well_founded.fix (>)

/-- The value from `well_founded_gt.fix` is built from the successive ones as specified. -/
theorem fix_eq {C : α → Sort*} (F : Π (x : α), (Π (y : α), x < y → C y) → C x) :
  ∀ x, fix F x = F x (λ y h, fix F y) :=
is_well_founded.fix_eq _ F

/-- Derive a `has_well_founded` instance from a `well_founded_gt` instance. -/
def to_has_well_founded : has_well_founded α := is_well_founded.to_has_well_founded (>)

end well_founded_gt

/-- Construct a decidable linear order from a well-founded linear order. -/
noncomputable def is_well_order.linear_order (r : α → α → Prop) [is_well_order α r] :
  linear_order α :=
by { letI := λ x y, classical.dec (¬r x y), exact linear_order_of_STO r }

/-- Derive a `has_well_founded` instance from a `is_well_order` instance. -/
def is_well_order.to_has_well_founded [has_lt α] [hwo : is_well_order α (<)] :
  has_well_founded α := { r := (<), wf := hwo.wf }

-- This isn't made into an instance as it loops with `is_irrefl α r`.
theorem subsingleton.is_well_order [subsingleton α] (r : α → α → Prop) [hr : is_irrefl α r] :
  is_well_order α r :=
{ trichotomous := λ a b, or.inr $ or.inl $ subsingleton.elim a b,
  trans        := λ a b c h, (not_rel_of_subsingleton r a b h).elim,
  wf           := ⟨λ a, ⟨_, λ y h, (not_rel_of_subsingleton r y a h).elim⟩⟩,
  ..hr }

instance empty_relation.is_well_order [subsingleton α] : is_well_order α empty_relation :=
subsingleton.is_well_order _

@[priority 100]
instance is_empty.is_well_order [is_empty α] (r : α → α → Prop) : is_well_order α r :=
{ trichotomous := is_empty_elim,
  trans        := is_empty_elim,
  wf           := well_founded_of_empty r }

instance prod.lex.is_well_founded [is_well_founded α r] [is_well_founded β s] :
  is_well_founded (α × β) (prod.lex r s) :=
⟨prod.lex_wf is_well_founded.wf is_well_founded.wf⟩

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
  trans := λ a b c h₁ h₂, begin
    cases h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab;
    cases h₂ with _ _ c₁ c₂ bc _ _ c₂ bc,
    { exact prod.lex.left _ _ (trans ab bc) },
    { exact prod.lex.left _ _ ab },
    { exact prod.lex.left _ _ bc },
    { exact prod.lex.right _ (trans ab bc) }
  end,
  wf := prod.lex_wf is_well_founded.wf is_well_founded.wf }

instance inv_image.is_well_founded (r : α → α → Prop) [is_well_founded α r] (f : β → α) :
  is_well_founded _ (inv_image r f) :=
⟨inv_image.wf f is_well_founded.wf⟩

instance measure.is_well_founded (f : α → ℕ) : is_well_founded _ (measure f) := ⟨measure_wf f⟩

theorem subrelation.is_well_founded (r : α → α → Prop) [is_well_founded α r] {s : α → α → Prop}
  (h : subrelation s r) : is_well_founded α s :=
⟨h.wf is_well_founded.wf⟩

namespace set

/-- An unbounded or cofinal set. -/
def unbounded (r : α → α → Prop) (s : set α) : Prop := ∀ a, ∃ b ∈ s, ¬ r b a
/-- A bounded or final set. Not to be confused with `metric.bounded`. -/
def bounded (r : α → α → Prop) (s : set α) : Prop := ∃ a, ∀ b ∈ s, r b a

@[simp] lemma not_bounded_iff {r : α → α → Prop} (s : set α) : ¬bounded r s ↔ unbounded r s :=
by simp only [bounded, unbounded, not_forall, not_exists, exists_prop, not_and, not_not]

@[simp] lemma not_unbounded_iff {r : α → α → Prop} (s : set α) : ¬unbounded r s ↔ bounded r s :=
by rw [not_iff_comm, not_bounded_iff]

lemma unbounded_of_is_empty [is_empty α] {r : α → α → Prop} (s : set α) : unbounded r s :=
is_empty_elim

end set

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

/-! ### Strict-non strict relations -/

/-- An unbundled relation class stating that `r` is the nonstrict relation corresponding to the
strict relation `s`. Compare `preorder.lt_iff_le_not_le`. This is mostly meant to provide dot
notation on `(⊆)` and `(⊂)`. -/
class is_nonstrict_strict_order (α : Type*) (r s : α → α → Prop) :=
(right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬ r b a)

lemma right_iff_left_not_left {r s : α → α → Prop} [is_nonstrict_strict_order α r s] {a b : α} :
  s a b ↔ r a b ∧ ¬ r b a :=
is_nonstrict_strict_order.right_iff_left_not_left _ _

/-- A version of `right_iff_left_not_left` with explicit `r` and `s`. -/
lemma right_iff_left_not_left_of (r s : α → α → Prop) [is_nonstrict_strict_order α r s] {a b : α} :
  s a b ↔ r a b ∧ ¬ r b a :=
right_iff_left_not_left

-- The free parameter `r` is strictly speaking not uniquely determined by `s`, but in practice it
-- always has a unique instance, so this is not dangerous.
@[priority 100, nolint dangerous_instance] -- see Note [lower instance priority]
instance is_nonstrict_strict_order.to_is_irrefl {r : α → α → Prop} {s : α → α → Prop}
  [is_nonstrict_strict_order α r s] :
  is_irrefl α s :=
⟨λ a h, ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section subset
variables [has_subset α] {a b c : α}

lemma subset_of_eq_of_subset (hab : a = b) (hbc : b ⊆ c) : a ⊆ c := by rwa hab
lemma subset_of_subset_of_eq (hab : a ⊆ b) (hbc : b = c) : a ⊆ c := by rwa ←hbc
@[refl] lemma subset_refl [is_refl α (⊆)] (a : α) : a ⊆ a := refl _
lemma subset_rfl [is_refl α (⊆)] : a ⊆ a := refl _
lemma subset_of_eq [is_refl α (⊆)] : a = b → a ⊆ b := λ h, h ▸ subset_rfl
lemma superset_of_eq [is_refl α (⊆)] : a = b → b ⊆ a := λ h, h ▸ subset_rfl
lemma ne_of_not_subset [is_refl α (⊆)] : ¬ a ⊆ b → a ≠ b := mt subset_of_eq
lemma ne_of_not_superset [is_refl α (⊆)] : ¬ a ⊆ b → b ≠ a := mt superset_of_eq
@[trans] lemma subset_trans [is_trans α (⊆)] {a b c : α} : a ⊆ b → b ⊆ c → a ⊆ c := trans

lemma subset_antisymm [is_antisymm α (⊆)] (h : a ⊆ b) (h' : b ⊆ a) : a = b :=
antisymm h h'

lemma superset_antisymm [is_antisymm α (⊆)] (h : a ⊆ b) (h' : b ⊆ a) : b = a :=
antisymm' h h'

alias subset_of_eq_of_subset ← eq.trans_subset
alias subset_of_subset_of_eq ← has_subset.subset.trans_eq
alias subset_of_eq ← eq.subset' --TODO: Fix it and kill `eq.subset`
alias superset_of_eq ← eq.superset
alias subset_trans      ← has_subset.subset.trans
alias subset_antisymm   ← has_subset.subset.antisymm
alias superset_antisymm ← has_subset.subset.antisymm'

lemma subset_antisymm_iff [is_refl α (⊆)] [is_antisymm α (⊆)] : a = b ↔ a ⊆ b ∧ b ⊆ a :=
⟨λ h, ⟨h.subset', h.superset⟩, λ h, h.1.antisymm h.2⟩

lemma superset_antisymm_iff [is_refl α (⊆)] [is_antisymm α (⊆)] : a = b ↔ b ⊆ a ∧ a ⊆ b :=
⟨λ h, ⟨h.superset, h.subset'⟩, λ h, h.1.antisymm' h.2⟩

end subset

section ssubset
variables [has_ssubset α] {a b c : α}

lemma ssubset_of_eq_of_ssubset (hab : a = b) (hbc : b ⊂ c) : a ⊂ c := by rwa hab
lemma ssubset_of_ssubset_of_eq (hab : a ⊂ b) (hbc : b = c) : a ⊂ c := by rwa ←hbc
lemma ssubset_irrefl [is_irrefl α (⊂)] (a : α) : ¬ a ⊂ a := irrefl _
lemma ssubset_irrfl [is_irrefl α (⊂)] {a : α} : ¬ a ⊂ a := irrefl _
lemma ne_of_ssubset [is_irrefl α (⊂)] {a b : α} : a ⊂ b → a ≠ b := ne_of_irrefl
lemma ne_of_ssuperset [is_irrefl α (⊂)] {a b : α} : a ⊂ b → b ≠ a := ne_of_irrefl'
@[trans] lemma ssubset_trans [is_trans α (⊂)] {a b c : α} : a ⊂ b → b ⊂ c → a ⊂ c := trans
lemma ssubset_asymm [is_asymm α (⊂)] {a b : α} (h : a ⊂ b) : ¬ b ⊂ a := asymm h

alias ssubset_of_eq_of_ssubset ← eq.trans_ssubset
alias ssubset_of_ssubset_of_eq ← has_ssubset.ssubset.trans_eq
alias ssubset_irrfl   ← has_ssubset.ssubset.false
alias ne_of_ssubset   ← has_ssubset.ssubset.ne
alias ne_of_ssuperset ← has_ssubset.ssubset.ne'
alias ssubset_trans   ← has_ssubset.ssubset.trans
alias ssubset_asymm   ← has_ssubset.ssubset.asymm

end ssubset

section subset_ssubset
variables [has_subset α] [has_ssubset α] [is_nonstrict_strict_order α (⊆) (⊂)] {a b c : α}

lemma ssubset_iff_subset_not_subset : a ⊂ b ↔ a ⊆ b ∧ ¬ b ⊆ a := right_iff_left_not_left
lemma subset_of_ssubset (h : a ⊂ b) : a ⊆ b := (ssubset_iff_subset_not_subset.1 h).1
lemma not_subset_of_ssubset (h : a ⊂ b) : ¬ b ⊆ a := (ssubset_iff_subset_not_subset.1 h).2
lemma not_ssubset_of_subset (h : a ⊆ b) : ¬ b ⊂ a := λ h', not_subset_of_ssubset h' h

lemma ssubset_of_subset_not_subset (h₁ : a ⊆ b) (h₂ : ¬ b ⊆ a) : a ⊂ b :=
ssubset_iff_subset_not_subset.2 ⟨h₁, h₂⟩

alias subset_of_ssubset            ← has_ssubset.ssubset.subset
alias not_subset_of_ssubset        ← has_ssubset.ssubset.not_subset
alias not_ssubset_of_subset        ← has_subset.subset.not_ssubset
alias ssubset_of_subset_not_subset ← has_subset.subset.ssubset_of_not_subset

lemma ssubset_of_subset_of_ssubset [is_trans α (⊆)] (h₁ : a ⊆ b) (h₂ : b ⊂ c) : a ⊂ c :=
(h₁.trans h₂.subset).ssubset_of_not_subset $ λ h, h₂.not_subset $ h.trans h₁

lemma ssubset_of_ssubset_of_subset [is_trans α (⊆)] (h₁ : a ⊂ b) (h₂ : b ⊆ c) : a ⊂ c :=
(h₁.subset.trans h₂).ssubset_of_not_subset $ λ h, h₁.not_subset $ h₂.trans h

lemma ssubset_of_subset_of_ne [is_antisymm α (⊆)] (h₁ : a ⊆ b) (h₂ : a ≠ b) : a ⊂ b :=
h₁.ssubset_of_not_subset $ mt h₁.antisymm h₂

lemma ssubset_of_ne_of_subset [is_antisymm α (⊆)] (h₁ : a ≠ b) (h₂ : a ⊆ b) : a ⊂ b :=
ssubset_of_subset_of_ne h₂ h₁

lemma eq_or_ssubset_of_subset [is_antisymm α (⊆)] (h : a ⊆ b) : a = b ∨ a ⊂ b :=
(em (b ⊆ a)).imp h.antisymm h.ssubset_of_not_subset

lemma ssubset_or_eq_of_subset [is_antisymm α (⊆)] (h : a ⊆ b) : a ⊂ b ∨ a = b :=
(eq_or_ssubset_of_subset h).swap

alias ssubset_of_subset_of_ssubset ← has_subset.subset.trans_ssubset
alias ssubset_of_ssubset_of_subset ← has_ssubset.ssubset.trans_subset
alias ssubset_of_subset_of_ne      ← has_subset.subset.ssubset_of_ne
alias ssubset_of_ne_of_subset      ← ne.ssubset_of_subset
alias eq_or_ssubset_of_subset      ← has_subset.subset.eq_or_ssubset
alias ssubset_or_eq_of_subset      ← has_subset.subset.ssubset_or_eq

lemma ssubset_iff_subset_ne [is_antisymm α (⊆)] : a ⊂ b ↔ a ⊆ b ∧ a ≠ b :=
⟨λ h, ⟨h.subset, h.ne⟩, λ h, h.1.ssubset_of_ne h.2⟩

lemma subset_iff_ssubset_or_eq [is_refl α (⊆)] [is_antisymm α (⊆)] : a ⊆ b ↔ a ⊂ b ∨ a = b :=
⟨λ h, h.ssubset_or_eq, λ h, h.elim subset_of_ssubset subset_of_eq⟩

end subset_ssubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/

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
instance [preorder α] : is_nonstrict_strict_order α (≤) (<) := ⟨@lt_iff_le_not_le _ _⟩
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
instance [linear_order α] : is_strict_total_order α (<) := {}
instance [linear_order α] : is_order_connected α (<) := by apply_instance
instance [linear_order α] : is_incomp_trans α (<) := by apply_instance
instance [linear_order α] : is_strict_weak_order α (<) := by apply_instance

lemma transitive_le [preorder α] : transitive (@has_le.le α _) := transitive_of_trans _
lemma transitive_lt [preorder α] : transitive (@has_lt.lt α _) := transitive_of_trans _
lemma transitive_ge [preorder α] : transitive (@ge α _) := transitive_of_trans _
lemma transitive_gt [preorder α] : transitive (@gt α _) := transitive_of_trans _

instance order_dual.is_total_le [has_le α] [is_total α (≤)] : is_total αᵒᵈ (≤) :=
@is_total.swap α _ _

instance : well_founded_lt ℕ := ⟨nat.lt_wf⟩
instance nat.lt.is_well_order : is_well_order ℕ (<) := { }

instance [linear_order α] [h : is_well_order α (<)] : is_well_order αᵒᵈ (>) := h
instance [linear_order α] [h : is_well_order α (>)] : is_well_order αᵒᵈ (<) := h
