/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import logic.function.basic
import tactic.basic

/-!
# Disjoint union of types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves basic results about the sum type `α ⊕ β`.

`α ⊕ β` is the type made of a copy of `α` and a copy of `β`. It is also called *disjoint union*.

## Main declarations

* `sum.get_left`: Retrieves the left content of `x : α ⊕ β` or returns `none` if it's coming from
  the right.
* `sum.get_right`: Retrieves the right content of `x : α ⊕ β` or returns `none` if it's coming from
  the left.
* `sum.is_left`: Returns whether `x : α ⊕ β` comes from the left component or not.
* `sum.is_right`: Returns whether `x : α ⊕ β` comes from the right component or not.
* `sum.map`: Maps `α ⊕ β` to `γ ⊕ δ` component-wise.
* `sum.elim`: Nondependent eliminator/induction principle for `α ⊕ β`.
* `sum.swap`: Maps `α ⊕ β` to `β ⊕ α` by swapping components.
* `sum.lex`: Lexicographic order on `α ⊕ β` induced by a relation on `α` and a relation on `β`.

## Notes

The definition of `sum` takes values in `Type*`. This effectively forbids `Prop`- valued sum types.
To this effect, we have `psum`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence. The `Prop` version is `or`.
-/

universes u v w x
variables {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

namespace sum

attribute [derive decidable_eq] sum

@[simp] lemma «forall» {p : α ⊕ β → Prop} : (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ ∀ b, p (inr b) :=
⟨λ h, ⟨λ a, h _, λ b, h _⟩, λ ⟨h₁, h₂⟩, sum.rec h₁ h₂⟩

@[simp] lemma «exists» {p : α ⊕ β → Prop} : (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
⟨λ h, match h with
| ⟨inl a, h⟩ := or.inl ⟨a, h⟩
| ⟨inr b, h⟩ := or.inr ⟨b, h⟩
end, λ h, match h with
| or.inl ⟨a, h⟩ := ⟨inl a, h⟩
| or.inr ⟨b, h⟩ := ⟨inr b, h⟩
end⟩

lemma inl_injective : function.injective (inl : α → α ⊕ β) := λ x y, inl.inj
lemma inr_injective : function.injective (inr : β → α ⊕ β) := λ x y, inr.inj

section get

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
@[simp] def get_left : α ⊕ β → option α
| (inl a) := some a
| (inr _) := none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
@[simp] def get_right : α ⊕ β → option β
| (inr b) := some b
| (inl _) := none

/-- Check if a sum is `inl`. -/
@[simp] def is_left : α ⊕ β → bool
| (inl _) := tt
| (inr _) := ff

/-- Check if a sum is `inr`. -/
@[simp] def is_right : α ⊕ β → bool
| (inl _) := ff
| (inr _) := tt

variables {x y : α ⊕ β}

@[simp] lemma get_left_eq_none_iff : x.get_left = none ↔ x.is_right :=
by cases x; simp only [get_left, is_right, coe_sort_tt, coe_sort_ff, eq_self_iff_true]

@[simp] lemma get_right_eq_none_iff : x.get_right = none ↔ x.is_left :=
by cases x; simp only [get_right, is_left, coe_sort_tt, coe_sort_ff, eq_self_iff_true]

@[simp] lemma get_left_eq_some_iff {a} : x.get_left = some a ↔ x = inl a :=
by cases x; simp only [get_left]

@[simp] lemma get_right_eq_some_iff {b} : x.get_right = some b ↔ x = inr b :=
by cases x; simp only [get_right]

@[simp] lemma bnot_is_left (x : α ⊕ β) : bnot x.is_left = x.is_right := by cases x; refl
@[simp] lemma is_left_eq_ff : x.is_left = ff ↔ x.is_right := by cases x; simp
lemma not_is_left : ¬x.is_left ↔ x.is_right := by simp
@[simp] lemma bnot_is_right (x : α ⊕ β) : bnot x.is_right = x.is_left := by cases x; refl
@[simp] lemma is_right_eq_ff : x.is_right = ff ↔ x.is_left := by cases x; simp
lemma not_is_right : ¬x.is_right ↔ x.is_left := by simp

lemma is_left_iff : x.is_left ↔ ∃ y, x = sum.inl y := by cases x; simp
lemma is_right_iff : x.is_right ↔ ∃ y, x = sum.inr y := by cases x; simp

end get

theorem inl.inj_iff {a b} : (inl a : α ⊕ β) = inl b ↔ a = b :=
⟨inl.inj, congr_arg _⟩

theorem inr.inj_iff {a b} : (inr a : α ⊕ β) = inr b ↔ a = b :=
⟨inr.inj, congr_arg _⟩

theorem inl_ne_inr {a : α} {b : β} : inl a ≠ inr b.

theorem inr_ne_inl {a : α} {b : β} : inr b ≠ inl a.

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ : Sort*} (f : α → γ) (g : β → γ) : α ⊕ β → γ := λ x, sum.rec_on x f g

@[simp] lemma elim_inl {α β γ : Sort*} (f : α → γ) (g : β → γ) (x : α) :
  sum.elim f g (inl x) = f x := rfl

@[simp] lemma elim_inr {α β γ : Sort*} (f : α → γ) (g : β → γ) (x : β) :
  sum.elim f g (inr x) = g x := rfl

@[simp] lemma elim_comp_inl {α β γ : Sort*} (f : α → γ) (g : β → γ) :
  sum.elim f g ∘ inl = f := rfl

@[simp] lemma elim_comp_inr {α β γ : Sort*} (f : α → γ) (g : β → γ) :
  sum.elim f g ∘ inr = g := rfl

@[simp] lemma elim_inl_inr {α β : Sort*} :
  @sum.elim α β _ inl inr = id :=
funext $ λ x, sum.cases_on x (λ _, rfl) (λ _, rfl)

lemma comp_elim {α β γ δ : Sort*} (f : γ → δ) (g : α → γ) (h : β → γ):
  f ∘ sum.elim g h = sum.elim (f ∘ g) (f ∘ h) :=
funext $ λ x, sum.cases_on x (λ _, rfl) (λ _, rfl)

@[simp] lemma elim_comp_inl_inr {α β γ : Sort*} (f : α ⊕ β → γ) :
  sum.elim (f ∘ inl) (f ∘ inr) = f :=
funext $ λ x, sum.cases_on x (λ _, rfl) (λ _, rfl)

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β') : α ⊕ β → α' ⊕ β' :=
sum.elim (inl ∘ f) (inr ∘ g)

@[simp] lemma map_inl (f : α → α') (g : β → β') (x : α) : (inl x).map f g = inl (f x) := rfl
@[simp] lemma map_inr (f : α → α') (g : β → β') (x : β) : (inr x).map f g = inr (g x) := rfl

@[simp] lemma map_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
  ∀ x : α ⊕ β, (x.map f g).map f' g' = x.map (f' ∘ f) (g' ∘ g)
| (inl a) := rfl
| (inr b) := rfl

@[simp] lemma map_comp_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
  (sum.map f' g') ∘ (sum.map f g) = sum.map (f' ∘ f) (g' ∘ g) :=
funext $ map_map f' g' f g

@[simp] lemma map_id_id (α β) : sum.map (@id α) (@id β) = id :=
funext $ λ x, sum.rec_on x (λ _, rfl) (λ _, rfl)

lemma elim_map {α β γ δ ε : Sort*} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} {x} :
  sum.elim f₂ g₂ (sum.map f₁ g₁ x) = sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) x :=
by cases x; refl

lemma elim_comp_map {α β γ δ ε : Sort*} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} :
  sum.elim f₂ g₂ ∘ sum.map f₁ g₁ = sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) :=
funext $ λ _, elim_map

@[simp] lemma is_left_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
  is_left (x.map f g) = is_left x :=
by cases x; refl

@[simp] lemma is_right_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
  is_right (x.map f g) = is_right x :=
by cases x; refl

@[simp] lemma get_left_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
  (x.map f g).get_left = x.get_left.map f :=
by cases x; refl

@[simp] lemma get_right_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
  (x.map f g).get_right = x.get_right.map g :=
by cases x; refl

open function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp] lemma update_elim_inl [decidable_eq α] [decidable_eq (α ⊕ β)] {f : α → γ} {g : β → γ}
  {i : α} {x : γ} :
  update (sum.elim f g) (inl i) x = sum.elim (update f i x) g :=
update_eq_iff.2 ⟨by simp, by simp { contextual := tt }⟩

@[simp] lemma update_elim_inr [decidable_eq β] [decidable_eq (α ⊕ β)] {f : α → γ} {g : β → γ}
  {i : β} {x : γ} :
  update (sum.elim f g) (inr i) x = sum.elim f (update g i x) :=
update_eq_iff.2 ⟨by simp, by simp { contextual := tt }⟩

@[simp] lemma update_inl_comp_inl [decidable_eq α] [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : α}
  {x : γ} :
  update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
update_comp_eq_of_injective _ inl_injective _ _

@[simp] lemma update_inl_apply_inl [decidable_eq α] [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ}
  {i j : α} {x : γ} :
  update f (inl i) x (inl j) = update (f ∘ inl) i x j :=
by rw ← update_inl_comp_inl

@[simp] lemma update_inl_comp_inr [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {x : γ} :
  update f (inl i) x ∘ inr = f ∘ inr :=
update_comp_eq_of_forall_ne _ _ $ λ _, inr_ne_inl

@[simp] lemma update_inl_apply_inr [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
  update f (inl i) x (inr j) = f (inr j) :=
function.update_noteq inr_ne_inl _ _

@[simp] lemma update_inr_comp_inl [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {x : γ} :
  update f (inr i) x ∘ inl = f ∘ inl :=
update_comp_eq_of_forall_ne _ _ $ λ _, inl_ne_inr

@[simp] lemma update_inr_apply_inl [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
  update f (inr j) x (inl i) = f (inl i) :=
function.update_noteq inl_ne_inr _ _

@[simp] lemma update_inr_comp_inr [decidable_eq β] [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ} {i : β}
  {x : γ} :
  update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
update_comp_eq_of_injective _ inr_injective _ _

@[simp] lemma update_inr_apply_inr [decidable_eq β] [decidable_eq (α ⊕ β)] {f : α ⊕ β → γ}
  {i j : β} {x : γ} :
  update f (inr i) x (inr j) = update (f ∘ inr) i x j :=
by rw ← update_inr_comp_inr

/-- Swap the factors of a sum type -/
def swap : α ⊕ β → β ⊕ α := sum.elim inr inl

@[simp] lemma swap_inl (x : α) : swap (inl x : α ⊕ β) = inr x := rfl
@[simp] lemma swap_inr (x : β) : swap (inr x : α ⊕ β) = inl x := rfl
@[simp] lemma swap_swap (x : α ⊕ β) : swap (swap x) = x := by cases x; refl
@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α ⊕ β) := funext $ swap_swap
@[simp] lemma swap_left_inverse : function.left_inverse (@swap α β) swap := swap_swap
@[simp] lemma swap_right_inverse : function.right_inverse (@swap α β) swap := swap_swap
@[simp] lemma is_left_swap (x : α ⊕ β) : x.swap.is_left = x.is_right := by cases x; refl
@[simp] lemma is_right_swap (x : α ⊕ β) : x.swap.is_right = x.is_left := by cases x; refl
@[simp] lemma get_left_swap (x : α ⊕ β) : x.swap.get_left = x.get_right := by cases x; refl
@[simp] lemma get_right_swap (x : α ⊕ β) : x.swap.get_right = x.get_left := by cases x; refl

section lift_rel

/-- Lifts pointwise two relations between `α` and `γ` and between `β` and `δ` to a relation between
`α ⊕ β` and `γ ⊕ δ`. -/
inductive lift_rel (r : α → γ → Prop) (s : β → δ → Prop) : α ⊕ β → γ ⊕ δ → Prop
| inl {a c} : r a c → lift_rel (inl a) (inl c)
| inr {b d} : s b d → lift_rel (inr b) (inr d)

attribute [protected] lift_rel.inl lift_rel.inr

variables {r r₁ r₂ : α → γ → Prop} {s s₁ s₂ : β → δ → Prop} {a : α} {b : β} {c : γ} {d : δ}
  {x : α ⊕ β} {y : γ ⊕ δ}

@[simp] lemma lift_rel_inl_inl : lift_rel r s (inl a) (inl c) ↔ r a c :=
⟨λ h, by { cases h, assumption }, lift_rel.inl⟩

@[simp] lemma not_lift_rel_inl_inr : ¬ lift_rel r s (inl a) (inr d) .
@[simp] lemma not_lift_rel_inr_inl : ¬ lift_rel r s (inr b) (inl c) .

@[simp] lemma lift_rel_inr_inr : lift_rel r s (inr b) (inr d) ↔ s b d :=
⟨λ h, by { cases h, assumption }, lift_rel.inr⟩

instance [Π a c, decidable (r a c)] [Π b d, decidable (s b d)] :
  Π (ab : α ⊕ β) (cd : γ ⊕ δ), decidable (lift_rel r s ab cd)
| (inl a) (inl c) := decidable_of_iff' _ lift_rel_inl_inl
| (inl a) (inr d) := decidable.is_false not_lift_rel_inl_inr
| (inr b) (inl c) := decidable.is_false not_lift_rel_inr_inl
| (inr b) (inr d) := decidable_of_iff' _ lift_rel_inr_inr

lemma lift_rel.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b)
  (h : lift_rel r₁ s₁ x y) :
  lift_rel r₂ s₂ x y :=
by { cases h, exacts [lift_rel.inl (hr _ _ ‹_›), lift_rel.inr (hs _ _ ‹_›)] }

lemma lift_rel.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : lift_rel r₁ s x y) :
  lift_rel r₂ s x y :=
h.mono hr $ λ _ _, id

lemma lift_rel.mono_right (hs : ∀ a b, s₁ a b → s₂ a b)  (h : lift_rel r s₁ x y) :
  lift_rel r s₂ x y :=
h.mono (λ _ _, id) hs

protected lemma lift_rel.swap (h : lift_rel r s x y) : lift_rel s r x.swap y.swap :=
by { cases h, exacts [lift_rel.inr ‹_›, lift_rel.inl ‹_›] }

@[simp] lemma lift_rel_swap_iff : lift_rel s r x.swap y.swap ↔ lift_rel r s x y :=
⟨λ h, by { rw [←swap_swap x, ←swap_swap y], exact h.swap }, lift_rel.swap⟩

end lift_rel

section lex

/-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`, otherwise use the
respective order on `α` or `β`. -/
inductive lex (r : α → α → Prop) (s : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
| inl {a₁ a₂} (h : r a₁ a₂) : lex (inl a₁) (inl a₂)
| inr {b₁ b₂} (h : s b₁ b₂) : lex (inr b₁) (inr b₂)
| sep (a b) : lex (inl a) (inr b)

attribute [protected] sum.lex.inl sum.lex.inr
attribute [simp] lex.sep

variables {r r₁ r₂ : α → α → Prop} {s s₁ s₂ : β → β → Prop} {a a₁ a₂ : α} {b b₁ b₂ : β}
  {x y : α ⊕ β}

@[simp] lemma lex_inl_inl : lex r s (inl a₁) (inl a₂) ↔ r a₁ a₂ :=
⟨λ h, by { cases h, assumption }, lex.inl⟩

@[simp] lemma lex_inr_inr : lex r s (inr b₁) (inr b₂) ↔ s b₁ b₂ :=
⟨λ h, by { cases h, assumption }, lex.inr⟩

@[simp] lemma lex_inr_inl : ¬ lex r s (inr b) (inl a) .

instance [decidable_rel r] [decidable_rel s] : decidable_rel (lex r s)
| (inl a) (inl c) := decidable_of_iff' _ lex_inl_inl
| (inl a) (inr d) := decidable.is_true (lex.sep _ _)
| (inr b) (inl c) := decidable.is_false lex_inr_inl
| (inr b) (inr d) := decidable_of_iff' _ lex_inr_inr

protected lemma lift_rel.lex {a b : α ⊕ β} (h : lift_rel r s a b) : lex r s a b :=
by { cases h, exacts [lex.inl ‹_›, lex.inr ‹_›] }

lemma lift_rel_subrelation_lex : subrelation (lift_rel r s) (lex r s) := λ a b, lift_rel.lex

lemma lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : lex r₁ s₁ x y) :
  lex r₂ s₂ x y :=
by { cases h, exacts [lex.inl (hr _ _ ‹_›), lex.inr (hs _ _ ‹_›), lex.sep _ _] }

lemma lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : lex r₁ s x y) : lex r₂ s x y :=
h.mono hr $ λ _ _, id

lemma lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : lex r s₁ x y) : lex r s₂ x y :=
h.mono (λ _ _, id) hs

lemma lex_acc_inl {a} (aca : acc r a) : acc (lex r s) (inl a) :=
begin
  induction aca with a H IH,
  constructor, intros y h,
  cases h with a' _ h',
  exact IH _ h'
end

lemma lex_acc_inr (aca : ∀ a, acc (lex r s) (inl a)) {b} (acb : acc s b) : acc (lex r s) (inr b) :=
begin
  induction acb with b H IH,
  constructor, intros y h,
  cases h with _ _ _ b' _ h' a,
  { exact IH _ h' },
  { exact aca _ }
end

lemma lex_wf (ha : well_founded r) (hb : well_founded s) : well_founded (lex r s) :=
have aca : ∀ a, acc (lex r s) (inl a), from λ a, lex_acc_inl (ha.apply a),
⟨λ x, sum.rec_on x aca (λ b, lex_acc_inr aca (hb.apply b))⟩

end lex
end sum

open sum

namespace function

lemma injective.sum_elim {f : α → γ} {g : β → γ}
  (hf : injective f) (hg : injective g) (hfg : ∀ a b, f a ≠ g b) :
  injective (sum.elim f g)
| (inl x) (inl y) h := congr_arg inl $ hf h
| (inl x) (inr y) h := (hfg x y h).elim
| (inr x) (inl y) h := (hfg y x h.symm).elim
| (inr x) (inr y) h := congr_arg inr $ hg h

lemma injective.sum_map {f : α → β} {g : α' → β'} (hf : injective f) (hg : injective g) :
  injective (sum.map f g)
| (inl x) (inl y) h := congr_arg inl $ hf $ inl.inj h
| (inr x) (inr y) h := congr_arg inr $ hg $ inr.inj h

lemma surjective.sum_map {f : α → β} {g : α' → β'} (hf : surjective f) (hg : surjective g) :
  surjective (sum.map f g)
| (inl y) := let ⟨x, hx⟩ := hf y in ⟨inl x, congr_arg inl hx⟩
| (inr y) := let ⟨x, hx⟩ := hg y in ⟨inr x, congr_arg inr hx⟩

lemma bijective.sum_map {f : α → β} {g : α' → β'} (hf : bijective f) (hg : bijective g) :
  bijective (sum.map f g) :=
⟨hf.injective.sum_map hg.injective, hf.surjective.sum_map hg.surjective⟩

end function

namespace sum
open function

@[simp] lemma map_injective {f : α → γ} {g : β → δ} :
  injective (sum.map f g) ↔ injective f ∧ injective g :=
⟨λ h, ⟨λ a₁ a₂ ha, inl_injective $ @h (inl a₁) (inl a₂) (congr_arg inl ha : _),
      λ b₁ b₂ hb, inr_injective $ @h (inr b₁) (inr b₂) (congr_arg inr hb : _)⟩,
  λ h, h.1.sum_map h.2⟩

@[simp] lemma map_surjective {f : α → γ} {g : β → δ} :
  surjective (sum.map f g) ↔ surjective f ∧ surjective g :=
⟨λ h, ⟨λ c, begin
  obtain ⟨a | b, h⟩ := h (inl c),
  { exact ⟨a, inl_injective h⟩ },
  { cases h },
end, λ d, begin
  obtain ⟨a | b, h⟩ := h (inr d),
  { cases h },
  { exact ⟨b, inr_injective h⟩ },
end⟩, λ h, h.1.sum_map h.2⟩

@[simp] lemma map_bijective {f : α → γ} {g : β → δ} :
  bijective (sum.map f g) ↔ bijective f ∧ bijective g :=
(map_injective.and map_surjective).trans $ and_and_and_comm _ _ _ _

lemma elim_const_const (c : γ) :
  sum.elim (const _ c : α → γ) (const _ c : β → γ) = const _ c :=
by { ext x, cases x; refl }

@[simp]
lemma elim_lam_const_lam_const (c : γ) :
  sum.elim (λ (_ : α), c) (λ (_ : β), c) = λ _, c :=
sum.elim_const_const c

lemma elim_update_left [decidable_eq α] [decidable_eq β]
    (f : α → γ) (g : β → γ) (i : α) (c : γ) :
  sum.elim (function.update f i c) g = function.update (sum.elim f g) (inl i) c :=
begin
  ext x, cases x,
  { by_cases h : x = i,
    { subst h, simp },
    { simp [h] } },
  { simp }
end

lemma elim_update_right [decidable_eq α] [decidable_eq β]
    (f : α → γ) (g : β → γ) (i : β) (c : γ) :
  sum.elim f (function.update g i c) = function.update (sum.elim f g) (inr i) c :=
begin
  ext x, cases x,
  { simp },
  { by_cases h : x = i,
    { subst h, simp },
    { simp [h] } }
end

end sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace sum3

/-- The map from the first summand into a ternary sum. -/
@[pattern, simp, reducible] def in₀ (a) : α ⊕ β ⊕ γ := inl a
/-- The map from the second summand into a ternary sum. -/
@[pattern, simp, reducible] def in₁ (b) : α ⊕ β ⊕ γ := inr $ inl b
/-- The map from the third summand into a ternary sum. -/
@[pattern, simp, reducible] def in₂ (c) : α ⊕ β ⊕ γ := inr $ inr c

end sum3
