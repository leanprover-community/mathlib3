/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import logic.function.basic
import tactic.protected

/-!
# Disjoint union of types

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

end get

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β')  : α ⊕ β → α' ⊕ β'
| (inl x) := inl (f x)
| (inr x) := inr (g x)

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
@[simp] def swap : α ⊕ β → β ⊕ α
| (inl a) := inr a
| (inr b) := inl b

@[simp] lemma swap_swap (x : α ⊕ β) : swap (swap x) = x := by cases x; refl
@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α ⊕ β) := funext $ swap_swap
@[simp] lemma swap_left_inverse : function.left_inverse (@swap α β) swap := swap_swap
@[simp] lemma swap_right_inverse : function.right_inverse (@swap α β) swap := swap_swap

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

lemma lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : lex r₁ s₁ x y) :
  lex r₂ s₂ x y :=
by { cases h, exacts [lex.inl (hr _ _ ‹_›), lex.inr (hs _ _ ‹_›), lex.sep _ _] }

lemma lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : lex r₁ s x y) : lex r₂ s x y :=
h.mono hr $ λ _ _, id

lemma lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b)  (h : lex r s₁ x y) : lex r s₂ x y :=
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

namespace function

open sum

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

end function
