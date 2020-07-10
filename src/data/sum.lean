/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import tactic.lint

/-!
# More theorems about the sum type
-/

universes u v w x
variables {α : Type u} {α' : Type w} {β : Type v} {β' : Type x}
open sum

attribute [derive decidable_eq] sum

@[simp] theorem sum.forall {p : α ⊕ β → Prop} : (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ (∀ b, p (inr b)) :=
⟨λ h, ⟨λ a, h _, λ b, h _⟩, λ ⟨h₁, h₂⟩, sum.rec h₁ h₂⟩

@[simp] theorem sum.exists {p : α ⊕ β → Prop} : (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
⟨λ h, match h with
| ⟨inl a, h⟩ := or.inl ⟨a, h⟩
| ⟨inr b, h⟩ := or.inr ⟨b, h⟩
end, λ h, match h with
| or.inl ⟨a, h⟩ := ⟨inl a, h⟩
| or.inr ⟨b, h⟩ := ⟨inr b, h⟩
end⟩

namespace sum

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β')  : α ⊕ β → α' ⊕ β'
| (sum.inl x) := sum.inl (f x)
| (sum.inr x) := sum.inr (g x)

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

lemma elim_injective {α β γ : Sort*} {f : α → γ} {g : β → γ}
  (hf : function.injective f) (hg : function.injective g)
 (hfg : ∀ a b, f a ≠ g b) : function.injective (sum.elim f g) :=
λ x y, sum.rec_on x
  (sum.rec_on y (λ x y hxy, by rw hf hxy) (λ x y hxy, false.elim $ hfg _ _ hxy))
  (sum.rec_on y (λ x y hxy, false.elim $ hfg x y hxy.symm) (λ x y hxy, by rw hg hxy))

section
  variables (ra : α → α → Prop) (rb : β → β → Prop)

  /-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`,
    otherwise use the respective order on `α` or `β`. -/
  inductive lex : α ⊕ β → α ⊕ β → Prop
  | inl {a₁ a₂} (h : ra a₁ a₂) : lex (inl a₁) (inl a₂)
  | inr {b₁ b₂} (h : rb b₁ b₂) : lex (inr b₁) (inr b₂)
  | sep (a b) : lex (inl a) (inr b)

  variables {ra rb}

  @[simp] theorem lex_inl_inl {a₁ a₂} : lex ra rb (inl a₁) (inl a₂) ↔ ra a₁ a₂ :=
  ⟨λ h, by cases h; assumption, lex.inl⟩

  @[simp] theorem lex_inr_inr {b₁ b₂} : lex ra rb (inr b₁) (inr b₂) ↔ rb b₁ b₂ :=
  ⟨λ h, by cases h; assumption, lex.inr⟩

  @[simp] theorem lex_inr_inl {b a} : ¬ lex ra rb (inr b) (inl a) :=
  λ h, by cases h

  attribute [simp] lex.sep

  theorem lex_acc_inl {a} (aca : acc ra a) : acc (lex ra rb) (inl a) :=
  begin
    induction aca with a H IH,
    constructor, intros y h,
    cases h with a' _ h',
    exact IH _ h'
  end

  theorem lex_acc_inr (aca : ∀ a, acc (lex ra rb) (inl a)) {b} (acb : acc rb b) : acc (lex ra rb) (inr b) :=
  begin
    induction acb with b H IH,
    constructor, intros y h,
    cases h with _ _ _ b' _ h' a,
    { exact IH _ h' },
    { exact aca _ }
  end

  theorem lex_wf (ha : well_founded ra) (hb : well_founded rb) : well_founded (lex ra rb) :=
  have aca : ∀ a, acc (lex ra rb) (inl a), from λ a, lex_acc_inl (ha.apply a),
  ⟨λ x, sum.rec_on x aca (λ b, lex_acc_inr aca (hb.apply b))⟩

end

/-- Swap the factors of a sum type -/
@[simp] def swap : α ⊕ β → β ⊕ α
| (inl a) := inr a
| (inr b) := inl b

@[simp] lemma swap_swap (x : α ⊕ β) : swap (swap x) = x :=
by cases x; refl

@[simp] lemma swap_swap_eq : swap ∘ swap = @id (α ⊕ β) :=
funext $ swap_swap

@[simp] lemma swap_left_inverse : function.left_inverse (@swap α β) swap :=
swap_swap

@[simp] lemma swap_right_inverse : function.right_inverse (@swap α β) swap :=
swap_swap

end sum

namespace function

open sum

lemma injective.sum_map {f : α → β} {g : α' → β'} (hf : injective f) (hg : injective g) :
  injective (sum.map f g)
| (inl x) (inl y) h := congr_arg inl $ hf $ inl.inj h
| (inr x) (inr y) h := congr_arg inr $ hg $ inr.inj h

lemma surjective.sum_map {f : α → β} {g : α' → β'} (hf : surjective f) (hg : surjective g) :
  surjective (sum.map f g)
| (inl y) := let ⟨x, hx⟩ := hf y in ⟨inl x, congr_arg inl hx⟩
| (inr y) := let ⟨x, hx⟩ := hg y in ⟨inr x, congr_arg inr hx⟩

end function
