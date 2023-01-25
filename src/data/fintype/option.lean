/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import data.finset.option

/-!
# fintype instances for option

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open function
open_locale nat

universes u v

variables {α β γ : Type*}


open finset function

instance {α : Type*} [fintype α] : fintype (option α) :=
⟨univ.insert_none, λ a, by simp⟩

lemma univ_option (α : Type*) [fintype α] : (univ : finset (option α)) = insert_none univ := rfl

@[simp] theorem fintype.card_option {α : Type*} [fintype α] :
  fintype.card (option α) = fintype.card α + 1 :=
(finset.card_cons _).trans $ congr_arg2 _ (card_map _) rfl

/-- If `option α` is a `fintype` then so is `α` -/
def fintype_of_option {α : Type*} [fintype (option α)] : fintype α :=
⟨finset.erase_none (fintype.elems (option α)), λ x, mem_erase_none.mpr (fintype.complete (some x))⟩

/-- A type is a `fintype` if its successor (using `option`) is a `fintype`. -/
def fintype_of_option_equiv [fintype α] (f : α ≃ option β) : fintype β :=
by { haveI := fintype.of_equiv _ f, exact fintype_of_option }

namespace fintype

/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def trunc_rec_empty_option {P : Type u → Sort v}
  (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_empty : P pempty)
  (h_option : ∀ {α} [fintype α] [decidable_eq α], P α → P (option α))
  (α : Type u) [fintype α] [decidable_eq α] : trunc (P α) :=
begin
  suffices : ∀ n : ℕ, trunc (P (ulift $ fin n)),
  { apply trunc.bind (this (fintype.card α)),
    intro h,
    apply trunc.map _ (fintype.trunc_equiv_fin α),
    intro e,
    exact of_equiv (equiv.ulift.trans e.symm) h },
  intro n,
  induction n with n ih,
  { have : card pempty = card (ulift (fin 0)),
    { simp only [card_fin, card_pempty, card_ulift] },
    apply trunc.bind (trunc_equiv_of_card_eq this),
    intro e,
    apply trunc.mk,
    refine of_equiv e h_empty, },
  { have : card (option (ulift (fin n))) = card (ulift (fin n.succ)),
    { simp only [card_fin, card_option, card_ulift] },
    apply trunc.bind (trunc_equiv_of_card_eq this),
    intro e,
    apply trunc.map _ ih,
    intro ih,
    refine of_equiv e (h_option ih), },
end

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_eliminator]
lemma induction_empty_option {P : Π (α : Type u) [fintype α], Prop}
  (of_equiv : ∀ α β [fintype β] (e : α ≃ β), @P α (@fintype.of_equiv α β ‹_› e.symm) → @P β ‹_›)
  (h_empty : P pempty)
  (h_option : ∀ α [fintype α], by exactI P α → P (option α))
  (α : Type u) [fintype α] : P α :=
begin
  obtain ⟨p⟩ := @trunc_rec_empty_option (λ α, ∀ h, @P α h)
    (λ α β e hα hβ, @of_equiv α β hβ e (hα _)) (λ _i, by convert h_empty)
    _ α _ (classical.dec_eq α),
  { exact p _ },
  { rintro α hα - Pα hα', resetI, convert h_option α (Pα _) }
end

end fintype

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
lemma finite.induction_empty_option {P : Type u → Prop}
  (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_empty : P pempty)
  (h_option : ∀ {α} [fintype α], P α → P (option α))
  (α : Type u) [finite α] : P α :=
begin
  casesI nonempty_fintype α,
  refine fintype.induction_empty_option _ _ _ α,
  exacts [λ α β _, of_equiv, h_empty, @h_option]
end
