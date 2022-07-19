/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import logic.basic

/-!
# Indexed equality

This file provides `indeq` with notation `a =ᵢ b`, which provide a different notion of heterogeneous
equality to `heq` (`a == b`).

In particular, `indeq` is for when `a : A i` and `b : A j`, where `A : ι → Sort u` is an indexed
family of types. Instead of `type_eq_of_heq` which states `A i = A j` for `a == b`, this provides
`indeq.index_eq` which states `i = j` for `a =ᵢ b`.

Note that in the degenerate case when `A = id`, this is equivalent to `heq`.
-/

universes ui ui' u u'

section

variables {ι : Sort ui} {ι' : Sort ui'} {A : ι → Sort u} {A' : ι' → Sort u'}

/-- Indexed equality; `(ai : A i) =ᵢ (aj : A j)` if `i = j` -/
inductive indeq {i : ι} (ai : A i) : Π {j} (aj : A j), Prop
| refl [] : indeq ai

infix ` =ᵢ `:50 := indeq

attribute [refl] indeq.refl

variables {i j k : ι} {a a' : A i} {b : A j} {c : A k}
@[symm] lemma indeq.symm (h : a =ᵢ b) : b =ᵢ a :=
indeq.rec_on h (indeq.refl a)

@[trans] lemma indeq.trans (h₁ : a =ᵢ b) (h₂ : b =ᵢ c) : a =ᵢ c :=
indeq.rec_on h₂ h₁

protected lemma eq.indeq (h : a = a') : a =ᵢ a' :=
eq.subst h (indeq.refl a)

lemma indeq.index_eq (h : a =ᵢ b) : i = j :=
indeq.rec_on h (eq.refl _)

protected lemma indeq.heq (h : a =ᵢ b) : a == b :=
indeq.rec_on h (heq.refl _)

lemma indeq_of_eq_of_heq (hij : i = j) (hab : a == b) : a =ᵢ b :=
by { cases hij, cases hab, refl }

lemma indeq_iff : a =ᵢ b ↔ i = j ∧ a == b :=
⟨λ h, ⟨h.index_eq, h.heq⟩, and.rec $ indeq_of_eq_of_heq⟩

lemma indeq_id_iff_heq {α β} {a : α} {b : β} : @indeq (Sort u) id _ a _ b ↔ a == b :=
by split; { intro h, cases h, refl }

/-- In the degenerate case when `A = id`, then `indeq` is just `heq` -/
@[simp] lemma indeq_id_eq_heq : @indeq (Sort u) id = @heq :=
funext $ λ α, funext $ λ a, funext $ λ β, funext $ λ b, propext indeq_id_iff_heq

lemma indeq_congr_arg {I : Π i, A i → ι'} (f : Π i (a : A i), A' (I i a)) (h : a =ᵢ b) :
  f _ a =ᵢ f _ b :=
indeq.rec_on h (indeq.refl _)

lemma sigma_mk_eq_iff_indeq {ι : Type*} {A : ι → Type u} {i j} {a : A i} {b : A j} :
  sigma.mk _ a = sigma.mk _ b ↔ a =ᵢ b :=
(iff_of_eq (sigma.mk.inj_eq _ _ _ _)).trans indeq_iff.symm

end
