/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import data.set.countable
import model_theory.basic
import category_theory.concrete_category.bundled

/-!
# Types and Classes of First-Order Structures
This file defines types of bundled first-order structures and describes classes of first-order
structures.

## Main Definitions
* The type of bundled `L`-structures is `category_theory.bundled L.Structure`, and each element has
a canonical `L.Structure` instance.
* `first_order.language.equiv_setoid` is an equivalence relation on bundled `L.Structure`s
designating structures as equivalent when they are isomorphic.
* `first_order.language.is_equiv_invariant` denotes that a class of `L.Structure`s is
isomorphism-invariant.
* `first_order.language.is_equiv_invariant.to_set_quotient` describes an isomorphism-invariant class
of `L.Structure`s as a set of isomorphism classes.

-/

universes u v w

open_locale first_order
open set category_theory

variables (L : first_order.language.{u v})

@[protected] instance category_theory.bundled.Structure (M : bundled L.Structure) :
  L.Structure M :=
M.str

namespace first_order
namespace language
open Structure

/-! ### Isomorphism-Invariant Classes and Essential Countability -/

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

variables {L} (K : Π (M : Type w) [L.Structure M], Prop)

/-- A class `K` is isomorphism-invariant when structure isomorphic to a structure in `K` is also in
  `K`. -/
def is_equiv_invariant : Prop :=
∀ (M N : Type w) [strM : L.Structure M] [strN : L.Structure N],
  nonempty (@equiv L M N strM strN) → (@K M strM = @K N strN)

variables {K}

/-- An isomorphism-invariant class can also be thought of as a set of isomorphism classes. -/
def is_equiv_invariant.to_set_quotient (h : is_equiv_invariant K) :
  set (quotient L.equiv_setoid) :=
{ M | quotient.lift (λ (M : bundled L.Structure), K M) (λ M N MN, h M N MN) M }

@[simp]
lemma is_equiv_invariant.mk_mem_to_set_quotient (h : is_equiv_invariant K)
  (M : bundled L.Structure) :
  (⟦M⟧ : quotient L.equiv_setoid) ∈ h.to_set_quotient ↔ K M :=
by rw [is_equiv_invariant.to_set_quotient, set.mem_set_of_eq, quotient.lift_mk]

/-- If `K` is a nonempty but essentially countable class of structures, there is a family of
  structures in `K`, indexed by `ℕ`, that covers every isomorphism class. -/
lemma exists_nat_transversal_of_countable_quotient (hn : K ≠ λ _ _, false)
  (h : is_equiv_invariant K) (hc : h.to_set_quotient.countable) :
  ∃ (f : ℕ → bundled.{w} L.Structure), ∀ (M : Type w) [strM : L.Structure M],
    @K M strM ↔ ∃ (n : ℕ), nonempty (@equiv L M (f n) strM _) :=
begin
  have hne : h.to_set_quotient.nonempty,
  { simp_rw [ne.def, function.funext_iff, not_forall, eq_iff_iff, iff_false, not_not] at hn,
    obtain ⟨M, strM, hM⟩ := hn,
    exact ⟨⟦⟨M, strM⟩⟧, hM⟩ },
  obtain ⟨f, hf⟩ := hc.exists_surjective hne,
  refine ⟨quotient.out ∘ f, λ M strM, _⟩,
  rw [is_equiv_invariant.to_set_quotient, set.ext_iff] at hf,
  have hfM := hf ⟦⟨M, strM⟩⟧,
  rw [mem_range, mem_set_of_eq, quotient.lift_mk] at hfM,
  simp_rw [quotient.eq_mk_iff_out] at hfM,
  exact hfM.trans (exists_congr (λ n, ⟨setoid.symm, λ h, setoid.symm h⟩)),
end

end language
end first_order
