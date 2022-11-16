/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.function.basic
import tactic.algebra
import tactic.alias
import tactic.auto_cases
import tactic.basic
import tactic.binder_matching
import tactic.chain
import tactic.choose
import tactic.clear
import tactic.congr
import tactic.converter.apply_congr
import tactic.converter.interactive
import tactic.converter.old_conv
import tactic.core
import tactic.dec_trivial
import tactic.delta_instance
import tactic.dependencies
import tactic.derive_inhabited
import tactic.elide
import tactic.explode
import tactic.ext
import tactic.find
import tactic.finish
import tactic.generalize_proofs
import tactic.generalizes
import tactic.hint
import tactic.interactive
import tactic.interactive_expr
import tactic.itauto
import tactic.lean_core_docs
import tactic.lift
import tactic.lint.basic
import tactic.lint.default
import tactic.lint.frontend
import tactic.lint.misc
import tactic.lint.simp
import tactic.lint.type_classes
import tactic.localized
import tactic.mk_iff_of_inductive_prop
import tactic.norm_cast
import tactic.obviously
import tactic.pretty_cases
import tactic.project_dir
import tactic.protected
import tactic.push_neg
import tactic.rcases
import tactic.rename_var
import tactic.replacer
import tactic.restate_axiom
import tactic.rewrite
import tactic.show_term
import tactic.simpa
import tactic.simp_command
import tactic.simp_result
import tactic.simp_rw
import tactic.simps
import tactic.solve_by_elim
import tactic.split_ifs
import tactic.squeeze
import tactic.suggest
import tactic.tauto
import tactic.tidy
import tactic.to_additive
import tactic.transform_decl
import tactic.trunc_cases
import tactic.unify_equations
import tactic.where

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `pairwise`: `pairwise r` states that `r i j` for all `i ≠ j`.
* `set.pairwise`: `s.pairwise r` states that `r i j` for all `i ≠ j` with `i, j ∈ s`.
-/

open set function

variables {α β γ ι ι' : Type*} {r p q : α → α → Prop}

section pairwise
variables {f g : ι → α} {s t u : set α} {a b : α}

/-- A relation `r` holds pairwise if `r i j` for all `i ≠ j`. -/
def pairwise (r : α → α → Prop) := ∀ ⦃i j⦄, i ≠ j → r i j

lemma pairwise.mono (hr : pairwise r) (h : ∀ ⦃i j⦄, r i j → p i j) : pairwise p :=
λ i j hij, h $ hr hij

protected lemma pairwise.eq (h : pairwise r) : ¬ r a b → a = b := not_imp_comm.1 $ @h _ _

lemma function.injective_iff_pairwise_ne : injective f ↔ pairwise ((≠) on f) :=
forall₂_congr $ λ i j, not_imp_not.symm

alias function.injective_iff_pairwise_ne ↔ function.injective.pairwise_ne _

namespace set

/-- The relation `r` holds pairwise on the set `s` if `r x y` for all *distinct* `x y ∈ s`. -/
protected def pairwise (s : set α) (r : α → α → Prop) := ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → r x y

lemma pairwise_of_forall (s : set α) (r : α → α → Prop) (h : ∀ a b, r a b) : s.pairwise r :=
λ a _ b _ _, h a b

lemma pairwise.imp_on (h : s.pairwise r) (hrp : s.pairwise (λ ⦃a b : α⦄, r a b → p a b)) :
  s.pairwise p :=
λ a ha b hb hab, hrp ha hb hab $ h ha hb hab

lemma pairwise.imp (h : s.pairwise r) (hpq : ∀ ⦃a b : α⦄, r a b → p a b) : s.pairwise p :=
h.imp_on $ pairwise_of_forall s _ hpq

protected lemma pairwise.eq (hs : s.pairwise r) (ha : a ∈ s) (hb : b ∈ s) (h : ¬ r a b) : a = b :=
of_not_not $ λ hab, h $ hs ha hb hab

lemma _root_.reflexive.set_pairwise_iff (hr : reflexive r) :
  s.pairwise r ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b :=
forall₄_congr $ λ a _ b _, or_iff_not_imp_left.symm.trans $ or_iff_right_of_imp $ eq.rec $ hr a

lemma pairwise.on_injective (hs : s.pairwise r) (hf : function.injective f)
  (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs (hfs i) (hfs j) (hf.ne hij)

end set

lemma pairwise.set_pairwise (h : pairwise r) (s : set α) : s.pairwise r := λ x hx y hy w, h w

end pairwise
