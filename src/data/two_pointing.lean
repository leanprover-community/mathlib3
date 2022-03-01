/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.sum.basic
import logic.nontrivial

/-!
# Two-pointings

This file defines `two_pointing α`, the type of two pointings of `α`. A two-pointing is the data of
two distinct terms.

This is morally a Type-valued `nontrivial`. Another type which is quite close in essence is `sym2`.
Categorically speaking, `prod` is a cospan in the category of types. This forms the category of
bipointed types. Two-pointed types form a full subcategory of those.

## References

* [nLab, *Coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

open function

variables {α β : Type*}

/-- Two-pointing of a type. This is a Type-valued termed `nontrivial`. -/
@[ext, derive decidable_eq] structure two_pointing (α : Type*) extends α × α :=
(fst_ne_snd : fst ≠ snd)

namespace two_pointing
variables (p : two_pointing α) (q : two_pointing β)

lemma snd_ne_fst : p.snd ≠ p.fst := p.fst_ne_snd.symm

/-- Swaps the two pointed elements. -/
@[simps] def swap : two_pointing α := ⟨(p.snd, p.fst), p.snd_ne_fst⟩

lemma swap_fst : p.swap.fst = p.snd := rfl
lemma swap_snd : p.swap.snd = p.fst := rfl
@[simp] lemma swap_swap : p.swap.swap = p := by ext; refl

@[reducible] -- See note [reducible non instances]
lemma to_nontrivial : nontrivial α := ⟨⟨p.fst, p.snd, p.fst_ne_snd⟩⟩

instance [nontrivial α] : nonempty (two_pointing α) :=
let ⟨a, b, h⟩ := exists_pair_ne α in ⟨⟨(a, b), h⟩⟩

@[simp] lemma nonempty_two_pointing_iff : nonempty (two_pointing α) ↔ nontrivial α :=
⟨λ ⟨p⟩, p.to_nontrivial, @two_pointing.nonempty _⟩

section pi
variables (α) [nonempty α]

/-- The two-pointing of constant functions. -/
def pi : two_pointing (α → β) :=
{ fst := λ _, q.fst,
  snd := λ _, q.snd,
  fst_ne_snd := λ h, q.fst_ne_snd $ by convert congr_fun h (classical.arbitrary α) }

@[simp] lemma pi_fst : (q.pi α).fst = const α (q.fst) := rfl
@[simp] lemma pi_snd : (q.pi α).snd = const α (q.snd) := rfl

end pi

/-- The product of two two-pointings. -/
def prod : two_pointing (α × β) :=
{ fst := (p.fst, q.fst),
  snd := (p.snd, q.snd),
  fst_ne_snd := λ h, p.fst_ne_snd (congr_arg prod.fst h) }

@[simp] lemma prod_fst : (p.prod q).fst = (p.fst, q.fst) := rfl
@[simp] lemma prod_snd : (p.prod q).snd = (p.snd, q.snd) := rfl

/-- The sum of two pointings. Keeps the first point from the left and the second point from the
right. -/
protected def sum : two_pointing (α ⊕ β) := ⟨(sum.inl (p.fst), sum.inr (q.snd)), sum.inl_ne_inr⟩

@[simp] lemma sum_fst : (p.sum q).fst = sum.inl p.fst := rfl
@[simp] lemma sum_snd : (p.sum q).snd = sum.inr q.snd := rfl

/-- The `ff`, `tt` two-pointing of `bool`. -/
protected def bool : two_pointing bool := ⟨(ff, tt), bool.ff_ne_tt⟩

@[simp] lemma bool_fst : two_pointing.bool.fst = ff := rfl
@[simp] lemma bool_snd : two_pointing.bool.snd = tt := rfl

instance : inhabited (two_pointing bool) := ⟨two_pointing.bool⟩

/-- The `false`, `true` two-pointing of `Prop`. -/
protected def «Prop» : two_pointing Prop := ⟨(false, true), false_ne_true⟩

@[simp] lemma Prop_fst : two_pointing.Prop.fst = false := rfl
@[simp] lemma Prop_snd : two_pointing.Prop.snd = true := rfl

end two_pointing
