/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import data.set.pointwise.basic
import data.set.mul_antidiagonal

/-! # Multiplication antidiagonal as a `finset`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the `finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered.-/

namespace set

open_locale pointwise
variables {α : Type*} {s t : set α}

@[to_additive]
lemma is_pwo.mul [ordered_cancel_comm_monoid α] (hs : s.is_pwo) (ht : t.is_pwo) : is_pwo (s * t) :=
by { rw ←image_mul_prod, exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd) }

variables [linear_ordered_cancel_comm_monoid α]

@[to_additive]
lemma is_wf.mul (hs : s.is_wf) (ht : t.is_wf) : is_wf (s * t) := (hs.is_pwo.mul ht.is_pwo).is_wf

@[to_additive]
lemma is_wf.min_mul (hs : s.is_wf) (ht : t.is_wf) (hsn : s.nonempty) (htn : t.nonempty) :
  (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn :=
begin
  refine le_antisymm (is_wf.min_le _ _ (mem_mul.2 ⟨_, _, hs.min_mem _, ht.min_mem _, rfl⟩)) _,
  rw is_wf.le_min_iff,
  rintro _ ⟨x, y, hx, hy, rfl⟩,
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy),
end

end set

namespace finset

open_locale pointwise

variables {α : Type*}
variables [ordered_cancel_comm_monoid α] {s t : set α} (hs : s.is_pwo) (ht : t.is_pwo) (a : α)

/-- `finset.mul_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive "`finset.add_antidiagonal_of_is_wf hs ht a` is the set of all pairs of an element in
`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are
well-ordered."]
noncomputable def mul_antidiagonal : finset (α × α) :=
(set.mul_antidiagonal.finite_of_is_pwo hs ht a).to_finset

variables {hs ht a} {u : set α} {hu : u.is_pwo} {x : α × α}

@[simp, to_additive]
lemma mem_mul_antidiagonal : x ∈ mul_antidiagonal hs ht a ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ x.1 * x.2 = a :=
by simp [mul_antidiagonal, and_rotate]

@[to_additive] lemma mul_antidiagonal_mono_left (h : u ⊆ s) :
  mul_antidiagonal hu ht a ⊆ mul_antidiagonal hs ht a :=
set.finite.to_finset_mono $ set.mul_antidiagonal_mono_left h

@[to_additive] lemma mul_antidiagonal_mono_right (h : u ⊆ t) :
  mul_antidiagonal hs hu a ⊆ mul_antidiagonal hs ht a :=
set.finite.to_finset_mono $ set.mul_antidiagonal_mono_right h

@[simp, to_additive] lemma swap_mem_mul_antidiagonal :
  x.swap ∈ finset.mul_antidiagonal hs ht a ↔ x ∈ finset.mul_antidiagonal ht hs a :=
by simp [mul_comm, and.left_comm]

@[to_additive]
lemma support_mul_antidiagonal_subset_mul : {a | (mul_antidiagonal hs ht a).nonempty} ⊆ s * t :=
λ a ⟨b, hb⟩, by { rw mem_mul_antidiagonal at hb, exact ⟨b.1, b.2, hb⟩ }

@[to_additive]
lemma is_pwo_support_mul_antidiagonal : {a | (mul_antidiagonal hs ht a).nonempty}.is_pwo :=
(hs.mul ht).mono support_mul_antidiagonal_subset_mul

@[to_additive]
lemma mul_antidiagonal_min_mul_min {α} [linear_ordered_cancel_comm_monoid α] {s t : set α}
  (hs : s.is_wf) (ht : t.is_wf) (hns : s.nonempty) (hnt : t.nonempty) :
  mul_antidiagonal hs.is_pwo ht.is_pwo ((hs.min hns) * (ht.min hnt)) = {(hs.min hns, ht.min hnt)} :=
begin
  ext ⟨a, b⟩,
  simp only [mem_mul_antidiagonal, mem_singleton, prod.ext_iff],
  split,
  { rintro ⟨has, hat, hst⟩,
    obtain rfl := (hs.min_le hns has).eq_of_not_lt
      (λ hlt, (mul_lt_mul_of_lt_of_le hlt $ ht.min_le hnt hat).ne' hst),
    exact ⟨rfl, mul_left_cancel hst⟩ },
  { rintro ⟨rfl, rfl⟩,
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩ }
end

end finset
