/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENsE.
Authors: Johan Commelin
-/
import ring_theory.subring.basic

/-!
# Centralizer of a ring.

## Main definitions

* `subring.centralizer`: the centralizer of a member of a ring.

-/


lemma set.center_subset_centraliser {α} [has_mul α] (s : set α) : set.center α ⊆ s.centralizer :=
λ x hx m _, hx m

namespace subring

variables {R : Type*} [ring R]

def centralizer (s : set R) : subring R :=
{ neg_mem' := λ x, set.neg_mem_centralizer,
  ..subsemiring.centralizer s }

@[simp, norm_cast]
lemma coe_centralizer (s : set R) : (centralizer s : set R) = s.centralizer := rfl

lemma centralizer_to_submonoid (s : set R) :
  (centralizer s).to_submonoid = submonoid.centralizer s := rfl

lemma centralizer_to_subsemiring (s : set R) :
  (centralizer s).to_subsemiring = subsemiring.centralizer s := rfl

lemma mem_centralizer_iff {s : set R} {z : R} :
  z ∈ centralizer s ↔ ∀ g ∈ s, g * z = z * g :=
iff.rfl

lemma center_le_centralizer (s) : center R ≤ centralizer s := s.center_subset_centraliser

lemma centralizer_le (s t : set R) (h : s ⊆ t) : centralizer t ≤ centralizer s :=
set.centralizer_subset h

@[simp] lemma centralizer_univ : centralizer set.univ = center R :=
set_like.ext' (set.centralizer_univ R)

lemma mem_center_of_centralizer_eq_top {r : R} (h : centralizer ({r} : set R) = ⊤) :
  r ∈ center R :=
λ x, eq.symm $ by simpa [mem_centralizer_iff] using eq_top_iff.mp h (mem_top x)

end subring
