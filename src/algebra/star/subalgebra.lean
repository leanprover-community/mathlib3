/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.star.basic
import algebra.algebra.subalgebra.basic

/-!
# Star subalgebras

A *-subalgebra is a subalgebra of a *-algebra which is closed under *.

The centralizer of a *-closed set is a *-subalgebra.
-/

universes u v

set_option old_structure_cmd true

/-- A *-subalgebra is a subalgebra of a *-algebra which is closed under *. -/
structure star_subalgebra (R : Type u) (A : Type v) [comm_semiring R] [star_ring R]
  [semiring A] [star_ring A] [algebra R A] [star_module R A] extends subalgebra R A : Type v :=
(star_mem' {a} : a ∈ carrier → star a ∈ carrier)

namespace star_subalgebra

/--
Forgetting that a *-subalgebra is closed under *.
-/
add_decl_doc star_subalgebra.to_subalgebra

variables (R : Type u) (A : Type v) [comm_semiring R] [star_ring R]
  [semiring A] [star_ring A] [algebra R A] [star_module R A]

instance : set_like (star_subalgebra R A) A :=
⟨star_subalgebra.carrier, λ p q h, by cases p; cases q; congr'⟩

instance : has_top (star_subalgebra R A) :=
⟨{ star_mem' := by tidy, ..(⊤ : subalgebra R A) }⟩

instance : inhabited (star_subalgebra R A) := ⟨⊤⟩

section centralizer
variables {A}

/-- The centralizer, or commutant, of a *-closed set as star subalgebra. -/
def centralizer
  (s : set A) (w : ∀ (a : A), a ∈ s → star a ∈ s) : star_subalgebra R A :=
{ star_mem' := λ x xm y hy, by simpa using congr_arg star (xm _ (w _ hy)).symm,
  ..subalgebra.centralizer R s, }

@[simp]
lemma coe_centralizer (s : set A) (w : ∀ (a : A), a ∈ s → star a ∈ s) :
  (centralizer R s w : set A) = s.centralizer := rfl

lemma mem_centralizer_iff {s : set A} {w} {z : A} :
  z ∈ centralizer R s w ↔ ∀ g ∈ s, g * z = z * g :=
iff.rfl

lemma centralizer_le (s t : set A)
  (ws : ∀ (a : A), a ∈ s → star a ∈ s) (wt : ∀ (a : A), a ∈ t → star a ∈ t) (h : s ⊆ t) :
  centralizer R t wt ≤ centralizer R s ws :=
set.centralizer_subset h

end centralizer

end star_subalgebra
