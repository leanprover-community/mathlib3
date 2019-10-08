/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.integral_closure

/-!
# Algebraic elements and algebraic extensions
-/

universe variables u v

open_locale classical
open polynomial

section
variables (R : Type u) {A : Type v} [comm_ring R] [comm_ring A] [algebra R A]

/-- An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial. -/
def is_algebraic (x : A) : Prop :=
∃ p : polynomial R, p ≠ 0 ∧ aeval R A x p = 0

variables {R}

def subalgebra.is_algebraic (S : subalgebra R A) : Prop := ∀ x ∈ S, is_algebraic R x

variables (R A)

def algebra.is_algebraic : Prop := (⊤ : subalgebra R A).is_algebraic

variables {R A}

lemma algebra.is_algebraic_iff : algebra.is_algebraic R A ↔ ∀ x : A, is_algebraic R x :=
begin
  delta algebra.is_algebraic subalgebra.is_algebraic,
  simp only [algebra.mem_top, forall_prop_of_true, iff_self],
end

end

section zero_ne_one
variables (R : Type u) {A : Type v} [nonzero_comm_ring R] [comm_ring A] [algebra R A]

lemma is_integral.is_algebraic {x : A} (h : is_integral R x) : is_algebraic R x :=
begin
  rcases h with ⟨p, hp, hpx⟩,
  refine ⟨p, hp.ne_zero, hpx⟩,
end

end zero_ne_one

section field
variables (K : Type u) {L : Type v} [discrete_field K] [comm_ring L] [algebra K L]

lemma is_algebraic_iff_is_integral {x : L} :
  is_algebraic K x ↔ is_integral K x :=
begin
  refine ⟨_, is_integral.is_algebraic K⟩,
  rintro ⟨p, hp, hpx⟩,
  refine ⟨_, monic_mul_leading_coeff_inv hp, _⟩,
  rw [alg_hom.map_mul, hpx, zero_mul],
end

end field

namespace algebra
variables {K : Type*} {L : Type*} {A : Type*}
variables [discrete_field K] [discrete_field L] [comm_ring A]
variables [algebra K L] [algebra L A]

lemma is_algebraic_trans (L_alg : is_algebraic K L) (A_alg : is_algebraic L A) :
  is_algebraic K (comap K L A) :=
begin
  rw is_algebraic_iff at *,
  simp [is_algebraic_iff_is_integral] at L_alg A_alg ⊢,
  exact is_integral_trans L_alg A_alg,
end

end algebra
