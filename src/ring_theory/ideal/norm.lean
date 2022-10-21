/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/

import linear_algebra.isomorphisms
import ring_theory.dedekind_domain.ideal

/-!
# Ideal norms
This file will define the absolute ideal norm `ideal.abs_norm (I : ideal R) : ℕ` as the cardinality
of the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions
 * `submodule.card_quot (S : submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
   This maps `⊥` to `0` and `⊤` to `1`.

## TODO
 * `ideal.abs_norm (I : ideal R)`: the absolute ideal norm, defined as
   the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.
   (In an upcoming PR!)

 * Define the relative norm.

-/

open_locale big_operators

namespace submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

section

open_locale classical

/-- The cardinality of `(M ⧸ S)`, if `(M ⧸ S)` is finite, and `0` otherwise.
This is used to define the absolute ideal norm `ideal.abs_norm`.
-/
noncomputable def card_quot (S : submodule R M) : ℕ :=
if h : nonempty (fintype (M ⧸ S)) then @fintype.card _ h.some else 0

@[simp] lemma card_quot_apply (S : submodule R M) [h : fintype (M ⧸ S)] :
  card_quot S = fintype.card (M ⧸ S) :=
by convert dif_pos (nonempty.intro h) -- `convert` deals with the different `fintype` instances

@[simp] lemma card_quot_bot [infinite M] : card_quot (⊥ : submodule R M) = 0 :=
dif_neg (by simp; apply_instance)

@[simp] lemma card_quot_top : card_quot (⊤ : submodule R M) = 1 :=
calc card_quot ⊤ = fintype.card (M ⧸ ⊤) : card_quot_apply _
... = fintype.card punit : fintype.card_eq.mpr ⟨equiv_of_subsingleton_of_subsingleton 0 0⟩
... = 1 : fintype.card_punit

@[simp] lemma card_quot_eq_one_iff {P : submodule R M} : card_quot P = 1 ↔ P = ⊤ :=
begin
  unfold card_quot,
  split_ifs,
  { rw [fintype.card_eq_one_iff_nonempty_unique, submodule.unique_quotient_iff_eq_top] },
  { simp only [zero_ne_one, false_iff],
    rintro rfl,
    have : nonempty (fintype (M ⧸ ⊤)) := ⟨@quotient_top.fintype R M _ _ _⟩,
    contradiction }
end

end

end submodule
