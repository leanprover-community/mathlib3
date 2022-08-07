/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Andrew Yang
-/

import data.mv_polynomial
import linear_algebra.smodeq

/-!

# Results about `I → mv_polynomial J R`

We collect results about the ring `(R[x₁,...,xₙ])ᵏ` here.

-/

open_locale big_operators

namespace mv_polynomial

variables {I J R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
  {p : submodule (mv_polynomial J R) (I → mv_polynomial J R)}

lemma C_comp_smul {a : I → R} {r : R} :
  @C _ J _ ∘ (r • a) = (@C _ J _ r) • (@C _ J _ ∘ a) :=
funext (λ _, C_mul)

lemma exists_smodeq_of_X_exists_smodeq [finite I] [decidable_eq I]
  (h : ∀ i j, ∃ r : I → R, pi.single i (X j) ≡ C ∘ r [SMOD p]) :
  ∀ x, ∃ r : I → R, x ≡ C ∘ r [SMOD p] :=
begin
  let q := ((C : R →+* (mv_polynomial J R)).comp_left I)
    .srange.to_add_submonoid.smodeq_closure p,
  have hq : ∀ x, x ∈ q ↔ ∃ r : I → R, x ≡ C ∘ r [SMOD p] := λ x, ⟨_, _⟩,
  rotate, { rintro ⟨_, ⟨r, rfl⟩, hr⟩, exact ⟨r, hr⟩ }, { rintros ⟨r, hr⟩, exact ⟨_, ⟨r, rfl⟩, hr⟩ },
  casesI nonempty_fintype I,
  intro x, rw pi_eq_sum_univ_single x,
  apply @finset.sum_induction _ _ _ _ _ (λ m, ∃ r, m ≡ C ∘ r [SMOD p]) _ _,
  { rintro i -,
    have : x i ∈ (⊤ : subalgebra R _) := algebra.mem_top,
    rw ← adjoin_range_X at this,
    simp_rw ← hq,
    apply subsemiring.smul_mem_of_mem_closure q _ _ _ this; simp_rw hq,
    { use pi.single i 1, convert smodeq.refl, ext1,
      simp only [pi.single_apply, apply_ite C, function.comp_app, C_1, C_0] },
    rintro x (⟨s,rfl⟩|⟨j,rfl⟩) m ⟨r, hr⟩,
    { use s • r, rw C_comp_smul, exact hr.smul _ },
    { rw [← hq, add_submonoid.mem_smodeq_closure_of_smodeq _ (hr.smul $ X j),
        pi_eq_sum_univ_single (C ∘ r), finset.smul_sum],
      apply sum_mem,
      rintro i -,
      obtain ⟨r', hr'⟩ := h i j,
      rw hq,
      use r i • r',
      rw [smul_comm, ← pi.single_smul', smul_eq_mul, mul_one, C_comp_smul],
      exact hr'.smul (C $ r i) } },
  { rintro a b ⟨ra, ha⟩ ⟨rb, hb⟩, use ra + rb, convert ha.add hb, ext1, exact C_add },
  { use 0, convert smodeq.refl, ext1, exact C_0 },
end

end mv_polynomial
