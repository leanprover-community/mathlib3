import data.mv_polynomial
import linear_algebra.smodeq

open_locale big_operators

namespace mv_polynomial

variables {I J R : Type*} [fintype I] [decidable_eq I] [comm_ring R]
  (p : submodule (mv_polynomial J R) (I → mv_polynomial J R))

def smodeq_C_add_submonoid : add_submonoid (I → mv_polynomial J R) :=
{ carrier := {x | ∃ r : I → R, x ≡ C ∘ r [SMOD p]},
  add_mem' := λ x y ⟨rx, hx⟩ ⟨ry, hy⟩, ⟨rx + ry, by { convert hx.add hy, ext1, exact C_add }⟩,
  zero_mem' := ⟨0, by { convert smodeq.refl, ext1, exact C_0 }⟩ }

variable {p}
lemma mem_smodeq_C_add_submonoid_of_smodeq {x y} (h : x ≡ y [SMOD p]) :
  x ∈ smodeq_C_add_submonoid p ↔ y ∈ smodeq_C_add_submonoid p :=
⟨λ ⟨r, hx⟩, ⟨r, h.symm.trans hx⟩, λ ⟨r, hy⟩, ⟨r, h.trans hy⟩⟩

lemma C_comp_smul {a : I → R} {r : R} :
  @C _ J _ ∘ (r • a) = (@C _ J _ r) • (@C _ J _ ∘ a) :=
funext (λ _, C_mul)

/- compiles in about 8 seconds -/
lemma exists_smodeq_of_X_exists_smodeq
  (h : ∀ i j, ∃ r : I → R, pi.single i (X j) ≡ C ∘ r [SMOD p]) :
  ∀ x, ∃ r : I → R, x ≡ C ∘ r [SMOD p] :=
begin
  intro x, rw pi_eq_sum_univ_single x,
  apply @finset.sum_induction _ _ _ _ _ (λ m, ∃ r, m ≡ C ∘ r [SMOD p]) _ _,
  { rintro i -,
    have : x i ∈ (⊤ : subalgebra R _) := algebra.mem_top,
    rw ← adjoin_range_X at this,
    apply subsemiring.smul_mem_of_mem_closure (smodeq_C_add_submonoid p) _ _ _ this,
    { use pi.single i 1, convert smodeq.refl, ext1,
      simp only [pi.single_apply, apply_ite C, function.comp_app, C_1, C_0] },
    rintro x (⟨s,rfl⟩|⟨j,rfl⟩) m ⟨r, hr⟩,
    { use s • r, rw C_comp_smul, exact hr.smul _ },
    { rw [mem_smodeq_C_add_submonoid_of_smodeq (hr.smul $ X j),
        pi_eq_sum_univ_single (C ∘ r), finset.smul_sum],
      apply sum_mem,
      rintro i -,
      obtain ⟨r', hr'⟩ := h i j,
      use r i • r',
      rw [smul_comm, ← pi.single_smul', smul_eq_mul, mul_one, C_comp_smul],
      exact hr'.smul (C $ r i) } },
  { rintro a b ⟨ra, ha⟩ ⟨rb, hb⟩, use ra + rb, convert ha.add hb, ext1, exact C_add },
  { use 0, convert smodeq.refl, ext1, exact C_0 },
end

end mv_polynomial
