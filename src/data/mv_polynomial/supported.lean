import ring_theory.adjoin
import data.mv_polynomial.variables

universes u v w

namespace mv_polynomial
variables {σ τ : Type*} {R : Type u} {S : Type v} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

section comm_semiring
variables [comm_semiring R] {p q : mv_polynomial σ R}

variables (R)

noncomputable def supported (s : set σ) : subalgebra R (mv_polynomial σ R) :=
algebra.adjoin R (X '' s)

local attribute [elab_as_eliminator] algebra.adjoin_induction

variables {σ R}

open_locale classical
open algebra

example {α β : Type*} (f : α → β) : α → set.range f := by library_search

lemma range_aeval {A : Type*} [comm_semiring A] [algebra R A]
  (f : σ → A) : (aeval f).range = adjoin R (set.range f) :=
begin
  ext x,
  simp only [adjoin_eq_range, alg_hom.mem_range],
  split,
  { rintros ⟨p, rfl⟩,
    use rename (set.range_factorization f) p,
    rw [← alg_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    ext,
    simp only [rename_X, function.comp_app, aeval_X, alg_hom.coe_comp,
      set.range_factorization_coe] },
  { rintros ⟨p, rfl⟩,
    use rename (function.surj_inv (@@set.surjective_onto_range f)) p,
    rw [← alg_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    ext,
    simp only [rename_X, function.comp_app, aeval_X, alg_hom.coe_comp],
    simpa [subtype.ext_iff] using function.surj_inv_eq (@@set.surjective_onto_range f) i }
end
#print finsupp.restrict_support_equiv
lemma supported_eq_range_rename (s : set σ) :
  supported R s = (rename (coe : s → σ)).range :=
by rw [supported, set.image_eq_range, ← range_aeval, rename]

-- @[elab_as_eliminator] lemma induction_on''
--   {M : mv_polynomial σ R → Prop} (p : mv_polynomial σ R)
--   (hC : ∀ x, M (C x))
--   (hmul : ∀ (m : σ →₀ ℕ) x i (n : ℕ), i ∉ m.support →
--     n ≠ 0 → M (monomial m x) → M (X i ^ n * monomial m x))
--   (hadd : ∀ (p : mv_polynomial σ R) (m : σ →₀ ℕ) x, m ∉ p.support →
--     x ≠ 0 → M (monomial m x) → M p → M (monomial m x + p)) : M p :=
-- finsupp.induction p
--   (by simpa using hC 0)
--   (λ m x p hmp hx0 hMp, hadd _ _ _ hmp hx0
--     begin
--       refine finsupp.induction m _ _,
--       { exact hC x },
--       { intros i n m hi hn hm,
--         rw [monomial_single_add],
--         exact hmul _ _ _ _ hi hn hm }
--     end
--     hMp)

lemma mem_supported {s : set σ} (p : mv_polynomial σ R) :
  p ∈ (supported R s) ↔ ↑p.vars ⊆ s :=
begin
  split,
  { rw [supported_eq_range_rename, alg_hom.mem_range],
    rintros ⟨p, rfl⟩,
    refine trans (finset.coe_subset.2 (vars_rename _ _)) _,
    simp },
  { intro h,
    rw [supported_eq_range_rename],

     }
  --rw [supported, algebra.adjoin_eq_range],
  -- cases subsingleton_or_nontrivial R,
  -- { admit, },
  -- { resetI, split,
  --   { assume h,
  --     rw [supported] at h,
  --     refine algebra.adjoin_induction h _ _ _ _,
  --     { simp },
  --     { simp [algebra_map_eq] },
  --     { intros p q hp hq,
  --       refine trans (finset.coe_subset.2 (vars_add_subset p q)) _,
  --       simp * },
  --     { intros p q hp hq,
  --       refine trans (finset.coe_subset.2 (vars_mul p q)) _,
  --       simp * } },
  --   { refine mv_polynomial.induction_on'' p _ _ _,
  --     { simp only [← algebra_map_eq, subalgebra.algebra_map_mem, forall_true_iff] },
  --     { intros m s i n hi hn ih h,

  --        }
  --      },
  --      }

end

end comm_semiring

end mv_polynomial
