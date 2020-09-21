import data.polynomial.ring_division
import data.mv_polynomial.rename
import ring_theory.polynomial.basic

namespace polynomial

variables {R : Type*} [integral_domain R] [infinite R]

lemma zero_of_eval_zero (p : polynomial R) (h : ∀ x, p.eval x = 0) : p = 0 :=
by classical; by_contradiction hp; exact
infinite.not_fintype ⟨p.roots.to_finset, λ x, multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

lemma funext {p q : polynomial R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q :=
begin
  rw ← sub_eq_zero,
  apply zero_of_eval_zero,
  intro x,
  rw [eval_sub, sub_eq_zero, ext],
end

end polynomial

namespace mv_polynomial

variables {R : Type*} [integral_domain R] [infinite R]

-- move this
instance {σ : Type*} : infinite (mv_polynomial σ R) :=
infinite.of_injective C (C_injective _ _)

-- move this!
instance poly_inf : infinite (polynomial R) :=
infinite.of_injective polynomial.C (λ r s h, polynomial.C_inj.mp h)

-- move this
@[simp] lemma fin_succ_equiv_apply (n : ℕ) (p : mv_polynomial (fin (n + 1)) R) :
  fin_succ_equiv R n p = 0 :=
begin
  change (option_equiv_left R (fin n) (rename _ p))  = _,

end

lemma funext_fin {n : ℕ} {p : mv_polynomial (fin n) R}
  (h : ∀ x : fin n → R, eval x p = 0) : p = 0 :=
begin
  unfreezingI { revert R },
  induction n with n ih,
  { introsI R _ _ p h,
    let e := (ring_equiv_of_equiv R fin_zero_equiv').trans (mv_polynomial.pempty_ring_equiv R),
    apply e.injective,
    rw ring_equiv.map_zero,
    convert h fin_zero_elim,
    show (eval₂_hom (ring_hom.id _) pempty.elim) (rename fin_zero_equiv' p) = _,
    rw [eval₂_hom_rename],
    exact eval₂_hom_congr rfl (subsingleton.elim _ _) rfl },
  { introsI R _ _ p h,
    let e := fin_succ_equiv R n,
    apply e.injective,
    simp only [ring_equiv.map_zero],
    apply polynomial.funext,
    intro r,
    rw [polynomial.eval_zero],
    apply ih, swap, { apply_instance },
    intro x,
    dsimp [e],
    -- change polynomial.eval r (eval x ((eval₂_hom (ring_hom.id _) _) _)) = 0,
    -- suffices : ∀ (p : mv_polynomial (fin (n + 1)) R),
    --   polynomial.eval r (eval x (e p)) = _,
       }
end

end mv_polynomial
