import linear_algebra.clifford_algebra.fold
import linear_algebra.pi_tensor_product

variables (R M A : Type*) [field R] [add_comm_group M] [ring A] [module R M] [algebra R A]

#check alternating_map.module

namespace fin
def snoc' {n : ℕ} (α : fin n.succ → Sort*) (p : Π(i : fin n), α i.cast_succ) (x : α (last n)) (i : fin (n+1)) : α i :=
if h : i.val < n
then _root_.cast (by rw fin.cast_succ_cast_lt i h) (p (cast_lt i h))
else _root_.cast (by rw eq_last_of_not_lt h) x

end fin
def alternating_map.to_exterior_hom {n : ℕ} (f : alternating_map R M A (fin n)) :
  clifford_algebra (0 : quadratic_form R M) →ₗ[R] A :=
begin
  letI : module R (Π i : fin n.succ, alternating_map R M A (fin i)) :=
    @pi.module (fin n.succ) (λ i, alternating_map R M A (fin i)) R _ _ (λ i,
      alternating_map.module),
  suffices : clifford_algebra (0 : quadratic_form R M) →ₗ[R] (Π i : fin n.succ, alternating_map R M A (fin i)),
  sorry,
  refine clifford_algebra.foldr (0 : quadratic_form R M) _ _ _,
  refine linear_map.mk₂ R (λ m f, _) sorry sorry sorry sorry,
  refine fin.snoc (λ i, _) 0,
  { have f' := (f (fin.succ i)).dom_dom_congr (fin.cast $ fin.coe_succ _).to_equiv,
    refine f'.curry_left m },
  { intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    refine fin.last_cases _ (λ i', _) i; clear i; dsimp only [pi.zero_apply],
    { rw [fin.snoc_last] },
    simp_rw [fin.snoc_cast_succ],
    generalize_proofs _ hi',
    revert hi',
    generalize hi'' : fin.succ i' = i'',
    revert hi'',
    -- simp_rw ←@alternating_map.dom_dom_congr_trans R _,
    refine fin.last_cases _ (λ i''', _) i''; intros hi' hi'',
    { rw [fin.snoc_last], ext i, exact eq.refl (0 : A) },
    simp_rw [fin.snoc_cast_succ],
    have := alternating_map.curry_left_same (x _) m,
    generalize_proofs hi''',
    convert alternating_map.curry_left_same _ m,
    simp_rw fin.coe_cast_succ,
    subst hi',
    rw @alternating_map.dom_dom_congr_refl R _ M _ _ _ _ _ (fin i''') _,
    subst hi'',
    simp at hi'
    simp,
    refine (alternating_map.dom_dom_congr_trans _ _ _).symm.trans _,
     dsimp, simp, sorry },
  -- refine linear_map.fst R A (fin n → A) ∘ₗ _,
  -- refine clifford_algebra.foldr (0 : quadratic_form R M) _ _ _,
end

#check fin.coe_succ

/--
Recursive step:

(![0, 0, 0], a )
(1, (a, b, c, d))
(f a, (b, c, d, 0))
(f a b, (c, d, 0, 0))
(f a b c, (d, 0, 0, 0))
(f a b c d, (d, 0, 0, 0))
(0, 0, 0, 0, 0, f)
(0, 0, 0, 0, f.bind a, 0)
(0, 0, 0, (f.bind a).bind b, f.bind b)

-/
