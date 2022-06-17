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
  { have f' := f (fin.succ i),
    rw fin.coe_cast_succ,
    rw fin.coe_succ at f',
    refine f'.curry_left m,},
  { intros m x,
    dsimp only [linear_map.mk₂_apply, quadratic_form.coe_fn_zero, pi.zero_apply],
    simp_rw zero_smul,
    ext i : 1,
    dsimp,
    refine fin.last_cases _ (λ i, _) i,
    { rw fin.snoc_last, },
    { rw fin.snoc_cast_succ, sorry} },
  -- refine linear_map.fst R A (fin n → A) ∘ₗ _,
  -- refine clifford_algebra.foldr (0 : quadratic_form R M) _ _ _,
end


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
