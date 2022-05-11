import algebra.big_operators.ring
import algebra.geom_sum

-- "for_mathlib": these should be moved to their natural homes in mathlib

@[simp] lemma sum_neg_one_pow {α : Type*} [ring α] (n : ℕ) :
  (finset.range n).sum (λ i, (-1 : α)^i) = if even n then 0 else 1 :=
neg_one_geom_sum

@[simp] lemma neg_one_pow_mul_neg_one_pow {α : Type*} [monoid α] [has_distrib_neg α] (n : ℕ) :
  (-1 : α)^n * (-1 : α)^n = 1 :=
by { rw [←pow_add, ←two_mul, pow_mul, neg_one_sq, one_pow], }

@[simp] lemma has_neg_neg_iterate {α : Type*} [add_comm_group α] (n : ℕ) (a : α) :
  has_neg.neg^[n] a = (-1 : ℤ)^n • a :=
by { induction n with n ih generalizing a, simp, simp [ih, pow_succ], }

-- This one is a little deceptive: the `w` argument isn't necessary for the definition,
-- so mathlib style says we should omit it. However the "no-cheating" proof breaks if we do so!
def iterate₂ {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) : ℕ × ℕ → α :=
λ p, f^[p.1] (g^[p.2] z)

@[simp] lemma iterate₂_succ_left
  {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) (x y : ℕ) :
  iterate₂ z f g w (x + 1, y) = f (iterate₂ z f g w (x, y)) :=
function.iterate_succ_apply' _ _ _

@[simp] lemma iterate₂_succ_right
  {α : Type*} (z : α) (f g : α → α) (w : ∀ a, f (g a) = g (f a)) (x y : ℕ) :
  iterate₂ z f g w (x, y + 1) = g (iterate₂ z f g w (x, y)) :=
begin
  have w : function.commute f g := w,
  dsimp [iterate₂],
  rw [←function.iterate_succ_apply, w.iterate_iterate, w.iterate_iterate,
    ←function.iterate_succ_apply' g],
end
