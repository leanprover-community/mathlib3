import algebra.big_operators
open int
open euclidean_domain
--https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/B.C3.A9zout's.20identity/near/222324467
-- this is at https://github.com/AdrianDoM/IMOinLEAN/blob/main/src/imo/bezout.lean

lemma map_mul_sum (r : ℤ) (l : list ℤ) : (l.map ((*) (r : ℤ))).sum = r * l.sum :=
by convert list.sum_hom l ⟨((*) r), mul_zero r, λ x y, mul_add r x y⟩
lemma zip_with_mul_map_mul (r : ℤ) (l₁ l₂ : list ℤ) : l₁.zip_with (*) (l₂.map ((*) (r : ℤ))) =
                                                     (l₁.zip_with (*) l₂).map ((*) (r : ℤ)) := sorry

def asd : Π (l : list ℤ), {a : list ℤ // l.foldr gcd 0 = (l.zip_with (*) a).sum }
| [] := ⟨ [], by simp ⟩
| (h :: ll) := ⟨ gcd_a h (ll.foldr gcd 0) :: ((asd ll : list ℤ).map ((*) (gcd_b h (ll.foldr gcd 0)))), begin
 simp,
 convert gcd_eq_gcd_ab _ _,
 have := (asd ll).2,
 simp [zip_with_mul_map_mul _ _ _, map_mul_sum],
 rw mul_comm,
 congr,
 exact this.symm,
end⟩
#eval asd [6, 15, 10]



