import data.dfinsupp.basic
import tactic

universes u v w

namespace dfinsupp.prod

variables {ι₁ : Type u} {ι₂ : Type v}
variables {β : ι₁ → ι₂ → Type w} [Π i j, has_zero (β i j)]

-- this definition is complete, and looks fairly readable - although there may be a shorter way
def curry (f : Π₀ (ij : ι₁ × ι₂), β ij.1 ij.2) : Π₀ i, Π₀ j, β i j :=
begin
  refine quotient.lift_on f (λ fij, _) (λ a b H, _),
  exact ⟦{
    to_fun := λ i, ⟦ {
      to_fun := λ j, fij.to_fun (i, j),
      pre_support := fij.pre_support.map prod.snd,
      zero := λ j, begin
        rw multiset.mem_map,
        refine (fij.zero (i, j)).imp_left _,
        intro hin,
        exact ⟨(i, j), hin, rfl⟩
      end
    } ⟧,
    pre_support := fij.pre_support.map prod.fst,
    zero := λ i, begin
      rw multiset.mem_map,
      refine or.imp id quotient.sound _,
      refine forall_or_distrib_left.mp (λ j, _),
      refine (fij.zero (i, j)).imp_left _,
      intro hin,
      exact ⟨(i, j), hin, rfl⟩
    end
  }⟧,
  exact (quotient.sound $ λ i, quotient.sound $ λ j, H (i, j)),
end

-- this was my first attempt, which requires me to prove untrue statements
def uncurry (f : Π₀ i j, β i j) : Π₀ (ij : ι₁ × ι₂), β ij.1 ij.2 := begin
  fapply quotient.lift_on f,
  exact λ fi, ⟦{
    to_fun := λ ij, fi.to_fun ij.fst ij.snd,
    pre_support := fi.pre_support.bind (λ i, begin
      let js : multiset ι₂ := quotient.lift_on (fi.to_fun i)
        dfinsupp.pre.pre_support
        (λ a b H, begin
          /- This is unprovable, I think lift_on is the wrong approach, or I need to return a clever quotient -/
          sorry
        end),
      exact js.map (prod.mk i)
    end),
    zero := λ ij, begin
      rw multiset.mem_bind,
      cases fi.zero ij.fst,
      { left, use ij.fst, simp [h], use ij.snd, simp,
        sorry},
      { right, simp [h] }
    end
  }⟧,
  exact λ a b H, quotient.sound $ λ ij, by simp [H ij.fst],
end

-- second attempt, by rewriting the inner function into a product function first.
def uncurry2  [decidable_eq ι₁] [decidable_eq ι₂] (f : Π₀ i j, β i j) :
  Π₀ (ij : ι₁ × ι₂), β ij.1 ij.2 :=
begin
  fapply quotient.lift_on f,
  exact λ fi, by {
    -- build a set of functions, each non-zero for a single i
    let fij : multiset (Π₀ (ij : ι₁ × ι₂), β ij.fst ij.snd) := fi.pre_support.map (λ i, begin
      fapply quotient.lift_on (fi.to_fun i),
      exact λ fij, begin
        exact ⟦{
          to_fun := λ ij, dite (ij.fst = i) (λ h, begin
            rw h,
            exact fij.to_fun ij.snd,
          end) (λ nh, 0),
          pre_support := fij.pre_support.map (prod.mk i),
          zero := λ ij, begin
            by_cases (i = ij.fst),
            {
              obtain hin | h0 := fij.zero ij.snd,
              {apply or.inl, rw multiset.mem_map, use ij.snd, simp only [hin, h, prod.mk.eta, eq_self_iff_true, and_self] },
              {
                apply or.inr,
                simp only [],
                split_ifs with heq,
                {simp [h0], induction heq, refl},
                {refl},
              }
            },
            {
              apply or.inr,
              simp only [],
              split_ifs,
              exfalso, exact h h_1.symm,
              refl,
            }
          end,
        }⟧,
      end,
      exact λ a b H, quotient.sound $ λ ij, begin
        simp [H],
        split_ifs,
        rw H, refl,
      end,
    end),
    -- I don't know whether I can actual build something useful out of this multiset of functions now...
    sorry,
  },
  -- this can't be filled in until the above sorry is
  exact λ a b H, sorry,
end

lemma is_right_inverse  (f : Π₀ i j, β i j) : curry(uncurry(f)) = f := begin
  unfold curry uncurry,
  simp,
  -- irrelevant until `uncurry` is fixed
  sorry
end

lemma is_left_inverse (f : Π₀ (ij : ι₁ × ι₂), β ij.1 ij.2) : uncurry(curry(f)) = f := begin
  unfold curry uncurry,
  simp,
  -- irrelevant until `uncurry` is fixed
  sorry
end

-- the sole purpose of this file
def eqv : (Π₀ (ij : ι₁ × ι₂), β ij.1 ij.2) ≃ (Π₀ i j, β i j) := {
  to_fun := curry,
  inv_fun := uncurry,
  left_inv := is_left_inverse,
  right_inv := is_right_inverse }

end dfinsupp.prod
