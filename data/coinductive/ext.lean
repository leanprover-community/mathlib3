
import data.coinductive.basic
       data.coinductive.subtree

universes u₀ u₁ u₂ v w

local prefix `♯`:0 := cast (by casesm* _ ∧ _ ; simp [*] <|> cc <|> solve_by_elim)
namespace coinduction.approx
open nat coinduction.subtree

variables {ι : Type u₁}
variables {α : ι → Type u₀}
variables {β : Π i, α i → Type u₂}
variables (γ : Π i (a : α i), β i a → ι)

lemma ext_aux {i : ι} {n : ℕ} (x y : cofix_a γ i (succ n)) (z : cofix_a γ i n)
  (hx : agree z x)
  (hy : agree z y)
  (hrec : ∀ (ps : path β) (_ : n = ps.length)
            {j : ι} (x' y' : α j),
             (select' x ps x') →
             (select' y ps y') →
            x' = y')
: x = y :=
begin
  induction n with n generalizing i x y,
  { cases x, cases y, cases z, cases hx,
    have : x_a = y_a,
    { apply hrec []; constructor; refl, },
    subst this, congr, },
  { cases hx, cases hy, congr, ext,
    apply n_ih, apply hx_a, apply hy_a,
    intros, apply hrec (⟨_,_,x⟩ :: ps);
      try { constructor; assumption <|> refl },
    simp [_x,one_add] }
end

end coinduction.approx
