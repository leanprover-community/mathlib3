import data.W.cardinal
import ring_theory.algebraic_independent
import field_theory.algebraic_closure
import algebra.char_p.algebra

open cardinal

universe u

inductive mv_polynomial_fun (R σ : Type u) : Type u
| of_ring : R → mv_polynomial_fun
| X : σ → mv_polynomial_fun
| mul : mv_polynomial_fun
| add : mv_polynomial_fun

open mv_polynomial_fun

variables {R σ : Type u}

namespace mv_polynomial_fun

@[simp] def mv_polynomial_fun_to_sum : mv_polynomial_fun R σ → R ⊕ σ ⊕ ulift.{u} bool
| (of_ring x) := sum.inl x
| (X i) := sum.inr (sum.inl i)
| mul := sum.inr (sum.inr ⟨tt⟩)
| add := sum.inr (sum.inr ⟨ff⟩)
#print cardinal.add
lemma cardinal_mk_mv_polynomial_fun :
  cardinal.mk (mv_polynomial_fun R σ) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial_fun R σ) ≤ #R + #σ + cardinal.lift (#bool) :
  begin
    rw [add_assoc],
    simp only [cardinal.add_def, cardinal.lift_mk, cardinal.le_def],
    refine ⟨⟨mv_polynomial_fun_to_sum, _⟩⟩,
    intros x y,
    induction x; induction y; simp [ulift.ext_iff]
  end
... ≤ _ : begin


end



@[simp] def arity : mv_polynomial_fun R σ → Type u
| (of_ring _) := pempty
| (X _) := pempty
| mul := ulift bool
| add := ulift bool

instance arity_fintype (x : mv_polynomial_fun R σ) : fintype x.arity :=
by cases x; dsimp; apply_instance

variables [comm_semiring R]

@[simp] noncomputable def to_mv_polynomial :
  W_type (@mv_polynomial_fun.arity R σ) → mv_polynomial σ R
| ⟨of_ring r, _⟩ := mv_polynomial.C r
| ⟨X i, _⟩       := mv_polynomial.X i
| ⟨mul, f⟩       := to_mv_polynomial (f (ulift.up ff)) * to_mv_polynomial (f (ulift.up tt))
| ⟨add, f⟩       := to_mv_polynomial (f (ulift.up tt)) + to_mv_polynomial (f (ulift.up ff))

lemma to_mv_polynomial_surjective : function.surjective (@to_mv_polynomial R σ _) :=
begin
  intro p,
  induction p using mv_polynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih,
  { exact ⟨W_type.mk (of_ring x) pempty.elim, rfl⟩ },
  { rcases ih₁ with ⟨w₁, rfl⟩,
    rcases ih₂ with ⟨w₂, rfl⟩,
    exact ⟨W_type.mk add (λ x, cond x.down w₁ w₂), by dsimp; refl⟩ },
  { rcases ih with ⟨w, rfl⟩,
    exact ⟨W_type.mk mul (λ x, cond x.down (W_type.mk (X i) pempty.elim) w), by dsimp; refl⟩ }
end

end mv_polynomial_fun

lemma cardinal_mk_mv_polynomial {R σ : Type u} [comm_semiring R] :
  #(mv_polynomial σ R) = max (max (#R) (#σ)) ω :=
let β : σ ⊕ R ⊕ bool ⊕ bool ⊕ unit → Type :=
