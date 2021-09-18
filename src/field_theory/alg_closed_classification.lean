import data.W.cardinal
import ring_theory.algebraic_independent
import field_theory.algebraic_closure
import algebra.char_p.algebra

open cardinal
open_locale cardinal

universe u

section mv_polynomial

def mv_polynomial_fun (R σ : Type u) : Type u :=
R ⊕ σ ⊕ ulift.{u} bool

variables {R σ : Type u}

namespace mv_polynomial_fun

@[simp] def arity : mv_polynomial_fun R σ → Type u
| (sum.inl _)              := pempty
| (sum.inr (sum.inl _))    := pempty
| (sum.inr (sum.inr ⟨ff⟩)) := ulift bool
| (sum.inr (sum.inr ⟨tt⟩)) := ulift bool

instance arity_fintype (x : mv_polynomial_fun R σ) : fintype x.arity :=
by rcases x with x | x | ⟨_ | _⟩; dsimp; apply_instance

variables [comm_semiring R]

@[simp] noncomputable def to_mv_polynomial :
  W_type (@mv_polynomial_fun.arity R σ) → mv_polynomial σ R
| ⟨sum.inl r, _⟩              := mv_polynomial.C r
| ⟨sum.inr (sum.inl i), _⟩    := mv_polynomial.X i
| ⟨sum.inr (sum.inr ⟨ff⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) * to_mv_polynomial (f (ulift.up ff))
| ⟨sum.inr (sum.inr ⟨tt⟩), f⟩ :=
  to_mv_polynomial (f (ulift.up tt)) + to_mv_polynomial (f (ulift.up ff))

lemma to_mv_polynomial_surjective : function.surjective (@to_mv_polynomial R σ _) :=
begin
  intro p,
  induction p using mv_polynomial.induction_on with x p₁ p₂ ih₁ ih₂ p i ih,
  { exact ⟨W_type.mk (sum.inl x) pempty.elim, rfl⟩ },
  { rcases ih₁ with ⟨w₁, rfl⟩,
    rcases ih₂ with ⟨w₂, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨tt⟩)) (λ x, cond x.down w₁ w₂), by simp⟩ },
  { rcases ih with ⟨w, rfl⟩,
    exact ⟨W_type.mk (sum.inr (sum.inr ⟨ff⟩)) (λ x, cond x.down w (W_type.mk
      (sum.inr (sum.inl i)) pempty.elim)), by simp⟩ }
end

lemma cardinal_mv_polynomial_fun_le : #(mv_polynomial_fun R σ) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial_fun R σ) = #R + #σ + #(ulift bool) :
  by delta mv_polynomial_fun; simp only [← add_def, add_assoc]
... ≤ max (max (#R + #σ) (#(ulift bool))) ω : add_le_max _ _
... ≤ max (max (max (max (#R) (#σ)) ω) (#(ulift bool))) ω :
  max_le_max (max_le_max (add_le_max _ _) (le_refl _)) (le_refl _)
... ≤ _ : begin
  have : #(ulift.{u} bool) ≤ ω,
    from le_of_lt (lt_omega_iff_fintype.2 ⟨infer_instance⟩),
  simp only [max_comm omega.{u}, max_assoc, max_left_comm omega.{u}, max_self, max_eq_left this],
end

end mv_polynomial_fun

open mv_polynomial_fun

namespace mv_polynomial

lemma cardinal_mk_le_max {R σ : Type u} [comm_semiring R] :
  #(mv_polynomial σ R) ≤ max (max (#R) (#σ)) ω :=
calc #(mv_polynomial σ R) ≤ #(W_type (@mv_polynomial_fun.arity R σ)) :
  cardinal.mk_le_of_surjective to_mv_polynomial_surjective
... ≤ max (#(mv_polynomial_fun R σ)) ω : W_type.cardinal_mk_le_max_omega_of_fintype
... ≤ _ : max_le_max cardinal_mv_polynomial_fun_le (le_refl _)
... ≤ _ : by simp only [max_assoc, max_self]

end mv_polynomial

end mv_polynomial

section field_of_fractions



end field_of_fractions
