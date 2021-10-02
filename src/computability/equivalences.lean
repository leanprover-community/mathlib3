import computability.epsilon_NFA
import computability.regular_expressions

open regular_expression set
open_locale classical

variables {α σ₁ σ₂ : Type*} [decidable_eq α]

def ε_NFA.prod (P : ε_NFA α σ₁) (Q : ε_NFA α σ₂) : ε_NFA α (σ₁ × σ₂) :=
{ step := λ s a, (P.step s.1 a).prod (Q.step s.2 a),
  start := P.start.prod Q.start,
  accept := P.accept.prod Q.accept }

lemma ε_NFA.accepts_mul (P : ε_NFA α σ₁) (Q : ε_NFA α σ₂) :
  (P.prod Q).accepts = P.accepts * Q.accepts :=
begin
  ext,
  unfold ε_NFA.prod ε_NFA.accepts,
  dsimp,
  rw language.mem_mul,
  split,
  {
    rintro ⟨s, hs, hsx⟩,
    sorry
  },
  rintro ⟨a, b, ⟨s₁, hs₁, ha⟩, ⟨s₂, hs₂, hb⟩, h⟩,
  dsimp,
end

def regular_expression.to_ε_NFA : regular_expression α → Σ σ, ε_NFA α σ
| 0 := ⟨empty, 0⟩
| 1 := ⟨unit, 1⟩
| (char a) := ⟨option unit,
  { step := λ s b, if (a ∈ b ∧ s = none) then {some ()} else ∅,
    start := univ,
    accept := univ }⟩
| (P + Q) := ⟨_, P.to_ε_NFA.2.add Q.to_ε_NFA.2⟩
| (P * Q) := ⟨_, P.to_ε_NFA.2.mul Q.to_ε_NFA.2⟩
| (star P') := begin
    obtain ⟨σ, P⟩ := P'.to_ε_NFA,
    have := P.star,
    exact ⟨option σ, P.star,⟩,
end

lemma regular_expression.to_ε_NFA_correct :
  ∀ (P : regular_expression α), P.to_ε_NFA.2.accepts = P.matches
| 0 := ε_NFA.accepts_zero
| 1 := ε_NFA.accepts_one
| (char a) := sorry
| (P + Q) := begin
    rw [matches_add_def, ←P.to_ε_NFA_correct, ←Q.to_ε_NFA_correct],
    exact ε_NFA.accepts_add _ _,
  end
| (P * Q) := begin
    rw [matches_mul_def, ←P.to_ε_NFA_correct, ←Q.to_ε_NFA_correct],
    exact ε_NFA.accepts_mul _ _,
  end
| (star P) := begin
    rw [matches_star_def, ←P.to_ε_NFA_correct],
    exact ε_NFA.accepts_star _,
  end
