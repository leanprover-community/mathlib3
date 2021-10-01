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
| 0 := ⟨empty, default _⟩
| 1 := ⟨unit,
  { step := λ _ _, univ,
    start := univ,
    accept := univ }⟩
| (char a) := ⟨option unit,
  { step := λ s b, if (a ∈ b ∧ s = none) then {some ()} else ∅,
    start := univ,
    accept := univ }⟩
| (P + Q) := ⟨P.to_ε_NFA.1 × Q.to_ε_NFA.1,
      { step := λ s a, (P.to_ε_NFA.2.step s.1 a).prod (Q.to_ε_NFA.2.step s.2 a),
        start := P.to_ε_NFA.2.start.prod Q.to_ε_NFA.2.start,
        accept := {ab | ab.1 ∈ P.to_ε_NFA.2.accept ∨ ab.2 ∈ Q.to_ε_NFA.2.accept} }⟩
| (P * Q) := begin
    obtain ⟨σ_P, NFA_P⟩ := regular_expression.to_ε_NFA P,
    obtain ⟨σ_Q, NFA_Q⟩ := regular_expression.to_ε_NFA Q,
    exact ⟨σ_P × σ_Q,
      { step := λ s a, (NFA_P.step s.1 a).prod (NFA_Q.step s.2 a),
        start := NFA_P.start.prod NFA_Q.start,
        accept := NFA_P.accept.prod NFA_Q.accept }⟩,
  end
| (star P) := begin
    obtain ⟨σ_P, NFA_P⟩ := regular_expression.to_ε_NFA P,
    exact ⟨option σ_P,
      { step := λ s a, match s with
          | none := match a with
            | none := coe '' NFA_P.start
            | (some a) := ∅
            end
          | (some s) :=  match a with
            | none := (coe '' NFA_P.step s none) ∪ (if (s ∈ NFA_P.accept) then {none} else ∅)
            | (some a) := coe '' NFA_P.step s a
            end
          end,
        start := {none},
        accept := {none} }⟩,
end

lemma regular_expression.to_ε_NFA_correct :
  ∀ (P : regular_expression α), P.to_ε_NFA.2.accepts = P.matches
| 0 := begin
    change ε_NFA.accepts (default _) = _,
    simp,
    sorry
  end
| 1 := begin
    change ε_NFA.accepts ({ step := λ _ _, univ,
    start := univ,
    accept := univ }) = _,
    sorry,
  end
| (char a) := sorry
| (P + Q) := begin
    rw [matches_add_def, ←P.to_ε_NFA_correct, ←Q.to_ε_NFA_correct],
    change ε_NFA.accepts ({ step := λ s a, (P.to_ε_NFA.2.step s.1 a).prod (Q.to_ε_NFA.2.step s.2 a),
        start := P.to_ε_NFA.2.start.prod Q.to_ε_NFA.2.start,
        accept := {ab | ab.1 ∈ P.to_ε_NFA.2.accept ∨ ab.2 ∈ Q.to_ε_NFA.2.accept} } : ε_NFA
        α (P.to_ε_NFA.1 × Q.to_ε_NFA.1)) = _,
    unfold ε_NFA.accepts,
    simp,
  end
| (P * Q) := sorry
| (star P) := sorry
