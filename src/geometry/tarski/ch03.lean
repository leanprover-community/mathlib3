import geometry.tarski.ch02

variables {α : Type*} [tarski α]
variables {A B C D E F A' B' C' P Q X Y : α}

namespace tarski

lemma betw.id_right (A B : α) : betw A B B :=
begin
  obtain ⟨E, hE₁, hE₂⟩ := segment_construction A B B B,
  cases hE₂.identity,
  apply hE₁
end

lemma betw.symm (h : betw A B C) : betw C B A :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h (betw.id_right B C),
  cases hx₁.identity,
  apply hx₂
end

lemma betw.id_left (A B : α) : betw A A B := (betw.id_right _ _).symm

lemma betw.antisymm_left (h₁ : betw A B C) (h₂ : betw B A C) : A = B :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h₁ h₂,
  cases hx₁.identity,
  apply hx₂.identity,
end

lemma betw.antisymm_right (h₁ : betw A B C) (h₂ : betw A C B) : B = C :=
h₂.symm.antisymm_left h₁.symm

-- between_exchange3
lemma betw.left_cancel (h₁ : betw A B C) (h₂ : betw A C D) : betw B C D :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h₂.symm h₁.symm,
  cases hx₁.identity,
  apply hx₂,
end

-- between_inner_transitivity
lemma betw.right_cancel (h₁ : betw A B D) (h₂ : betw B C D) : betw A B C :=
(h₂.symm.left_cancel h₁.symm).symm

-- outer_transitivity_between2
lemma betw.trans (h₁ : betw A B C) (h₂ : betw B C D) (h₃ : B ≠ C) : betw A C D :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := segment_construction A C C D,
  have : x = D := construction_uniqueness h₃ (h₁.left_cancel hx₁) hx₂ h₂ (cong.refl C D),
  cases this,
  apply hx₁
end

-- outer_transitivity_between
lemma betw.trans' (h₁ : betw A B C) (h₂ : betw B C D) (h₃ : B ≠ C) : betw A B D :=
(betw.trans h₂.symm h₁.symm h₃.symm).symm

lemma betw.right_trans (h₁ : betw A B D) (h₂ : betw B C D) : betw A C D :=
begin
  rcases eq_or_ne B C with rfl | nBC,
  { apply h₁ },
  apply betw.trans (h₁.right_cancel h₂) h₂ nBC,
end

lemma betw.left_trans (h₁ : betw A B C) (h₂ : betw A C D) : betw A B D :=
(h₂.symm.right_trans h₁.symm).symm

lemma l3_17 (h₁ : betw A B C) (h₂ : betw A' B' C) (h₃ : betw A P A') :
  ∃ Q, betw P Q C ∧ betw B Q B' :=
begin
  obtain ⟨x, hx₁, hx₂⟩ := inner_pasch h₂.symm h₃,
  obtain ⟨y, hy₁ : betw x y C, hy₂ : betw B y B'⟩ := inner_pasch hx₁ h₁.symm,
  exact ⟨y, betw.right_trans hx₂ hy₁, hy₂⟩,
end

-- 3.13
lemma two_distinct_points (α : Type*) [tarski α] : ∃ (X Y : α), X ≠ Y :=
begin
  obtain ⟨X, Y, Z, XYZ, -, -⟩ := @lower_dim α _,
  refine ⟨X, Y, _⟩,
  rintro rfl,
  apply XYZ (betw.id_left _ _),
end

-- 3.14
lemma point_construction_different (A B : α) : ∃ C, betw A B C ∧ B ≠ C :=
begin
  obtain ⟨X, Y, nXY⟩ := two_distinct_points α,
  obtain ⟨C, hC₁, hC₂⟩ := segment_construction A B X Y,
  refine ⟨_, hC₁, _⟩,
  rintro rfl,
  apply nXY (hC₂.reverse_identity),
end

lemma another_point : ∃ B, A ≠ B :=
begin
  obtain ⟨_, _, i⟩ := point_construction_different A A,
  exact ⟨_, i⟩
end

lemma betw.ne : ∀ {A B C : α}, betw A B C → A ≠ B → A ≠ C
| _ B _ b i (eq.refl A) := i b.identity

lemma betw.ne' (h : betw A B C) (nCB : C ≠ B) : A ≠ C :=
(h.symm.ne nCB).symm

end tarski
