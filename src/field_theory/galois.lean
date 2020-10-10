import field_theory.normal
import field_theory.primitive_element

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

@[class] def is_galois : Prop := is_separable F E ∧ normal F E

lemma galois.exists_is_splitting_field [finite_dimensional F E] (h : is_galois F E) :
  ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E :=
begin
  cases field.exists_primitive_element h.1 with α h1,
  cases h.1 α with h2 h3,
  cases h.2 α with h4 h5,
  use minimal_polynomial h2,
  split,
  exact h3,
  split,
  exact h5,
  sorry,--this will get easier after the PR
end
