import group_theory.quotient_group
import algebra.category.Group.abelian

open_locale classical pointwise

section
variables (G : Type*) [group G] (N : subgroup G) [nN : N.normal]

@[to_additive add_mk_surjective]
lemma mk_surjective : function.surjective (@quotient_group.mk G _ N) :=
by apply quotient.surjective_quotient_mk'
end

section

variables (G : Type*) [add_comm_group G]

lemma mem_smul (m : ℕ) (N : add_subgroup G) {a : G} :
 a ∈ m • (⊤ : add_subgroup G) ↔ ∃ a' : G, a = m • a' :=
begin
  split; intro ha,
  rcases ha with ⟨a', h1, h2⟩,
  use a', rw ←h2, refl,

  obtain ⟨a', h⟩ := ha,
  use a', split, simp only [add_subgroup.coe_top], rw h, refl,
end

end
