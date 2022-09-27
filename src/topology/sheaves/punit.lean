import topology.sheaves.sheaf
import topology.sheaves.sheaf_condition.opens_le_cover

namespace category_theory

open Top topological_space category_theory.limits opposite

universes u v w

variables {C : Type u} [category.{v} C]
variables [Π (U : opens (Top.of (punit : Type w))), decidable (punit.star ∈ U)]

lemma presheaf_on_unit_is_sheaf_of_is_terminal (F : presheaf C (Top.of (punit : Type w)))
  (it: is_terminal $ F.obj $ op ⊥) : F.is_sheaf := λ c U s hs,
begin
  by_cases h : punit.star ∈ U,
  { have H : s (𝟙 U),
    { apply s.downward_closed, exact (hs punit.star h).some_spec.some_spec.1,
      refine eq_to_hom _, ext, rcases x, rw [opens.mem_coe, opens.mem_coe],
      exact ⟨λ _, (hs punit.star h).some_spec.some_spec.2, λ _, h⟩, },
    have s_top : s = ⊤ := sieve.id_mem_iff_eq_top.mp H,
    rw s_top, exact presieve.is_sheaf_for_top_sieve _, },
  { intros α hα,
    have it' : is_terminal (F.obj $ op U),
    { convert it, ext, cases x, rw [opens.mem_coe, opens.mem_coe],
      split; intros H; contrapose! H, assumption, exact set.not_mem_empty punit.star, },
    refine ⟨it'.from _, _, λ _ _, (it'.hom_ext _ _).symm⟩,
    intros V i hi,
    have it'' : is_terminal (F.obj (op V)),
    { convert it,
      ext, rcases x, rw [opens.mem_coe, opens.mem_coe],
      split; intros H; contrapose! H,
      exact λ r, h (le_of_hom i r),
      exact set.not_mem_empty punit.star, },
    exact it''.hom_ext _ _, },
end

end category_theory
