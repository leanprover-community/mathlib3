/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import topology.sheaves.sheaf
import topology.sheaves.sheaf_condition.opens_le_cover

/-!
# Presheaves on punit

Presheaves on punit satisfy sheaf condition iff its value at empty set is a terminal object.
-/

namespace category_theory

open Top topological_space category_theory.limits opposite

universes u v w

variables {C : Type u} [category.{v} C]
variables [Π (U : opens (Top.of (punit : Type w))), decidable (punit.star ∈ U)]

lemma presheaf_on_punit_is_sheaf_of_is_terminal (F : presheaf C (Top.of (punit : Type w)))
  (it : is_terminal $ F.obj $ op ⊥) : F.is_sheaf := λ c U s hs,
begin
  by_cases h : punit.star ∈ U,
  { convert presieve.is_sheaf_for_top_sieve _, rw ←sieve.id_mem_iff_eq_top,
    refine s.downward_closed (hs punit.star h).some_spec.some_spec.1 (eq_to_hom _),
    ext, rcases x, rw [opens.mem_coe, opens.mem_coe],
    exact ⟨λ _, (hs punit.star h).some_spec.some_spec.2, λ _, h⟩, },
  { intros α hα,
    have it' : is_terminal (F.obj $ op U),
    { convert it, ext, cases x, rw [opens.mem_coe, opens.mem_coe],
      split; intros H; contrapose! H, assumption, exact set.not_mem_empty punit.star, },
    refine ⟨it'.from _, λ V i hi, (_ : is_terminal (F.obj (op V))).hom_ext _ _,
      λ _ _, (it'.hom_ext _ _).symm⟩,
    convert it, ext, rcases x, rw [opens.mem_coe, opens.mem_coe],
    split; intros H; contrapose! H, exact λ r, h (le_of_hom i r),
    exact set.not_mem_empty punit.star, },
end

lemma presheaf_on_punit_is_sheaf_iff_is_terminal (F : presheaf C (Top.of (punit : Type w))) :
  F.is_sheaf ↔ nonempty (is_terminal (F.obj (op ⊥))) :=
⟨λ h, nonempty.intro begin
  convert Sheaf.is_terminal_of_bot_cover ⟨F, h⟩ ⊥ _,
  rintros ⟨⟩ h, contrapose! h, exact set.not_mem_empty punit.star,
end, λ ⟨it⟩, presheaf_on_punit_is_sheaf_of_is_terminal F it⟩

end category_theory
