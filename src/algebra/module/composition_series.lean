import order.jordan_holder
import order.cover
import ring_theory.simple_module

namespace composition_series

-- TODO
instance temp {α : Type*} [lattice α] [is_modular_lattice α] : is_weak_lower_modular_lattice α := sorry

open submodule
open lattice
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

@[simp]
lemma comap_map_subtype (B : submodule R M) (A : submodule R B) :
  comap B.subtype (map B.subtype A) = A :=
comap_map_eq_of_injective subtype.coe_injective A

lemma covby_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  A ⋖ B ↔ is_simple_module R (B ⧸ comap B.subtype A) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h,
  { split,
    { intro htop,
      rw comap_subtype_eq_top at htop,
      rw le_antisymm hAB htop at h,
      exact lt_irrefl B h.lt },
    { intros C' hAC',
      have hA : A = map B.subtype (comap B.subtype A),
        rwa [map_comap_subtype,right_eq_inf],
      have hAC : A ≤ map B.subtype C',
      { rw hA,
        exact map_mono (le_of_lt hAC') },
      cases h.wcovby.eq_or_eq hAC (map_subtype_le B C') with h h,
      { exfalso,
        apply ne_of_lt hAC',
        rw congr_arg (comap B.subtype) h.symm,
        exact comap_map_subtype B C' },
      { rw [←comap_map_subtype B C', h, comap_subtype_self] } } },
  { rw covby_iff_lt_and_eq_or_eq,
    split,
    { apply lt_of_le_of_ne hAB,
      intro hAB',
      apply h.1,
      rw hAB',
      exact comap_subtype_self B },
    { intros C hAC hCB,
      by_cases u : comap B.subtype A < comap B.subtype C,
      { right,
        exact le_antisymm hCB (comap_subtype_eq_top.mp $ h.2 _ u) },
      { left,
        have eqAC := eq_of_le_of_not_lt (comap_mono hAC) u,
        rw [right_eq_inf.mpr hAB, right_eq_inf.mpr hCB, ←map_comap_subtype, ←eqAC, map_comap_subtype] } } }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) :=
{ is_maximal                            := (⋖),
  lt_of_is_maximal                      := λ x y, covby.lt,
  sup_eq_of_is_maximal                  := λ x y z hxz hyz, wcovby.sup_eq hxz.wcovby hyz.wcovby,
  is_maximal_inf_left_of_is_maximal_sup := λ A B, inf_covby_of_covby_sup_of_covby_sup_left,
  iso                                   := λ X Y,
    nonempty $ (X.2 ⧸ comap X.2.subtype X.1) ≃ₗ[R] (Y.2 ⧸ comap Y.2.subtype Y.1),
  iso_symm                              := λ A B ⟨f⟩, ⟨f.symm⟩,
  iso_trans                             := λ A B C ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  second_iso                            := λ A B h, ⟨by {
    rw [sup_comm,inf_comm],
    exact (linear_map.quotient_inf_equiv_sup_quotient B A).symm }⟩ }

end composition_series
