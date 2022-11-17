import order.jordan_holder
import order.cover
import ring_theory.simple_module

namespace composition_series

open set

lemma covby_iff_coatom_Iic {α : Type*} [partial_order α] {x y : α} (hxy : x ≤ y):
  x ⋖ y ↔ is_coatom (⟨x, hxy⟩ : Iic y) :=
begin
  let f : Iic y ↪o α := order_embedding.subtype (λ z, z ≤ y),
  rw ←covby_top_iff,
  refine ⟨λ h, covby.of_image f h, λ h, covby.image f h _⟩,
  change (range coe).ord_connected,
  rw subtype.range_coe,
  exact ord_connected_Iic,
end

open submodule
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

lemma covby_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  A ⋖ B ↔ is_simple_module R (B ⧸ comap B.subtype A) :=
begin
  let f : submodule R B ≃o Iic B := map_subtype.rel_iso B,
  rw [covby_iff_coatom_Iic hAB, is_simple_module_iff_is_coatom, ←order_iso.is_coatom_iff f _],
  refine iff_of_eq (congr_arg _ _),
  change (⟨A, _⟩ : Iic B) = ⟨map B.subtype (comap B.subtype A), _⟩,
  rw [subtype.mk_eq_mk, map_comap_subtype, inf_eq_right.mpr hAB],
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
