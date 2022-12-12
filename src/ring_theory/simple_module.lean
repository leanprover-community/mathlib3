/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import linear_algebra.isomorphisms
import order.jordan_holder

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `is_semisimple_module` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/

variables (R : Type*) [ring R] (M : Type*) [add_comm_group M] [module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbreviation is_simple_module := (is_simple_order (submodule R M))

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbreviation is_semisimple_module := (complemented_lattice (submodule R M))

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem is_simple_module.nontrivial [is_simple_module R M] : nontrivial M :=
⟨⟨0, begin
  have h : (⊥ : submodule R M) ≠ ⊤ := bot_ne_top,
  contrapose! h,
  ext,
  simp [submodule.mem_bot,submodule.mem_top, h x],
end⟩⟩

variables {R} {M} {m : submodule R M} {N : Type*} [add_comm_group N] [module R N]

lemma is_simple_module.congr (l : M ≃ₗ[R] N) [is_simple_module R N] : is_simple_module R M :=
(submodule.order_iso_map_comap l).is_simple_order

theorem is_simple_module_iff_is_atom :
  is_simple_module R m ↔ is_atom m :=
begin
  rw ← set.is_simple_order_Iic_iff_is_atom,
  apply order_iso.is_simple_order_iff,
  exact submodule.map_subtype.rel_iso m,
end

theorem is_simple_module_iff_is_coatom :
  is_simple_module R (M ⧸ m) ↔ is_coatom m :=
begin
  rw ← set.is_simple_order_Ici_iff_is_coatom,
  apply order_iso.is_simple_order_iff,
  exact submodule.comap_mkq.rel_iso m,
end

theorem covby_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  A ⋖ B ↔ is_simple_module R (B ⧸ submodule.comap B.subtype A) :=
begin
  set f : submodule R B ≃o set.Iic B := submodule.map_subtype.rel_iso B with hf,
  rw [covby_iff_coatom_Iic hAB, is_simple_module_iff_is_coatom, ←order_iso.is_coatom_iff f, hf],
  simp [-order_iso.is_coatom_iff, submodule.map_subtype.rel_iso, submodule.map_comap_subtype,
    inf_eq_right.2 hAB],
end

namespace is_simple_module

variable [hm : is_simple_module R m]

@[simp]
lemma is_atom : is_atom m := is_simple_module_iff_is_atom.1 hm

end is_simple_module

theorem is_semisimple_of_Sup_simples_eq_top
  (h : Sup {m : submodule R M | is_simple_module R m} = ⊤) :
  is_semisimple_module R M :=
complemented_lattice_of_Sup_atoms_eq_top (by simp_rw [← h, is_simple_module_iff_is_atom])

namespace is_semisimple_module

variable [is_semisimple_module R M]

theorem Sup_simples_eq_top : Sup {m : submodule R M | is_simple_module R m} = ⊤ :=
begin
  simp_rw is_simple_module_iff_is_atom,
  exact Sup_atoms_eq_top,
end

instance is_semisimple_submodule {m : submodule R M} : is_semisimple_module R m :=
begin
  have f : submodule R m ≃o set.Iic m := submodule.map_subtype.rel_iso m,
  exact f.complemented_lattice_iff.2 is_modular_lattice.complemented_lattice_Iic,
end

end is_semisimple_module

theorem is_semisimple_iff_top_eq_Sup_simples :
  Sup {m : submodule R M | is_simple_module R m} = ⊤ ↔ is_semisimple_module R M :=
⟨is_semisimple_of_Sup_simples_eq_top, by { introI, exact is_semisimple_module.Sup_simples_eq_top }⟩

namespace linear_map

theorem injective_or_eq_zero [is_simple_module R M] (f : M →ₗ[R] N) :
  function.injective f ∨ f = 0 :=
begin
  rw [← ker_eq_bot, ← ker_eq_top],
  apply eq_bot_or_eq_top,
end

theorem injective_of_ne_zero [is_simple_module R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
  function.injective f :=
f.injective_or_eq_zero.resolve_right h

theorem surjective_or_eq_zero [is_simple_module R N] (f : M →ₗ[R] N) :
  function.surjective f ∨ f = 0 :=
begin
  rw [← range_eq_top, ← range_eq_bot, or_comm],
  apply eq_bot_or_eq_top,
end

theorem surjective_of_ne_zero [is_simple_module R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
  function.surjective f :=
f.surjective_or_eq_zero.resolve_right h

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [is_simple_module R M] [is_simple_module R N]
  (f : M →ₗ[R] N) :
  function.bijective f ∨ f = 0 :=
begin
  by_cases h : f = 0,
  { right,
    exact h },
  exact or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩,
end

theorem bijective_of_ne_zero [is_simple_module R M] [is_simple_module R N]
  {f : M →ₗ[R] N} (h : f ≠ 0):
  function.bijective f :=
f.bijective_or_eq_zero.resolve_right h

theorem is_coatom_ker_of_surjective [is_simple_module R N] {f : M →ₗ[R] N}
  (hf : function.surjective f) : is_coatom f.ker :=
begin
  rw ←is_simple_module_iff_is_coatom,
  exact is_simple_module.congr (f.quot_ker_equiv_of_surjective hf)
end

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance _root_.module.End.division_ring
  [decidable_eq (module.End R M)] [is_simple_module R M] :
  division_ring (module.End R M) :=
{ inv := λ f, if h : f = 0 then 0 else (linear_map.inverse f
    (equiv.of_bijective _ (bijective_of_ne_zero h)).inv_fun
    (equiv.of_bijective _ (bijective_of_ne_zero h)).left_inv
    (equiv.of_bijective _ (bijective_of_ne_zero h)).right_inv),
  exists_pair_ne := ⟨0, 1, begin
    haveI := is_simple_module.nontrivial R M,
    have h := exists_pair_ne M,
    contrapose! h,
    intros x y,
    simp_rw [ext_iff, one_apply, zero_apply] at h,
    rw [← h x, h y],
  end⟩,
  mul_inv_cancel := begin
    intros a a0,
    change (a * (dite _ _ _)) = 1,
    ext,
    rw [dif_neg a0, mul_eq_comp, one_apply, comp_apply],
    exact (equiv.of_bijective _ (bijective_of_ne_zero a0)).right_inv x,
  end,
  inv_zero := dif_pos rfl,
.. (module.End.ring : ring (module.End R M))}

end linear_map

instance jordan_holder_module : jordan_holder_lattice (submodule R M) :=
{ is_maximal                            := (⋖),
  lt_of_is_maximal                      := λ x y, covby.lt,
  sup_eq_of_is_maximal                  := λ x y z hxz hyz, wcovby.sup_eq hxz.wcovby hyz.wcovby,
  is_maximal_inf_left_of_is_maximal_sup := λ A B, inf_covby_of_covby_sup_of_covby_sup_left,
  iso                                   := λ X Y,
    nonempty $ (X.2 ⧸ X.1.comap X.2.subtype) ≃ₗ[R] Y.2 ⧸ Y.1.comap Y.2.subtype,
  iso_symm                              := λ A B ⟨f⟩, ⟨f.symm⟩,
  iso_trans                             := λ A B C ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  second_iso                            := λ A B h,
    ⟨by { rw [sup_comm, inf_comm], exact (linear_map.quotient_inf_equiv_sup_quotient B A).symm }⟩}
