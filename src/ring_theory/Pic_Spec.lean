/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import ring_theory.class_group
import algebra.category.Module.change_of_rings

universes v u u'

open_locale tensor_product

open category_theory

variables (R : Type u) [comm_ring R]

instance : has_mul (Module.{v} R) := ⟨λ M N, ⟨M ⊗[R] N⟩⟩

variable {R}

def Module.iso_equiv_linear_equiv {M N : Module.{v} R} : (M ≅ N) ≃ (M ≃ₗ[R] N) :=
{ to_fun := λ f, linear_equiv.of_linear f.hom f.inv f.inv_hom_id f.hom_inv_id,
  inv_fun := λ f,
    ⟨f, f.symm, linear_map.ext $ f.symm_apply_apply, linear_map.ext $ f.apply_symm_apply⟩,
  left_inv := λ f, iso.ext $ linear_map.ext $ λ x, rfl,
  right_inv := λ f, linear_equiv.ext $ λ x, rfl }

namespace Pic_Spec

variable (R)
def isomorphic_con : con (Module.{v} R) :=
{ to_setoid := is_isomorphic_setoid _,
  mul' := λ M N M' N' ⟨h⟩ ⟨h'⟩, begin
    refine ⟨Module.iso_equiv_linear_equiv.symm _⟩,
    apply tensor_product.congr; apply Module.iso_equiv_linear_equiv.to_fun,
    exacts [h, h'],
  end }

variable {R}
lemma isomorphic_con.eq_iff {M N : Module.{v} R} :
  (M : (isomorphic_con.{v} R).quotient) = N ↔ nonempty (M ≃ₗ[R] N) :=
(con.eq _).trans $ Module.iso_equiv_linear_equiv.nonempty_congr

variable (R)
instance : comm_monoid (isomorphic_con.{u} R).quotient :=
{ mul := (*),
  one := (⟨R⟩ : Module.{u} R),
  mul_assoc := λ M N P, con.induction_on₂ M N $ λ M N, con.induction_on P $
    λ P, isomorphic_con.eq_iff.2 ⟨tensor_product.assoc R M N P⟩,
  one_mul := λ M, con.induction_on M $ λ M, isomorphic_con.eq_iff.2 ⟨tensor_product.lid R M⟩,
  mul_one := λ M, con.induction_on M $ λ M, isomorphic_con.eq_iff.2 ⟨tensor_product.rid R M⟩,
  mul_comm := λ M N, con.induction_on₂ M N $
    λ M N, isomorphic_con.eq_iff.2 ⟨tensor_product.comm R M N⟩ }

@[derive comm_group] def _root_.Pic_Spec := units (isomorphic_con.{u} R).quotient

variables {R} {A : Type u} [comm_ring A] (f : R →+* A) --[algebra R A]

def map_monoid (f : R →+* A) : (isomorphic_con.{u} R).quotient →* (isomorphic_con.{u} A).quotient :=
{ to_fun := λ M, begin
    refine quotient.lift_on' M (λ M, ↑((Module.extend_scalars f).obj M)) _,
    rintro M N ⟨g⟩, exact quotient.sound' ⟨(Module.extend_scalars f).map_iso g⟩,
  end,
  map_one' := quotient.sound' sorry,
  map_mul' := sorry }

def map : Pic_Spec R →* Pic_Spec A := units.map $ map_monoid f

def equiv_class_group [is_domain R] : Pic_Spec R ≃* class_group R := sorry

end Pic_Spec
