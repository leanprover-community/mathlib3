#exit
import category_theory.abelian.injective
import category_theory.abelian.ext
import category_theory.limits.preserves.opposites
universes v u
noncomputable theory
open category_theory category_theory.limits
open_locale zero_object
namespace category_theory
section
variables {C : Type u} [category C] {D : Type v} [category D]
  [abelian C] [enough_projectives C] [abelian D]
  (F : C ⥤ D) [functor.additive F] [preserves_finite_limits F]
  [preserves_finite_colimits F] (n : ℕ) (X : C)

def functor.left_derived_succ_of_exact (n : ℕ) (X : C) :
  (F.left_derived (n + 1)).obj X ≅ 0 :=
F.left_derived_obj_iso (n + 1) (ProjectiveResolution.of X) ≪≫ (F.homology_iso
  (ProjectiveResolution.of X).complex (n + 1)).symm ≪≫ F.map_iso
  ((ProjectiveResolution.of X).complex.homology_succ_iso n ≪≫ @cokernel.of_epi _ _ _ _
  _ _ _ _ ((ProjectiveResolution.of X).exact n).epi) ≪≫ F.map_zero_object

end
variables {C : Type u} [category.{u} C] [abelian C] (I : C) [injective I] (R : Type u) [comm_ring R]
  [linear R C] [enough_projectives C] (n : ℕ)

instance preserves_limits_linear_yoneda_obj (X : C) :
  preserves_limits ((linear_yoneda R C).obj X) :=
have preserves_limits ((linear_yoneda R C).obj X ⋙ forget _),
  from (infer_instance : preserves_limits (yoneda.obj X)),
by exactI preserves_limits_of_reflects_of_preserves _ (forget _)

instance preserves_epis_linear_yoneda_obj_of_injective :
  ((linear_yoneda R C).obj I).preserves_epimorphisms :=
begin
  refine @functor.preserves_epimorphisms_of_preserves_of_reflects _ _ _ _ _ _
    ((linear_yoneda R C).obj I) (forget _)
    (by {show functor.preserves_epimorphisms (yoneda.obj I),
    exact (injective.injective_iff_preserves_epimorphisms_yoneda_obj I).1 infer_instance}) _,
end

instance : preserves_finite_colimits ((linear_yoneda R C).obj I) :=
functor.preserves_finite_colimits_of_preserves_epis_and_kernels _
instance : preserves_finite_colimits ((linear_yoneda R C).obj I).right_op :=
preserves_finite_colimits_right_op ((linear_yoneda R C).obj I)
instance : preserves_finite_limits  ((linear_yoneda R C).obj I).right_op :=
preserves_finite_limits_right_op ((linear_yoneda R C).obj I)

def Ext_succ_of_injective (n : ℕ) (X : Cᵒᵖ) : ((Ext R C (n + 1)).obj X).obj I ≅ 0 :=
by apply (((linear_yoneda R C).obj I).right_op.left_derived_succ_of_exact n
  (opposite.unop X)).symm.unop ≪≫ is_zero.iso (is_zero.unop $ is_zero_zero _) (is_zero_zero _)

end category_theory
