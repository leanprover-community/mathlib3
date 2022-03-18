import category_theory.abelian.injective_resolution
import algebra.homology.additive

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C] {D : Type*} [category D]
variables [abelian C] [has_injective_resolutions C] [abelian D]

def functor.right_derived (F : C ⥤ D) [F.additive] (n : ℕ) : C ⥤ D :=
injective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

@[simps]
def functor.right_derived_obj_iso (F : C ⥤ D) [F.additive] (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (F.right_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.cocomplex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (InjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

@[simps]
def functor.right_derived_obj_projective_zero (F : C ⥤ D) [F.additive]
  (X : C) [injective X] :
  (F.right_derived 0).obj X ≅ F.obj X :=
F.right_derived_obj_iso 0 (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_0_single₀ D).app (F.obj X)

open_locale zero_object

/-- The higher derived functors vanish on projective objects. -/
@[simps]
def functor.right_derived_obj_injective_succ (F : C ⥤ D) [F.additive] (n : ℕ)
  (X : C) [injective X] :
  (F.right_derived (n+1)).obj X ≅ 0 :=
F.right_derived_obj_iso (n+1) (InjectiveResolution.self X) ≪≫
  (homology_functor _ _ _).map_iso ((cochain_complex.single₀_map_homological_complex F).app X) ≪≫
  (cochain_complex.homology_functor_succ_single₀ D n).app (F.obj X)

lemma functor.right_derived_map_eq (F : C ⥤ D) [F.additive] (n : ℕ) {X Y : C} (f : Y ⟶ X)
  {P : InjectiveResolution X} {Q : InjectiveResolution Y} (g : Q.cocomplex ⟶ P.cocomplex)
  (w : Q.ι ≫ g = (cochain_complex.single₀ C).map f ≫ P.ι) :
  (F.right_derived n).map f =
  (F.right_derived_obj_iso n Q).hom ≫
  (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
  (F.right_derived_obj_iso n P).inv :=
begin
  dsimp only [functor.right_derived, functor.right_derived_obj_iso],
  dsimp, simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  apply functor.map_homotopy,
  apply homotopy.trans,
  exact homotopy_category.homotopy_out_map _,
  apply InjectiveResolution.desc_homotopy f,
  { simp, },
  { simp only [InjectiveResolution.homotopy_equiv_hom_π_assoc],
    rw [←category.assoc, w, category.assoc],
    simp only [InjectiveResolution.homotopy_equiv_inv_π], },
end

@[simps]
def nat_trans.right_derived {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ) :
  F.right_derived n ⟶ G.right_derived n :=
whisker_left (injective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

@[simp] lemma nat_trans.right_derived_id (F : C ⥤ D) [F.additive] (n : ℕ) :
  nat_trans.right_derived (𝟙 F) n = 𝟙 (F.right_derived n) :=
by { simp [nat_trans.right_derived], refl, }

@[simp, nolint simp_nf] lemma nat_trans.left_derived_comp
  {F G H : C ⥤ D} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H) (n : ℕ) :
  nat_trans.right_derived (α ≫ β) n = nat_trans.right_derived α n ≫ nat_trans.right_derived β n :=
by simp [nat_trans.right_derived]

lemma nat_trans.left_derived_eq {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) (n : ℕ)
  {X : C} (P : InjectiveResolution X) :
  (nat_trans.right_derived α n).app X =
    (F.right_derived_obj_iso n P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.cocomplex) ≫
        (G.right_derived_obj_iso n P).inv :=
begin
  symmetry,
  dsimp [nat_trans.right_derived, functor.right_derived_obj_iso],
  simp only [category.comp_id, category.id_comp],
  rw [←homology_functor_map, homotopy_category.homology_functor_map_factors],
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
  simp only [nat_trans.map_homological_complex_naturality_assoc,
    ←functor.map_comp],
  apply homotopy.comp_left_id,
  rw [←functor.map_id],
  apply functor.map_homotopy,
  apply homotopy_equiv.homotopy_hom_inv_id,
end

end category_theory
