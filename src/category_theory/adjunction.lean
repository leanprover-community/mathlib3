import category_theory.limits.preserves
import category_theory.whiskering
import data.equiv.basic

namespace category_theory
open category
open category_theory.limits

universes v₁ v₂ v₃ u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

structure adjunction.core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(hom_equiv_naturality_left' : Π {X' X Y} (f : X' ⟶ X) (g : F.obj X ⟶ Y),
  (hom_equiv _ _).to_fun (F.map f ≫ g) = f ≫ (hom_equiv _ _).to_fun g . obviously)
(hom_equiv_naturality_right' : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  (hom_equiv _ _).to_fun (f ≫ g) = (hom_equiv _ _).to_fun f ≫ G.map g . obviously)

namespace adjunction.core_hom_equiv

restate_axiom hom_equiv_naturality_left'
attribute [simp] hom_equiv_naturality_left
restate_axiom hom_equiv_naturality_right'

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction.core_hom_equiv F G) {X' X : C} {Y Y' : D}

lemma hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶  G.obj Y) :
  (adj.hom_equiv _ _).inv_fun (f ≫ g) = F.map f ≫ (adj.hom_equiv _ _).inv_fun g :=
begin
  conv {
    to_rhs,
    rw ← (adj.hom_equiv X' Y).left_inv (F.map f ≫ (adj.hom_equiv X Y).inv_fun g) },
  simp [(adj.hom_equiv _ _).right_inv g]
end

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶  G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv _ _).inv_fun (f ≫ G.map g) = (adj.hom_equiv _ _).inv_fun f ≫ g :=
begin
  conv {
    to_rhs,
    rw ← (adj.hom_equiv X Y').left_inv ((adj.hom_equiv X Y).inv_fun f ≫ g) },
  simp [hom_equiv_naturality_right, (adj.hom_equiv _ _).right_inv f]
end

end adjunction.core_hom_equiv

structure adjunction.core_unit_counit (F : C ⥤ D) (G : D ⥤ C) :=
(unit : functor.id C ⟹ F.comp G)
(counit : G.comp F ⟹ functor.id D)
(left_triangle' : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _ . obviously)
(right_triangle' : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _ . obviously)

namespace adjunction.core_unit_counit

restate_axiom left_triangle'
attribute [simp] left_triangle
restate_axiom right_triangle'
attribute [simp] right_triangle

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction.core_unit_counit F G)

lemma left_triangle_components {c : C} :
  F.map (adj.unit.app c) ≫ adj.counit.app (F.obj c) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ functor.id C ⋙ F), nat_trans.app t c) adj.left_triangle

lemma right_triangle_components {d : D} :
  adj.unit.app (G.obj d) ≫ G.map (adj.counit.app d) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ G ⋙ functor.id C), nat_trans.app t d) adj.right_triangle

end adjunction.core_unit_counit

/--
`adjunction F G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) extends
  (adjunction.core_hom_equiv F G), (adjunction.core_unit_counit F G) :=
(unit_hom_equiv : Π {X}, unit.app X = (hom_equiv _ _).to_fun (𝟙 (F.obj X)) . obviously)
(counit_hom_equiv : Π {Y}, counit.app Y = (hom_equiv _ _).inv_fun (𝟙 (G.obj Y)) . obviously)

namespace adjunction
variables {F : C ⥤ D} {G : D ⥤ C}

def of_core_hom_equiv (adj : core_hom_equiv F G) : adjunction F G :=
{ unit :=
  { app := λ X, (adj.hom_equiv _ _).to_fun (𝟙 (F.obj X)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left, ← adj.hom_equiv_naturality_right],
      dsimp, simp
    end },
  counit :=
  { app := λ Y, (adj.hom_equiv _ _).inv_fun (𝟙 (G.obj Y)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm],
      dsimp, simp
    end },
  left_triangle' :=
  begin
    ext1, dsimp,
    erw ←adj.hom_equiv_naturality_left_symm,
    simpa using equiv.left_inv (@core_hom_equiv.hom_equiv _ _ _ _ _ _ adj _ _) (𝟙 _)
  end,
  right_triangle' :=
  begin
    ext1, dsimp,
    erw [← adj.hom_equiv_naturality_right],
    simpa using equiv.right_inv (@core_hom_equiv.hom_equiv _ _ _ _ _ _ adj _ _) (𝟙 _)
  end,
  .. adj }

def of_core_unit_counit (adj : core_unit_counit F G) : adjunction F G :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, adj.unit.app X ≫ G.map f,
    inv_fun := λ g, F.map g ≫ adj.counit.app Y,
    left_inv := λ f, begin
      change F.map (_ ≫ _) ≫ _ = _,
      rw [F.map_comp, assoc, ←functor.comp_map, adj.counit.naturality, ←assoc],
      convert id_comp _ f,
      apply adj.left_triangle_components
    end,
    right_inv := λ g, begin
      change _ ≫ G.map (_ ≫ _) = _,
      rw [G.map_comp, ←assoc, ←functor.comp_map, ←adj.unit.naturality, assoc],
      convert comp_id _ g,
      apply adj.right_triangle_components
  end },
  hom_equiv_naturality_left' :=
  begin
    intros X' X Y f g,
    dsimp,
    simp only [category_theory.functor.map_comp],
    erw [← category.assoc, ← category.assoc],
    congr' 1,
    simpa using (adj.unit.naturality f).symm
  end,
  .. adj }

end adjunction

end category_theory
