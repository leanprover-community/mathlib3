/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import category_theory.punit
import category_theory.structured_arrow
import category_theory.limits.functor_category
import category_theory.limits.shapes.terminal

/-!

# Kan extensions

This file defines the right and left Kan extensions of a functor.
They exist under the assumption that the target category has enough limits
resp. colimits.

The main definitions are `Ran ι` and `Lan ι`, where `ι : S ⥤ L` is a functor.
Namely, `Ran ι` is the right Kan extension, while `Lan ι` is the left Kan extension,
both as functors `(S ⥤ D) ⥤ (L ⥤ D)`.

To access the right resp. left adjunction associated to these, use `Ran.adjunction`
resp. `Lan.adjunction`.

# Projects

A lot of boilerplate could be generalized by defining and working with pseudofunctors.

-/

noncomputable theory

namespace category_theory

open limits

universes v u₁ u₂ u₃

variables {S : Type v} {L : Type u₂} {D : Type u₃}
variables [category.{v} S] [category.{v} L] [category.{v} D]
variables (ι : S ⥤ L)

namespace Ran

local attribute [simp] structured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbreviation diagram (F : S ⥤ D) (x : L) : structured_arrow x ι ⥤ D :=
  structured_arrow.proj x ι ⋙ F

variable {ι}

/-- A cone over `Ran.diagram ι F x` used to define `Ran`. -/
@[simp]
def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) :
  cone (diagram ι F x) :=
{ X := G.obj x,
  π :=
  { app := λ i, G.map i.hom ≫ f.app i.right,
    naturality' := begin
      rintro ⟨⟨il⟩, ir, i⟩ ⟨⟨jl⟩, jr, j⟩ ⟨⟨⟨fl⟩⟩, fr, ff⟩,
      dsimp at *,
      simp only [category.id_comp, category.assoc] at *,
      rw [ff],
      have := f.naturality,
      tidy,
    end } }

variable (ι)

/-- An auxiliary definition used to define `Ran`. -/
@[simps]
def loc (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] : L ⥤ D :=
{ obj := λ x, limit (diagram ι F x),
  map := λ x y f, limit.pre (diagram _ _ _) (structured_arrow.map f : structured_arrow _ ι ⥤ _),
  map_id' := begin
    intro l,
    ext j,
    simp only [category.id_comp, limit.pre_π],
    congr' 1,
    simp,
  end,
  map_comp' := begin
    intros x y z f g,
    ext j,
    erw [limit.pre_pre, limit.pre_π, limit.pre_π],
    congr' 1,
    tidy,
  end }

/-- An auxiliary definition used to define `Ran` and `Ran.adjunction`. -/
@[simps]
def equiv (F : S ⥤ D) [∀ x, has_limit (diagram ι F x)] (G : L ⥤ D) :
  (G ⟶ loc ι F) ≃ (((whiskering_left _ _ _).obj ι).obj G ⟶ F) :=
{ to_fun := λ f,
  { app := λ x, f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (structured_arrow.mk (𝟙 _)),
  naturality' := begin
    intros x y ff,
    dsimp only [whiskering_left],
    simp only [functor.comp_map, nat_trans.naturality_assoc, loc_map, category.assoc],
    congr' 1,
    erw limit.pre_π,
    change _ = _ ≫ (diagram ι F (ι.obj x)).map (structured_arrow.hom_mk _ _),
    rw limit.w,
    tidy,
  end },
  inv_fun := λ f,
  { app := λ x, limit.lift (diagram ι F x) (cone _ f),
    naturality' := begin
      intros x y ff,
      ext j,
      erw [limit.lift_pre, limit.lift_π, category.assoc, limit.lift_π (cone _ f) j],
      tidy,
    end },
  left_inv := begin
    intro x,
    ext k j,
    dsimp only [cone],
    rw limit.lift_π,
    simp only [nat_trans.naturality_assoc, loc_map],
    erw limit.pre_π,
    congr,
    cases j,
    tidy,
  end,
  right_inv := by tidy }

end Ran

/-- The right Kan extension of a functor. -/
@[simps]
def Ran [∀ X, has_limits_of_shape (structured_arrow X ι) D] : (S ⥤ D) ⥤ L ⥤ D :=
adjunction.right_adjoint_of_equiv (λ F G, (Ran.equiv ι G F).symm) (by tidy)

namespace Ran

variable (D)

/-- The adjunction associated to `Ran`. -/
def adjunction [∀ X, has_limits_of_shape (structured_arrow X ι) D] :
  (whiskering_left _ _ D).obj ι ⊣ Ran ι :=
adjunction.adjunction_of_equiv_right _ _

lemma reflective [full ι] [faithful ι] [∀ X, has_limits_of_shape (structured_arrow X ι) D] :
  is_iso (adjunction D ι).counit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intros F,
  apply nat_iso.is_iso_of_is_iso_app _,
  intros X,
  dsimp [adjunction],
  simp only [category.id_comp],
  exact is_iso.of_iso ((limit.is_limit _).cone_point_unique_up_to_iso
    (limit_of_diagram_initial structured_arrow.mk_id_initial _)),
end

end Ran

namespace Lan

local attribute [simp] costructured_arrow.proj

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
abbreviation diagram (F : S ⥤ D) (x : L) : costructured_arrow ι x ⥤ D :=
  costructured_arrow.proj ι x ⋙ F
variable {ι}

/-- A cocone over `Lan.diagram ι F x` used to define `Lan`. -/
@[simp]
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) :
  cocone (diagram ι F x) :=
{ X := G.obj x,
  ι :=
  { app := λ i, f.app i.left ≫ G.map i.hom,
    naturality' := begin
      rintro ⟨ir, ⟨il⟩, i⟩ ⟨jl, ⟨jr⟩, j⟩ ⟨fl, ⟨⟨fl⟩⟩, ff⟩,
      dsimp at *,
      simp only [functor.comp_map, category.comp_id, nat_trans.naturality_assoc],
      rw [← G.map_comp, ff],
      tidy,
    end } }

variable (ι)

/-- An auxiliary definition used to define `Lan`. -/
@[simps]
def loc (F : S ⥤ D) [I : ∀ x, has_colimit (diagram ι F x)] : L ⥤ D :=
{ obj := λ x, colimit (diagram ι F x),
  map := λ x y f,
    colimit.pre (diagram _ _ _) (costructured_arrow.map f : costructured_arrow ι _ ⥤ _),
  map_id' := begin
    intro l,
    ext j,
    erw [colimit.ι_pre, category.comp_id],
    congr' 1,
    simp,
  end,
  map_comp' := begin
    intros x y z f g,
    ext j,
    let ff : costructured_arrow ι _ ⥤ _ := costructured_arrow.map f,
    let gg : costructured_arrow ι _ ⥤ _ := costructured_arrow.map g,
    let dd := diagram ι F z,
    -- I don't know why lean can't deduce the following three instances...
    haveI : has_colimit (ff ⋙ gg ⋙ dd) := I _,
    haveI : has_colimit ((ff ⋙ gg) ⋙ dd) := I _,
    haveI : has_colimit (gg ⋙ dd) :=  I _,
    change _ = colimit.ι ((ff ⋙ gg) ⋙ dd) j ≫ _ ≫ _,
    erw [colimit.pre_pre dd gg ff, colimit.ι_pre, colimit.ι_pre],
    congr' 1,
    simp,
  end }

/-- An auxiliary definition used to define `Lan` and `Lan.adjunction`. -/
@[simps]
def equiv (F : S ⥤ D) [I : ∀ x, has_colimit (diagram ι F x)] (G : L ⥤ D) :
  (loc ι F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj ι).obj G) :=
{ to_fun := λ f,
  { app := λ x,
      by apply colimit.ι (diagram ι F (ι.obj x)) (costructured_arrow.mk (𝟙 _)) ≫ f.app _, -- sigh
  naturality' := begin
    intros x y ff,
    dsimp only [whiskering_left],
    simp only [functor.comp_map, category.assoc],
    rw [← f.naturality (ι.map ff), ← category.assoc, ← category.assoc],
    let fff : costructured_arrow ι _ ⥤ _ := costructured_arrow.map (ι.map ff),
    -- same issue :-(
    haveI : has_colimit (fff ⋙ diagram ι F (ι.obj y)) := I _,
    erw colimit.ι_pre (diagram ι F (ι.obj y)) fff (costructured_arrow.mk (𝟙 _)),
    let xx : costructured_arrow ι (ι.obj y) := costructured_arrow.mk (ι.map ff),
    let yy : costructured_arrow ι (ι.obj y) := costructured_arrow.mk (𝟙 _),
    let fff : xx ⟶ yy := costructured_arrow.hom_mk ff
      (by {simp only [costructured_arrow.mk_hom_eq_self], erw category.comp_id}),
    erw colimit.w (diagram ι F (ι.obj y)) fff,
    congr,
    simp,
  end },
  inv_fun := λ f,
  { app := λ x, colimit.desc (diagram ι F x) (cocone _ f),
    naturality' := begin
      intros x y ff,
      ext j,
      erw [colimit.pre_desc, ← category.assoc, colimit.ι_desc, colimit.ι_desc],
      tidy,
    end },
  left_inv := begin
    intro x,
    ext k j,
    rw colimit.ι_desc,
    dsimp only [cocone],
    rw [category.assoc, ← x.naturality j.hom, ← category.assoc],
    congr' 1,
    change colimit.ι _ _ ≫ colimit.pre (diagram ι F k) (costructured_arrow.map _) = _,
    rw colimit.ι_pre,
    congr,
    cases j,
    tidy,
  end,
  right_inv := by tidy }

end Lan

/-- The left Kan extension of a functor. -/
@[simps]
def Lan [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
adjunction.left_adjoint_of_equiv (λ F G, Lan.equiv ι F G) (by tidy)

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] :
  Lan ι ⊣ (whiskering_left _ _ D).obj ι :=
adjunction.adjunction_of_equiv_left _ _

lemma coreflective [full ι] [faithful ι] [∀ X, has_colimits_of_shape (costructured_arrow ι X) D] :
  is_iso (adjunction D ι).unit :=
begin
  apply nat_iso.is_iso_of_is_iso_app _,
  intros F,
  apply nat_iso.is_iso_of_is_iso_app _,
  intros X,
  dsimp [adjunction],
  simp only [category.comp_id],
  exact is_iso.of_iso ((colimit.is_colimit _).cocone_point_unique_up_to_iso
    (colimit_of_diagram_terminal costructured_arrow.mk_id_terminal _)).symm,
end

end Lan

end category_theory
