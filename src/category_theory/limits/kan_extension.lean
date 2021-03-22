/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/
import category_theory.punit
import category_theory.comma
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

local attribute [simp] comma.snd comma.map_left

/-- The index category of limits used to define `Ran`. -/
@[simp, derive category, nolint has_inhabited_instance]
def index (l : L) := comma (functor.from_punit l) ι

variable {ι}

/-- Make a term of type `Ran.index ι x`. -/
@[simp]
def index.mk {x : L} {y : S} (f : x ⟶ ι.obj y) : index ι x := ⟨⟨⟩, y, f⟩

/-- The functor `Ran.index ι y ⥤ Ran.index ι x` associated to a morphism `x ⟶ y`. -/
@[simp]
def index.map {x y : L} (f : x ⟶ y) : index ι y ⥤ index ι x :=
comma.map_left _ ((functor.const _).map f)

/-- Make a morphism in `Ran.index ι x`. -/
@[simps]
def index.mk_hom {x : L} {y z : S} (f : x ⟶ ι.obj y) (g : y ⟶ z) :
  index.mk f ⟶ index.mk (f ≫ ι.map g) :=
{ left := 𝟙 _,
  right := g,
  w' := by simpa }

lemma index.map_mk {x y : L} {z : S} (f : x ⟶ ι.obj z) (g : y ⟶ x) :
  (index.map g).obj (index.mk f) = index.mk (g ≫ f) := rfl

lemma index.map_id {x : L} {j : index ι x} :
  (index.map (𝟙 x)).obj j = j := by {cases j, tidy}

lemma index.map_comp {x y z : L} (f : z ⟶ y) (g : y ⟶ x) (j : index ι x) :
  (index.map (f ≫ g)).obj j = (index.map f).obj ((index.map g).obj j) :=
by {cases j, tidy}

-- TODO: Use this to prove that `Ran.adjunction` is reflective
-- when `ι` is fully faithful.
/-- `index.mk (𝟙 (ι.obj y))` is initial when `ι` is fully faithful. -/
def index.mk_id_initial [full ι] [faithful ι] {y : S} : is_initial (index.mk (𝟙 (ι.obj y))) :=
{ desc := λ T, ⟨eq_to_hom (by simp), ι.preimage T.X.hom, by tidy⟩,
  --fac' := _,
  uniq' := begin
    intros T m w,
    ext j,
    apply ι.map_injective,
    have := m.w,
    tidy,
  end }

variable (ι)

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
@[simp]
def diagram (F : S ⥤ D) (x : L) : index ι x ⥤ D :=
  comma.snd (functor.from_punit x) ι ⋙ F
variable {ι}

/-- A cone over `Ran.diagram ι F x` used to define `Ran`. -/
@[simp]
def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) :
  cone (diagram ι F x) :=
{ X := G.obj x,
  π :=
  { app := λ i, G.map i.hom ≫ f.app i.right,
    naturality' := begin
      rintro ⟨⟨il⟩,ir,i⟩ ⟨⟨jl⟩,jr,j⟩ ⟨⟨⟨fl⟩⟩,fr,ff⟩,
      dsimp at *,
      simp only [category.id_comp, category.assoc] at *,
      rw [ff],
      have := f.naturality,
      tidy,
    end } }

variable (ι)

/-- An auxiliary definition used to define `Ran`. -/
@[simps]
def obj_aux (F : S ⥤ D) [∀ x, has_limits_of_shape (index ι x) D] : L ⥤ D :=
{ obj := λ x, limit (diagram ι F x),
  map := λ x y f, limit.pre (diagram _ _ _) (index.map f),
  map_id' := begin
    intro l,
    ext j,
    simp only [category.id_comp, limit.pre_π],
    congr' 1,
    rw [index.map_id],
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
def equiv [∀ x, has_limits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (G ⟶ obj_aux ι F) ≃ (ι ⋙ G ⟶ F) :=
{ to_fun := λ f,
  { app := λ x, f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (index.mk (𝟙 _)),
  naturality' := begin
    intros x y ff,
    simp only [functor.comp_map, nat_trans.naturality_assoc, obj_aux_map, category.assoc],
    congr' 1,
    erw [limit.pre_π, limit.w (diagram ι F _) (index.mk_hom (𝟙 _) ff)],
    congr,
    tidy,
  end },
  inv_fun := λ f,
  { app := λ x, limit.lift (diagram ι F x) (cone _ f),
    naturality' := begin
      intros x y ff,
      ext j,
      erw [limit.lift_pre, limit.lift_π, category.assoc, limit.lift_π (cone _ f) j],
      delta cone index.map,
      tidy,
    end },
  left_inv := begin
    intro x,
    ext k j,
    dsimp only [cone, diagram],
    rw limit.lift_π,
    simp only [nat_trans.naturality_assoc, obj_aux_map],
    congr' 1,
    erw limit.pre_π,
    congr,
    cases j,
    tidy,
  end,
  right_inv := by tidy }

/-- A variant of `Ran.equiv` with `whiskering_left` instead of functor composition. -/
@[simps]
def equiv' [∀ x, has_limits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (G ⟶ obj_aux ι F) ≃ (((whiskering_left _ _ _).obj ι).obj G ⟶ F) := equiv _ _ _

end Ran

/-- The right Kan extension of a functor. -/
@[simps]
def Ran [∀ X, has_limits_of_shape (Ran.index ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
adjunction.right_adjoint_of_equiv (λ F G, (Ran.equiv' ι G F).symm) (by tidy)

namespace Ran

variable (D)

/-- The adjunction associated to `Ran`. -/
def adjunction [∀ X, has_limits_of_shape (Ran.index ι X) D] :
  (whiskering_left _ _ D).obj ι ⊣ Ran ι :=
adjunction.adjunction_of_equiv_right _ _

end Ran

namespace Lan

local attribute [simp] comma.fst comma.map_right

/-- The index category of limits used to define `Lan`. -/
@[simp, derive category, nolint has_inhabited_instance]
def index (l : L) := comma ι (functor.from_punit l)

variable {ι}

/-- Make a term of type `Lan.index ι x`. -/
@[simp]
def index.mk {x : L} {y : S} (f : ι.obj y ⟶ x) : index ι x := ⟨y, ⟨⟩, f⟩

/-- The functor `Lan.index ι x ⥤ Lan.index ι y` associated to a morphism `x ⟶ y`. -/
@[simp]
def index.map {x y : L} (f : x ⟶ y) : index ι x ⥤ index ι y :=
comma.map_right _ ((functor.const _).map f)

/-- Make a morphism in `Lan.index ι x`. -/
@[simps]
def index.mk_hom {x : L} {y z : S} (f : ι.obj z ⟶ x) (g : y ⟶ z) :
  index.mk (ι.map g ≫ f) ⟶ index.mk f :=
{ left := g,
  right := 𝟙 _,
  w' := by simpa }

lemma index.map_mk {x y : L} {z : S} (f : ι.obj z ⟶ x) (g : x ⟶ y) :
  (index.map g).obj (index.mk f) = index.mk (f ≫ g) := rfl

lemma index.map_id {x : L} {j : index ι x} :
  (index.map (𝟙 x)).obj j = j := by {cases j, tidy}

lemma index.map_comp {x y z : L} (f : x ⟶ y) (g : y ⟶ z) (j : index ι x) :
  (index.map (f ≫ g)).obj j = (index.map g).obj ((index.map f).obj j) :=
by {cases j, tidy}
variable (ι)

-- TODO: Use this to prove that `Lan.adjunction` is coreflective
-- when `ι` is fully faithful.
/-- `index.mk (𝟙 (ι.obj y))` is terminal when `ι` is fully faithful. -/
def index.mk_id_terminal [full ι] [faithful ι] {y : S} : is_terminal (index.mk (𝟙 (ι.obj y))) :=
{ lift := λ T, ⟨ι.preimage T.X.hom, eq_to_hom (by simp), by tidy⟩,
  uniq' := begin
    intros T m w,
    ext j,
    { apply ι.map_injective,
      have := m.w,
      change _ ≫ 𝟙 _ = _ ≫ 𝟙 _ at this,
      rw [category.comp_id, category.comp_id] at this,
      simpa },
    { tidy }
  end }

/-- The diagram indexed by `Ran.index ι x` used to define `Ran`. -/
@[simp]
def diagram (F : S ⥤ D) (x : L) : index ι x ⥤ D :=
  comma.fst ι (functor.from_punit x) ⋙ F
variable {ι}

/-- A cocone over `Lan.diagram ι F x` used to define `Lan`. -/
@[simp]
def cocone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : F ⟶ ι ⋙ G) :
  cocone (diagram ι F x) :=
{ X := G.obj x,
  ι :=
  { app := λ i, f.app i.left ≫ G.map i.hom,
    naturality' := begin
      rintro ⟨ir,⟨il⟩,i⟩ ⟨jl,⟨jr⟩,j⟩ ⟨fl,⟨⟨fl⟩⟩,ff⟩,
      dsimp at *,
      simp only [functor.comp_map, category.comp_id, nat_trans.naturality_assoc],
      rw [← G.map_comp, ff],
      tidy,
    end } }

variable (ι)

/-- An auxiliary definition used to define `Lan`. -/
@[simps]
def obj_aux (F : S ⥤ D) [∀ x, has_colimits_of_shape (index ι x) D] : L ⥤ D :=
{ obj := λ x, colimit (diagram ι F x),
  map := λ x y f, colimit.pre (diagram _ _ _) (index.map f),
  map_id' := begin
    intro l,
    ext j,
    erw [colimit.ι_pre, category.comp_id],
    congr' 1,
    rw index.map_id,
  end,
  map_comp' := begin
    intros x y z f g,
    ext j,
    have := colimit.pre_pre (diagram ι F z) (index.map g) (index.map f),
    change _ = _ ≫
      colimit.pre (index.map g ⋙ diagram ι F z) (index.map f) ≫
      colimit.pre (diagram ι F z) (index.map g),
    rw this,
    change _ = colimit.ι ((index.map f ⋙ index.map g) ⋙ diagram ι F z) j ≫ _,
    rw [colimit.ι_pre, colimit.ι_pre],
    congr' 1,
    simp only [index.map_comp, functor.comp_obj],
  end }

/-- An auxiliary definition used to define `Lan` and `Lan.adjunction`. -/
@[simps]
def equiv [∀ x, has_colimits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (obj_aux ι F ⟶ G) ≃ (F ⟶ ι ⋙ G ) :=
{ to_fun := λ f,
  { app := λ x, by apply colimit.ι (diagram ι F (ι.obj x)) (index.mk (𝟙 _)) ≫ f.app _, -- sigh
  naturality' := begin
    intros x y ff,
    simp,
    erw [← f.naturality (ι.map ff)],
    delta obj_aux,
    erw [← category.assoc, ← category.assoc],
    erw colimit.ι_pre (diagram ι F (ι.obj y)) (index.map (ι.map ff)) (index.mk (𝟙 _)),
    congr' 1,
    have := colimit.w (diagram ι F (ι.obj y)) (index.mk_hom (𝟙 _) ff),
    convert this,
    rw index.map_mk,
    simp [index.map_mk],
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
    dsimp only [obj_aux, index.map],
    change colimit.ι _ _ ≫ colimit.pre (diagram ι F k) (index.map _) = _,
    rw colimit.ι_pre,
    congr,
    cases j,
    tidy,
  end,
  right_inv := by tidy }

/-- A variant of `Lan.equiv` with `whiskering_left` instead of functor composition. -/
@[simps]
def equiv' [∀ x, has_colimits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (obj_aux ι F ⟶ G) ≃ (F ⟶ ((whiskering_left _ _ _).obj ι).obj G) := equiv _ _ _

end Lan

/-- The left Kan extension of a functor. -/
@[simps]
def Lan [∀ X, has_colimits_of_shape (Lan.index ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
adjunction.left_adjoint_of_equiv (Lan.equiv' ι) (by tidy)

namespace Lan

variable (D)

/-- The adjunction associated to `Lan`. -/
def adjunction [∀ X, has_colimits_of_shape (Lan.index ι X) D] :
  Lan ι ⊣ (whiskering_left _ _ D).obj ι :=
adjunction.adjunction_of_equiv_left _ _

end Lan

end category_theory
