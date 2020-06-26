/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.shapes.terminal

/-!
# Binary (co)products

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.

We include lemmas for simplifying equations involving projections and coprojections, and define
braiding and associating isomorphisms, and the product comparison morphism.
-/

universes v u u₂

open category_theory

namespace category_theory.limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
@[derive decidable_eq, derive inhabited]
inductive walking_pair : Type v
| left | right

open walking_pair

instance fintype_walking_pair : fintype walking_pair :=
{ elems := {left, right},
  complete := λ x, by { cases x; simp } }

/--
The equivalence swapping left and right.
-/
def walking_pair.swap : walking_pair ≃ walking_pair :=
{ to_fun := λ j, walking_pair.rec_on j right left,
  inv_fun := λ j, walking_pair.rec_on j right left,
  left_inv := λ j, by { cases j; refl, },
  right_inv := λ j, by { cases j; refl, }, }

@[simp] lemma walking_pair.swap_apply_left : walking_pair.swap left = right := rfl
@[simp] lemma walking_pair.swap_apply_right : walking_pair.swap right = left := rfl
@[simp] lemma walking_pair.swap_symm_apply_tt : walking_pair.swap.symm left = right := rfl
@[simp] lemma walking_pair.swap_symm_apply_ff : walking_pair.swap.symm right = left := rfl

/--
An equivalence from `walking_pair` to `bool`, sometimes useful when reindexing limits.
-/
def walking_pair.equiv_bool : walking_pair ≃ bool :=
{ to_fun := λ j, walking_pair.rec_on j tt ff, -- to match equiv.sum_equiv_sigma_bool
  inv_fun := λ b, bool.rec_on b right left,
  left_inv := λ j, by { cases j; refl, },
  right_inv := λ b, by { cases b; refl, }, }

@[simp] lemma walking_pair.equiv_bool_apply_left : walking_pair.equiv_bool left = tt := rfl
@[simp] lemma walking_pair.equiv_bool_apply_right : walking_pair.equiv_bool right = ff := rfl
@[simp] lemma walking_pair.equiv_bool_symm_apply_tt : walking_pair.equiv_bool.symm tt = left := rfl
@[simp] lemma walking_pair.equiv_bool_symm_apply_ff : walking_pair.equiv_bool.symm ff = right := rfl

variables {C : Type u} [category.{v} C]

/-- The diagram on the walking pair, sending the two points to `X` and `Y`. -/
def pair (X Y : C) : discrete walking_pair ⥤ C :=
discrete.functor (λ j, walking_pair.cases_on j X Y)

@[simp] lemma pair_obj_left (X Y : C) : (pair X Y).obj left = X := rfl
@[simp] lemma pair_obj_right (X Y : C) : (pair X Y).obj right = Y := rfl

section
variables {F G : discrete walking_pair.{v} ⥤ C} (f : F.obj left ⟶ G.obj left) (g : F.obj right ⟶ G.obj right)

/-- The natural transformation between two functors out of the walking pair, specified by its components. -/
def map_pair : F ⟶ G :=
{ app := λ j, match j with
  | left := f
  | right := g
  end }

@[simp] lemma map_pair_left : (map_pair f g).app left = f := rfl
@[simp] lemma map_pair_right : (map_pair f g).app right = g := rfl

/-- The natural isomorphism between two functors out of the walking pair, specified by its components. -/
@[simps]
def map_pair_iso (f : F.obj left ≅ G.obj left) (g : F.obj right ≅ G.obj right) : F ≅ G :=
{ hom := map_pair f.hom g.hom,
  inv := map_pair f.inv g.inv,
  hom_inv_id' := begin ext ⟨⟩; { dsimp, simp, } end,
  inv_hom_id' := begin ext ⟨⟩; { dsimp, simp, } end }
end

section
variables {D : Type u} [category.{v} D]

/-- The natural isomorphism between `pair X Y ⋙ F` and `pair (F.obj X) (F.obj Y)`. -/
def pair_comp (X Y : C) (F : C ⥤ D) : pair X Y ⋙ F ≅ pair (F.obj X) (F.obj Y) :=
map_pair_iso (eq_to_iso rfl) (eq_to_iso rfl)
end

/-- Every functor out of the walking pair is naturally isomorphic (actually, equal) to a `pair` -/
def diagram_iso_pair (F : discrete walking_pair ⥤ C) :
  F ≅ pair (F.obj walking_pair.left) (F.obj walking_pair.right) :=
map_pair_iso (eq_to_iso rfl) (eq_to_iso rfl)

/-- A binary fan is just a cone on a diagram indexing a product. -/
abbreviation binary_fan (X Y : C) := cone (pair X Y)

/-- The first projection of a binary fan. -/
abbreviation binary_fan.fst {X Y : C} (s : binary_fan X Y) := s.π.app walking_pair.left

/-- The second projection of a binary fan. -/
abbreviation binary_fan.snd {X Y : C} (s : binary_fan X Y) := s.π.app walking_pair.right

lemma binary_fan.is_limit.hom_ext {W X Y : C} {s : binary_fan X Y} (h : is_limit s)
  {f g : W ⟶ s.X} (h₁ : f ≫ s.fst = g ≫ s.fst) (h₂ : f ≫ s.snd = g ≫ s.snd) : f = g :=
h.hom_ext $ λ j, walking_pair.cases_on j h₁ h₂

/-- A binary cofan is just a cocone on a diagram indexing a coproduct. -/
abbreviation binary_cofan (X Y : C) := cocone (pair X Y)

/-- The first inclusion of a binary cofan. -/
abbreviation binary_cofan.inl {X Y : C} (s : binary_cofan X Y) := s.ι.app walking_pair.left

/-- The second inclusion of a binary cofan. -/
abbreviation binary_cofan.inr {X Y : C} (s : binary_cofan X Y) := s.ι.app walking_pair.right

lemma binary_cofan.is_colimit.hom_ext {W X Y : C} {s : binary_cofan X Y} (h : is_colimit s)
  {f g : s.X ⟶ W} (h₁ : s.inl ≫ f = s.inl ≫ g) (h₂ : s.inr ≫ f = s.inr ≫ g) : f = g :=
h.hom_ext $ λ j, walking_pair.cases_on j h₁ h₂

variables {X Y : C}

/-- A binary fan with vertex `P` consists of the two projections `π₁ : P ⟶ X` and `π₂ : P ⟶ Y`. -/
def binary_fan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : binary_fan X Y :=
{ X := P,
  π := { app := λ j, walking_pair.cases_on j π₁ π₂ }}

/-- A binary cofan with vertex `P` consists of the two inclusions `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P`. -/
def binary_cofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : binary_cofan X Y :=
{ X := P,
  ι := { app := λ j, walking_pair.cases_on j ι₁ ι₂ }}

@[simp] lemma binary_fan.mk_π_app_left {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.left = π₁ := rfl
@[simp] lemma binary_fan.mk_π_app_right {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.right = π₂ := rfl
@[simp] lemma binary_cofan.mk_ι_app_left {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.left = ι₁ := rfl
@[simp] lemma binary_cofan.mk_ι_app_right {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.right = ι₂ := rfl

/-- If `s` is a limit binary fan over `X` and `Y`, then every pair of morphisms `f : W ⟶ X` and
    `g : W ⟶ Y` induces a morphism `l : W ⟶ s.X` satisfying `l ≫ s.fst = f` and `l ≫ s.snd = g`.
    -/
def binary_fan.is_limit.lift' {W X Y : C} {s : binary_fan X Y} (h : is_limit s) (f : W ⟶ X)
  (g : W ⟶ Y) : {l : W ⟶ s.X // l ≫ s.fst = f ∧ l ≫ s.snd = g} :=
⟨h.lift $ binary_fan.mk f g, h.fac _ _, h.fac _ _⟩

/-- If `s` is a colimit binary cofan over `X` and `Y`,, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : s.X ⟶ W` satisfying `s.inl ≫ l = f` and `s.inr ≫ l = g`.
    -/
def binary_cofan.is_colimit.desc' {W X Y : C} {s : binary_cofan X Y} (h : is_colimit s) (f : X ⟶ W)
  (g : Y ⟶ W) : {l : s.X ⟶ W // s.inl ≫ l = f ∧ s.inr ≫ l = g} :=
⟨h.desc $ binary_cofan.mk f g, h.fac _ _, h.fac _ _⟩

/-- An abbreviation for `has_limit (pair X Y)`. -/
abbreviation has_binary_product (X Y : C) := has_limit (pair X Y)
/-- An abbreviation for `has_colimit (pair X Y)`. -/
abbreviation has_binary_coproduct (X Y : C) := has_colimit (pair X Y)

/-- If we have chosen a product of `X` and `Y`, we can access it using `prod X Y` or
    `X ⨯ Y`. -/
abbreviation prod (X Y : C) [has_binary_product X Y] := limit (pair X Y)

/-- If we have chosen a coproduct of `X` and `Y`, we can access it using `coprod X Y ` or
    `X ⨿ Y`. -/
abbreviation coprod (X Y : C) [has_binary_coproduct X Y] := colimit (pair X Y)

notation X ` ⨯ `:20 Y:20 := prod X Y
notation X ` ⨿ `:20 Y:20 := coprod X Y

/-- The projection map to the first component of the product. -/
abbreviation prod.fst {X Y : C} [has_binary_product X Y] : X ⨯ Y ⟶ X :=
limit.π (pair X Y) walking_pair.left

/-- The projecton map to the second component of the product. -/
abbreviation prod.snd {X Y : C} [has_binary_product X Y] : X ⨯ Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right

/-- The inclusion map from the first component of the coproduct. -/
abbreviation coprod.inl {X Y : C} [has_binary_coproduct X Y] : X ⟶ X ⨿ Y :=
colimit.ι (pair X Y) walking_pair.left

/-- The inclusion map from the second component of the coproduct. -/
abbreviation coprod.inr {X Y : C} [has_binary_coproduct X Y] : Y ⟶ X ⨿ Y :=
colimit.ι (pair X Y) walking_pair.right

@[ext] lemma prod.hom_ext {W X Y : C} [has_binary_product X Y] {f g : W ⟶ X ⨯ Y}
  (h₁ : f ≫ prod.fst = g ≫ prod.fst) (h₂ : f ≫ prod.snd = g ≫ prod.snd) : f = g :=
binary_fan.is_limit.hom_ext (limit.is_limit _) h₁ h₂

@[ext] lemma coprod.hom_ext {W X Y : C} [has_binary_coproduct X Y] {f g : X ⨿ Y ⟶ W}
  (h₁ : coprod.inl ≫ f = coprod.inl ≫ g) (h₂ : coprod.inr ≫ f = coprod.inr ≫ g) : f = g :=
binary_cofan.is_colimit.hom_ext (colimit.is_colimit _) h₁ h₂

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `prod.lift f g : W ⟶ X ⨯ Y`. -/
abbreviation prod.lift {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⨯ Y :=
limit.lift _ (binary_fan.mk f g)

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `coprod.desc f g : X ⨿ Y ⟶ W`. -/
abbreviation coprod.desc {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⨿ Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

@[simp, reassoc]
lemma prod.lift_fst {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  prod.lift f g ≫ prod.fst = f :=
limit.lift_π _ _

@[simp, reassoc]
lemma prod.lift_snd {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  prod.lift f g ≫ prod.snd = g :=
limit.lift_π _ _

/- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma. -/
@[reassoc, simp]
lemma prod.lift_comp_comp {V W X Y : C} [has_binary_product X Y] (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) :
  prod.lift (f ≫ g) (f ≫ h) = f ≫ prod.lift g h :=
by tidy

@[simp, reassoc]
lemma coprod.inl_desc {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  coprod.inl ≫ coprod.desc f g = f :=
colimit.ι_desc _ _

@[simp, reassoc]
lemma coprod.inr_desc {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  coprod.inr ≫ coprod.desc f g = g :=
colimit.ι_desc _ _

/- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma. -/
@[reassoc, simp]
lemma coprod.desc_comp_comp {V W X Y : C} [has_binary_coproduct X Y] (f : V ⟶ W) (g : X ⟶ V)
  (h : Y ⟶ V) : coprod.desc (g ≫ f) (h ≫ f) = coprod.desc g h ≫ f :=
by tidy

instance prod.mono_lift_of_mono_left {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y)
  [mono f] : mono (prod.lift f g) :=
mono_of_mono_fac $ prod.lift_fst _ _

instance prod.mono_lift_of_mono_right {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y)
  [mono g] : mono (prod.lift f g) :=
mono_of_mono_fac $ prod.lift_snd _ _

instance coprod.epi_desc_of_epi_left {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi f] : epi (coprod.desc f g) :=
epi_of_epi_fac $ coprod.inl_desc _ _

instance coprod.epi_desc_of_epi_right {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi g] : epi (coprod.desc f g) :=
epi_of_epi_fac $ coprod.inr_desc _ _

/-- If the product of `X` and `Y` exists, then every pair of morphisms `f : W ⟶ X` and `g : W ⟶ Y`
    induces a morphism `l : W ⟶ X ⨯ Y` satisfying `l ≫ prod.fst = f` and `l ≫ prod.snd = g`. -/
def prod.lift' {W X Y : C} [has_binary_product X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  {l : W ⟶ X ⨯ Y // l ≫ prod.fst = f ∧ l ≫ prod.snd = g} :=
⟨prod.lift f g, prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- If the coproduct of `X` and `Y` exists, then every pair of morphisms `f : X ⟶ W` and
    `g : Y ⟶ W` induces a morphism `l : X ⨿ Y ⟶ W` satisfying `coprod.inl ≫ l = f` and
    `coprod.inr ≫ l = g`. -/
def coprod.desc' {W X Y : C} [has_binary_coproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  {l : X ⨿ Y ⟶ W // coprod.inl ≫ l = f ∧ coprod.inr ≫ l = g} :=
⟨coprod.desc f g, coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : X ⟶ Z` induces a morphism `prod.map f g : W ⨯ X ⟶ Y ⨯ Z`. -/
abbreviation prod.map {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⨯ X ⟶ Y ⨯ Z :=
lim.map (map_pair f g)

/-- If the products `W ⨯ X` and `Y ⨯ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : X ≅ Z` induces a isomorphism `prod.map_iso f g : W ⨯ X ≅ Y ⨯ Z`. -/
abbreviation prod.map_iso {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : W ⨯ X ≅ Y ⨯ Z :=
lim.map_iso (map_pair_iso f g)

-- Note that the next two `simp` lemmas are proved by `simp`,
-- but nevertheless are useful,
-- because they state the right hand side in terms of `prod.map`
-- rather than `lim.map`.
@[simp] lemma prod.map_iso_hom {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : (prod.map_iso f g).hom = prod.map f.hom g.hom := by simp

@[simp] lemma prod.map_iso_inv {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : (prod.map_iso f g).inv = prod.map f.inv g.inv := by simp

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of morphisms `f : W ⟶ Y` and
    `g : W ⟶ Z` induces a morphism `coprod.map f g : W ⨿ X ⟶ Y ⨿ Z`. -/
abbreviation coprod.map {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⨿ X ⟶ Y ⨿ Z :=
colim.map (map_pair f g)

/-- If the coproducts `W ⨿ X` and `Y ⨿ Z` exist, then every pair of isomorphisms `f : W ≅ Y` and
    `g : W ≅ Z` induces a isomorphism `coprod.map_iso f g : W ⨿ X ≅ Y ⨿ Z`. -/
abbreviation coprod.map_iso {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : W ⨿ X ≅ Y ⨿ Z :=
colim.map_iso (map_pair_iso f g)

@[simp] lemma coprod.map_iso_hom {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : (coprod.map_iso f g).hom = coprod.map f.hom g.hom := by simp

@[simp] lemma coprod.map_iso_inv {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ≅ Y) (g : X ≅ Z) : (coprod.map_iso f g).inv = coprod.map f.inv g.inv := by simp


section prod_lemmas
variable [has_limits_of_shape.{v} (discrete walking_pair) C]

@[reassoc]
lemma prod.map_fst {W X Y Z : C}
  (f : W ⟶ Y) (g : X ⟶ Z) : prod.map f g ≫ prod.fst = prod.fst ≫ f := by simp

@[reassoc]
lemma prod.map_snd {W X Y Z : C}
  (f : W ⟶ Y) (g : X ⟶ Z) : prod.map f g ≫ prod.snd = prod.snd ≫ g := by simp

@[simp] lemma prod_map_id_id {X Y : C} :
  prod.map (𝟙 X) (𝟙 Y) = 𝟙 _ :=
by tidy

@[simp] lemma prod_lift_fst_snd {X Y : C} :
  prod.lift prod.fst prod.snd = 𝟙 (X ⨯ Y) :=
by tidy

-- I don't think it's a good idea to make any of the following simp lemmas.
@[reassoc]
lemma prod_map_map {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
  prod.map (𝟙 X) f ≫ prod.map g (𝟙 B) = prod.map g (𝟙 A) ≫ prod.map (𝟙 Y) f :=
by tidy

@[reassoc] lemma prod_map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  prod.map (f ≫ g) (𝟙 W) = prod.map f (𝟙 W) ≫ prod.map g (𝟙 W) :=
by tidy

@[reassoc] lemma prod_map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  prod.map (𝟙 W) (f ≫ g) = prod.map (𝟙 W) f ≫ prod.map (𝟙 W) g :=
by tidy

@[reassoc] lemma prod.lift_map (V W X Y Z : C) (f : V ⟶ W) (g : V ⟶ X) (h : W ⟶ Y) (k : X ⟶ Z) :
  prod.lift f g ≫ prod.map h k = prod.lift (f ≫ h) (g ≫ k) :=
by tidy

end prod_lemmas

section coprod_lemmas
variable [has_colimits_of_shape.{v} (discrete walking_pair) C]

@[reassoc]
lemma coprod.inl_map {W X Y Z : C}
  (f : W ⟶ Y) (g : X ⟶ Z) : coprod.inl ≫ coprod.map f g = f ≫ coprod.inl := by simp

@[reassoc]
lemma coprod.inr_map {W X Y Z : C}
  (f : W ⟶ Y) (g : X ⟶ Z) : coprod.inr ≫ coprod.map f g = g ≫ coprod.inr := by simp

@[simp] lemma coprod_map_id_id {X Y : C} :
  coprod.map (𝟙 X) (𝟙 Y) = 𝟙 _ :=
by tidy

@[simp] lemma coprod_desc_inl_inr {X Y : C} :
  coprod.desc coprod.inl coprod.inr = 𝟙 (X ⨿ Y) :=
by tidy

-- I don't think it's a good idea to make any of the following simp lemmas.
@[reassoc]
lemma coprod_map_map {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) :
  coprod.map (𝟙 X) f ≫ coprod.map g (𝟙 B) = coprod.map g (𝟙 A) ≫ coprod.map (𝟙 Y) f :=
by tidy

@[reassoc] lemma coprod_map_comp_id {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  coprod.map (f ≫ g) (𝟙 W) = coprod.map f (𝟙 W) ≫ coprod.map g (𝟙 W) :=
by tidy

@[reassoc] lemma coprod_map_id_comp {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  coprod.map (𝟙 W) (f ≫ g) = coprod.map (𝟙 W) f ≫ coprod.map (𝟙 W) g :=
by tidy

@[reassoc] lemma coprod.map_desc {S T U V W : C} (f : U ⟶ S) (g : W ⟶ S) (h : T ⟶ U) (k : V ⟶ W) :
  coprod.map h k ≫ coprod.desc f g = coprod.desc (h ≫ f) (k ≫ g) :=
by tidy

end coprod_lemmas


variables (C)

/-- `has_binary_products` represents a choice of product for every pair of objects. -/
class has_binary_products :=
(has_limits_of_shape : has_limits_of_shape.{v} (discrete walking_pair) C)

/-- `has_binary_coproducts` represents a choice of coproduct for every pair of objects. -/
class has_binary_coproducts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} (discrete walking_pair) C)

attribute [instance] has_binary_products.has_limits_of_shape has_binary_coproducts.has_colimits_of_shape

@[priority 200] -- see Note [lower instance priority]
instance [has_finite_products.{v} C] : has_binary_products.{v} C :=
{ has_limits_of_shape := by apply_instance }
@[priority 200] -- see Note [lower instance priority]
instance [has_finite_coproducts.{v} C] : has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := by apply_instance }

/-- If `C` has all limits of diagrams `pair X Y`, then it has all binary products -/
def has_binary_products_of_has_limit_pair [Π {X Y : C}, has_limit (pair X Y)] :
  has_binary_products.{v} C :=
{ has_limits_of_shape := { has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm } }

/-- If `C` has all colimits of diagrams `pair X Y`, then it has all binary coproducts -/
def has_binary_coproducts_of_has_colimit_pair [Π {X Y : C}, has_colimit (pair X Y)] :
  has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := { has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) } }

section

variables {C} [has_binary_products.{v} C]
variables {D : Type u₂} [category.{v} D] [has_binary_products.{v} D]

-- FIXME deterministic timeout with `-T50000`
/-- The binary product functor. -/
@[simps]
def prod_functor : C ⥤ C ⥤ C :=
{ obj := λ X, { obj := λ Y, X ⨯ Y, map := λ Y Z, prod.map (𝟙 X) },
  map := λ Y Z f, { app := λ T, prod.map f (𝟙 T) }}

/-- The braiding isomorphism which swaps a binary product. -/
@[simps] def prod.braiding (P Q : C) : P ⨯ Q ≅ Q ⨯ P :=
{ hom := prod.lift prod.snd prod.fst,
  inv := prod.lift prod.snd prod.fst }

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc] lemma braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
  prod.map f g ≫ (prod.braiding _ _).hom = (prod.braiding _ _).hom ≫ prod.map g f :=
by tidy

@[simp, reassoc] lemma prod.symmetry' (P Q : C) :
  prod.lift prod.snd prod.fst ≫ prod.lift prod.snd prod.fst = 𝟙 (P ⨯ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
@[reassoc] lemma prod.symmetry (P Q : C) :
  (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
by simp

/-- The associator isomorphism for binary products. -/
@[simps] def prod.associator
  (P Q R : C) : (P ⨯ Q) ⨯ R ≅ P ⨯ (Q ⨯ R) :=
{ hom :=
  prod.lift
    (prod.fst ≫ prod.fst)
    (prod.lift (prod.fst ≫ prod.snd) prod.snd),
  inv :=
  prod.lift
    (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.snd ≫ prod.snd) }

/-- The product functor can be decomposed. -/
def prod_functor_left_comp (X Y : C) :
  prod_functor.obj (X ⨯ Y) ≅ prod_functor.obj Y ⋙ prod_functor.obj X :=
nat_iso.of_components (prod.associator _ _) (by tidy)

@[reassoc]
lemma prod.pentagon (W X Y Z : C) :
  prod.map ((prod.associator W X Y).hom) (𝟙 Z) ≫
      (prod.associator W (X ⨯ Y) Z).hom ≫ prod.map (𝟙 W) ((prod.associator X Y Z).hom) =
    (prod.associator (W ⨯ X) Y Z).hom ≫ (prod.associator W X (Y ⨯ Z)).hom :=
by tidy

@[reassoc]
lemma prod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  prod.map (prod.map f₁ f₂) f₃ ≫ (prod.associator Y₁ Y₂ Y₃).hom =
    (prod.associator X₁ X₂ X₃).hom ≫ prod.map f₁ (prod.map f₂ f₃) :=
by tidy

/--
The product comparison morphism.

In `category_theory/limits/preserves` we show this is always an iso iff F preserves binary products.
-/
def prod_comparison (F : C ⥤ D) (A B : C) : F.obj (A ⨯ B) ⟶ F.obj A ⨯ F.obj B :=
prod.lift (F.map prod.fst) (F.map prod.snd)

/-- Naturality of the prod_comparison morphism in both arguments. -/
@[reassoc] lemma prod_comparison_natural (F : C ⥤ D) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  F.map (prod.map f g) ≫ prod_comparison F A' B' = prod_comparison F A B ≫ prod.map (F.map f) (F.map g) :=
begin
  rw [prod_comparison, prod_comparison, prod.lift_map],
  apply prod.hom_ext,
  { simp only [← F.map_comp, category.assoc, prod.lift_fst, prod.map_fst, category.comp_id] },
  { simp only [← F.map_comp, category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc] },
end

@[reassoc]
lemma inv_prod_comparison_map_fst (F : C ⥤ D) (A B : C) [is_iso (prod_comparison F A B)] :
  inv (prod_comparison F A B) ≫ F.map prod.fst = prod.fst :=
begin
  erw (as_iso (prod_comparison F A B)).inv_comp_eq,
  dsimp [as_iso_hom, prod_comparison],
  rw prod.lift_fst,
end

@[reassoc]
lemma inv_prod_comparison_map_snd (F : C ⥤ D) (A B : C) [is_iso (prod_comparison F A B)] :
  inv (prod_comparison F A B) ≫ F.map prod.snd = prod.snd :=
begin
  erw (as_iso (prod_comparison F A B)).inv_comp_eq,
  dsimp [as_iso_hom, prod_comparison],
  rw prod.lift_snd,
end

/-- If the product comparison morphism is an iso, its inverse is natural. -/
@[reassoc]
lemma prod_comparison_inv_natural (F : C ⥤ D) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B')
  [is_iso (prod_comparison F A B)] [is_iso (prod_comparison F A' B')] :
  inv (prod_comparison F A B) ≫ F.map (prod.map f g) = prod.map (F.map f) (F.map g) ≫ inv (prod_comparison F A' B') :=
by { erw [(as_iso (prod_comparison F A' B')).eq_comp_inv, category.assoc,
    (as_iso (prod_comparison F A B)).inv_comp_eq, prod_comparison_natural], refl }

variables [has_terminal.{v} C]

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simps] def prod.left_unitor
  (P : C) : ⊤_ C ⨯ P ≅ P :=
{ hom := prod.snd,
  inv := prod.lift (terminal.from P) (𝟙 _) }

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simps] def prod.right_unitor
  (P : C) : P ⨯ ⊤_ C ≅ P :=
{ hom := prod.fst,
  inv := prod.lift (𝟙 _) (terminal.from P) }

@[reassoc]
lemma prod_left_unitor_hom_naturality (f : X ⟶ Y):
  prod.map (𝟙 _) f ≫ (prod.left_unitor Y).hom = (prod.left_unitor X).hom ≫ f :=
prod.map_snd _ _

@[reassoc]
lemma prod_left_unitor_inv_naturality (f : X ⟶ Y):
  (prod.left_unitor X).inv ≫ prod.map (𝟙 _) f = f ≫ (prod.left_unitor Y).inv :=
by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod_left_unitor_hom_naturality]

@[reassoc]
lemma prod_right_unitor_hom_naturality (f : X ⟶ Y):
  prod.map f (𝟙 _) ≫ (prod.right_unitor Y).hom = (prod.right_unitor X).hom ≫ f :=
prod.map_fst _ _

@[reassoc]
lemma prod_right_unitor_inv_naturality (f : X ⟶ Y):
  (prod.right_unitor X).inv ≫ prod.map f (𝟙 _) = f ≫ (prod.right_unitor Y).inv :=
by rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, prod_right_unitor_hom_naturality]

lemma prod.triangle (X Y : C) :
  (prod.associator X (⊤_ C) Y).hom ≫ prod.map (𝟙 X) ((prod.left_unitor Y).hom) =
    prod.map ((prod.right_unitor X).hom) (𝟙 Y) :=
by tidy

end

section
variables {C} [has_binary_coproducts.{v} C]

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simps] def coprod.braiding (P Q : C) : P ⨿ Q ≅ Q ⨿ P :=
{ hom := coprod.desc coprod.inr coprod.inl,
  inv := coprod.desc coprod.inr coprod.inl }

@[simp] lemma coprod.symmetry' (P Q : C) :
  coprod.desc coprod.inr coprod.inl ≫ coprod.desc coprod.inr coprod.inl = 𝟙 (P ⨿ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
lemma coprod.symmetry (P Q : C) :
  (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
by simp

/-- The associator isomorphism for binary coproducts. -/
@[simps] def coprod.associator
  (P Q R : C) : (P ⨿ Q) ⨿ R ≅ P ⨿ (Q ⨿ R) :=
{ hom :=
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr),
  inv :=
  coprod.desc
    (coprod.inl ≫ coprod.inl)
    (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) }

lemma coprod.pentagon (W X Y Z : C) :
  coprod.map ((coprod.associator W X Y).hom) (𝟙 Z) ≫
      (coprod.associator W (X ⨿ Y) Z).hom ≫ coprod.map (𝟙 W) ((coprod.associator X Y Z).hom) =
    (coprod.associator (W ⨿ X) Y Z).hom ≫ (coprod.associator W X (Y ⨿ Z)).hom :=
by tidy

lemma coprod.associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
  coprod.map (coprod.map f₁ f₂) f₃ ≫ (coprod.associator Y₁ Y₂ Y₃).hom =
    (coprod.associator X₁ X₂ X₃).hom ≫ coprod.map f₁ (coprod.map f₂ f₃) :=
by tidy

variables [has_initial.{v} C]

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simps] def coprod.left_unitor
  (P : C) : ⊥_ C ⨿ P ≅ P :=
{ hom := coprod.desc (initial.to P) (𝟙 _),
  inv := coprod.inr }

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simps] def coprod.right_unitor
  (P : C) : P ⨿ ⊥_ C ≅ P :=
{ hom := coprod.desc (𝟙 _) (initial.to P),
  inv := coprod.inl }

lemma coprod.triangle (X Y : C) :
  (coprod.associator X (⊥_ C) Y).hom ≫ coprod.map (𝟙 X) ((coprod.left_unitor Y).hom) =
    coprod.map ((coprod.right_unitor X).hom) (𝟙 Y) :=
by tidy

end

end category_theory.limits
