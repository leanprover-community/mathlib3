/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.shapes.terminal
import category_theory.discrete_category
import data.equiv.fin

/-!
# Pullbacks

We define a category `walking_pair`, which is the index category
for a binary (co)product diagram. A convenience method `pair X Y`
constructs the functor from the walking pair, hitting the given objects.

We define `prod X Y` and `coprod X Y` as limits and colimits of such functors.

Typeclasses `has_binary_products` and `has_binary_coproducts` assert the existence
of (co)limits shaped as walking pairs.
-/

universes v u

open category_theory enumerable

namespace category_theory.limits

/-- The type of objects for the diagram indexing a binary (co)product. -/
@[derive decidable_eq]
inductive walking_pair : Type v
| left | right

instance fintype_walking_pair : enumerable walking_pair :=
enumerable.of_list [walking_pair.left, walking_pair.right]
(λ x, by { cases x; simp })

def pair_function {C : Type u} (X Y : C) : walking_pair → C
| walking_pair.left := X
| walking_pair.right := Y

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

def pair (X Y : C) : discrete walking_pair ⥤ C :=
functor.of_function (pair_function X Y)

@[simp] lemma pair_obj_left (X Y : C) : (pair X Y).obj walking_pair.left = X := rfl
@[simp] lemma pair_obj_right (X Y : C) : (pair X Y).obj walking_pair.right = Y := rfl

def map_pair {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : pair W X ⟶ pair Y Z :=
{ app := λ j, match j with
  | walking_pair.left := f
  | walking_pair.right := g
  end }

@[simp] lemma map_pair_left {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : (map_pair f g).app walking_pair.left = f := rfl
@[simp] lemma map_pair_right {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) : (map_pair f g).app walking_pair.right = g := rfl

@[simp] lemma map_pair_id {X Y : C} : map_pair (𝟙 X) (𝟙 Y) = 𝟙 (pair X Y) :=
by ext ⟨ ⟩; refl

@[simp] lemma map_pair_comp {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
  (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (g₀ : Y₀ ⟶ Y₁) (g₁ : Y₁ ⟶ Y₂)  :
  map_pair (f₀ ≫ f₁) (g₀ ≫ g₁) = map_pair f₀ g₀ ≫ map_pair f₁ g₁ :=
by ext ⟨ ⟩; refl

abbreviation binary_fan (X Y : C) := cone (pair X Y)
abbreviation binary_cofan (X Y : C) := cocone (pair X Y)

variables {X Y : C}

def binary_fan.mk {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : binary_fan X Y :=
{ X := P,
  π := { app := λ j, walking_pair.cases_on j π₁ π₂ }}
def binary_cofan.mk {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : binary_cofan X Y :=
{ X := P,
  ι := { app := λ j, walking_pair.cases_on j ι₁ ι₂ }}

@[simp] lemma binary_fan.mk_π_app_left {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.left = π₁ := rfl
@[simp] lemma binary_fan.mk_π_app_right {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) :
  (binary_fan.mk π₁ π₂).π.app walking_pair.right = π₂ := rfl
@[simp] lemma binary_cofan.mk_π_app_left {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.left = ι₁ := rfl
@[simp] lemma binary_cofan.mk_π_app_right {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) :
  (binary_cofan.mk ι₁ ι₂).ι.app walking_pair.right = ι₂ := rfl

abbreviation prod (X Y : C) [has_limit (pair X Y)] := limit (pair X Y)
abbreviation coprod (X Y : C) [has_colimit (pair X Y)] := colimit (pair X Y)

notation X `×'`:20 Y:20 := prod X Y
notation X `⊕'`:20 Y:20 := coprod X Y

abbreviation prod.fst {X Y : C} [has_limit (pair X Y)] : X ×' Y ⟶ X :=
limit.π (pair X Y) walking_pair.left
abbreviation prod.snd {X Y : C} [has_limit (pair X Y)] : X ×' Y ⟶ Y :=
limit.π (pair X Y) walking_pair.right
abbreviation coprod.inl {X Y : C} [has_colimit (pair X Y)] : X ⟶ X ⊕' Y :=
colimit.ι (pair X Y) walking_pair.left
abbreviation coprod.inr {X Y : C} [has_colimit (pair X Y)] : Y ⟶ X ⊕' Y :=
colimit.ι (pair X Y) walking_pair.right

@[extensionality]
lemma prod.ext {X Y Z : C} [has_limit (pair X Y)] {f g : Z ⟶ prod X Y}
  (h₀ : f ≫ prod.fst _ _ = g ≫ prod.fst _ _)
  (h₁ : f ≫ prod.snd _ _ = g ≫ prod.snd _ _) :
  f = g :=
by ext ⟨ ⟩; assumption

abbreviation prod.lift {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ×' Y :=

limit.lift _ (binary_fan.mk f g)
abbreviation coprod.desc {W X Y : C} [has_colimit (pair X Y)] (f : X ⟶ W) (g : Y ⟶ W) : X ⊕' Y ⟶ W :=
colimit.desc _ (binary_cofan.mk f g)

@[simp] lemma prod.lift_fst {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) :
  prod.lift f g ≫ prod.fst _ _ = f := limit.lift_π _ _

@[simp] lemma prod.lift_snd {W X Y : C} [has_limit (pair X Y)] (f : W ⟶ X) (g : W ⟶ Y) :
  prod.lift f g ≫ prod.snd _ _ = g := limit.lift_π _ _

abbreviation prod.diag {X : C} [has_limit (pair X X)] : X ⟶ prod X X := prod.lift (𝟙 _) (𝟙 _)
abbreviation coprod.diag {X : C} [has_colimit (pair X X)] : coprod X X ⟶ X := coprod.desc (𝟙 _) (𝟙 _)

abbreviation prod.map {W X Y Z : C} [has_limits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ×' X ⟶ Y ×' Z :=
lim.map (map_pair f g)

abbreviation coprod.map {W X Y Z : C} [has_colimits_of_shape.{v} (discrete walking_pair) C]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊕' X ⟶ Y ⊕' Z :=
colim.map (map_pair f g)

variables (C)

class has_binary_products :=
(has_limits_of_shape : has_limits_of_shape.{v} (discrete walking_pair) C)
class has_binary_coproducts :=
(has_colimits_of_shape : has_colimits_of_shape.{v} (discrete walking_pair) C)

attribute [instance] has_binary_products.has_limits_of_shape has_binary_coproducts.has_colimits_of_shape

instance [has_finite_products.{v} C] : has_binary_products.{v} C :=
{ has_limits_of_shape := by apply_instance }
instance [has_finite_coproducts.{v} C] : has_binary_coproducts.{v} C :=
{ has_colimits_of_shape := by apply_instance }

section
-- TODO The `@[simp] def`s below should probably instead have appropriate simp lemmas written.

structure binary_product_spec :=
(prod : C → C → C)
(map : Π {X X' Y Y'} (f : X ⟶ Y) (g : X' ⟶ Y'), prod X X' ⟶ prod Y Y')
(map_id : Π {X X'}, map (𝟙 X) (𝟙 X') = 𝟙 _)
(map_comp : Π {X₀ X₁ Y₀ Y₁ Z₀ Z₁} (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
              (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁),
              map f₀ f₁ ≫ map g₀ g₁ = map (f₀ ≫ g₀) (f₁ ≫ g₁))
(Δ : Π X, X ⟶ prod X X)
(π₀ : Π X Y, prod X Y ⟶ X)
(π₁ : Π X Y, prod X Y ⟶ Y)
(h₀ : Π {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), map f g ≫ π₀ Y Y' = π₀ X X' ≫ f)
(h₁ : Π {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), map f g ≫ π₁ Y Y' = π₁ X X' ≫ g)
(h₂ : Π X, Δ X ≫ π₀ X X = 𝟙 _)
(h₃ : Π X, Δ X ≫ π₁ X X = 𝟙 _)
(h₄ : Π X Y, Δ (prod X Y) ≫ map (π₀ X Y) (π₁ X Y) = 𝟙 _)
(h₅ : Π {X Y} (f : X ⟶ Y), Δ X ≫ map f f = f ≫ Δ Y)

open binary_product_spec

attribute [simp, reassoc] h₀ h₁ h₂ h₃ h₄ h₅

variables {C}

section binary_prod_spec

variable S : binary_product_spec.{v} C
include S

@[extensionality]
lemma binary_product_spec.ext {X Y Z : C} (f g : X ⟶ S.prod Y Z)
  (h₀ : f ≫ S.π₀ _ _ = g ≫ S.π₀ _ _)
  (h₁ : f ≫ S.π₁ _ _ = g ≫ S.π₁ _ _) :
  f = g :=
begin
  suffices : f ≫ S.Δ (S.prod Y Z) ≫ S.map (S.π₀ Y Z) (S.π₁ Y Z) =
             g ≫ S.Δ (S.prod Y Z) ≫ S.map (S.π₀ Y Z) (S.π₁ Y Z),
  { simpa [S.h₄] using this, },
  iterate 2 { rw [← category.assoc,← S.h₅] },
  iterate 2 { rw [category.assoc,S.map_comp] },
  rw [h₀,h₁]
end

def binary_products.cone (F : discrete walking_pair ⥤ C) : cone F :=
{ X := S.prod (F.obj walking_pair.left) (F.obj walking_pair.right),
  π := { app := λ X, walking_pair.cases_on X (S.π₀ _ _) (S.π₁ _ _) } }

def binary_products.is_limit (F : discrete walking_pair ⥤ C) :
  is_limit (binary_products.cone S F) :=
{ lift := (λ s, S.Δ _ ≫ S.map (s.π.app _) (s.π.app _)),
  uniq' := by { tidy; rw ← w; refl },
  fac' := λ s j,
    by { cases j; obviously,
         { erw [S.h₀,← category.assoc,h₂,category.id_comp] },
         { erw [h₁,← category.assoc,h₃,category.id_comp] }, } }

def mk_binary_products : has_binary_products.{v} C :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone := binary_products.cone S F,
      is_limit := binary_products.is_limit S F } } }

end binary_prod_spec

variables [has_binary_products.{v} C]

local attribute [tidy] tactic.case_bash

def cone.unit (F : discrete punit ⥤ C) : cone F :=
{ X := F.obj punit.star, π := { app := λ ⟨ ⟩, 𝟙 _ } }

def is_limit.unit (F : discrete punit.{v+1} ⥤ C) : limits.is_limit (cone.unit F) :=
{ lift := λ s, s.π.app _,
  fac' := λ s ⟨ ⟩, category.comp_id _ _,
  uniq' := λ s m h, by erw [← h,category.comp_id] }

def cone.option {A} (F : discrete (option A) ⥤ C) (s : cone (functor.of_function some ⋙ F)) : cone F :=
{ X := prod s.X (F.obj none),
  π := { app := λ X, option.cases_on X (prod.snd _ _) (λ val, prod.fst _ _ ≫ s.π.app _) } }

instance is_limit.option {A} (F : discrete (option A) ⥤ C) (s : cone $ functor.of_function some ⋙ F) [h : is_limit s] : is_limit (cone.option F s) :=
{ lift := λ s', prod.lift (h.lift (cone.whisker (functor.of_function some) s')) (s'.π.app none),
  fac' := λ s, by { rintro ⟨ ⟩; dsimp [cone.option]; simp, refl },
  uniq' := λ s' m h',
    by { ext ⟨ ⟩; simp *,
         { apply h.uniq (limits.cone.whisker (functor.of_function some) s'),
           intro j,
           rw category.assoc, apply h' (some j) },
         { apply h' none } } }

instance punit.has_limits_of_shape : limits.has_limits_of_shape.{v} (discrete punit) C :=
{ has_limit := λ F, { cone := cone.unit F, is_limit := is_limit.unit F } }

def option.limits.has_limits {A} (F : discrete (option A) ⥤ C)
  [limits.has_limit.{v} $ functor.of_function some ⋙ F] :
  limits.has_limit.{v} F :=
{ cone := cone.option F (limits.has_limit.cone _),
  is_limit := @is_limit.option _ _ _ _ _ _ (limits.has_limit.is_limit _) }

instance option.limits.has_limits_of_shape {A : Type v}
  [limits.has_limits_of_shape.{v} (discrete A) C] :
  limits.has_limits_of_shape.{v} (discrete (option A)) C :=
{ has_limit := λ F, option.limits.has_limits F }

instance fin.limits.has_limits_of_shape [has_terminal.{v} C] {n : ℕ} :
  limits.has_limits_of_shape.{v} (discrete (ulift (fin n))) C :=
begin
  induction n with n,
  { have : pempty ≃ ulift (fin 0), symmetry,
    calc  ulift (fin 0)
        ≃ fin 0  : equiv.ulift
    ... ≃ pempty : fin_zero_equiv_pempty,
    have : pempty ≌ discrete (ulift $ fin 0) :=
         equivalence.trans (functor.as_equivalence (functor.empty (discrete pempty)))
                           (discrete.equivalence_of_equiv this),
    refine has_limits_of_shape_of_equivalence this },
  { have : option.{v} (ulift.{v 0} (fin n)) ≃ ulift.{v 0} (fin (nat.succ n)),
    calc  option.{v} (ulift (fin n))
        ≃ option (fin n)               :
            @ufunctor.map_equiv option.{v} option.{0} _ (ulift $ fin n) (fin n) (@equiv.ulift (fin n))
    ... ≃ fin n.succ                   : option_equiv_fin
    ... ≃ ulift.{v} (fin (nat.succ n)) : equiv.ulift.symm,
    resetI,
    refine has_limits_of_shape_of_equivalence (discrete.equivalence_of_equiv this) }
end

/-- The braiding isomorphism which swaps a binary product. -/
@[simp] def prod.braiding (P Q : C) : P ×' Q ≅ Q ×' P :=
{ hom := prod.lift prod.snd prod.fst,
  inv := prod.lift prod.snd prod.fst }

/-- The braiding isomorphism is symmetric. -/
@[simp] lemma prod.symmetry (P Q : C) :
  (prod.braiding P Q).hom ≫ (prod.braiding Q P).hom = 𝟙 _ :=
by tidy

/-- The associator isomorphism for binary products. -/
@[simp] def prod.associator
  (P Q R : C) : (P ×' Q) ×' R ≅ P ×' (Q ×' R) :=
{ hom :=
  prod.lift
    (prod.fst ≫ prod.fst)
    (prod.lift (prod.fst ≫ prod.snd) prod.snd),
  inv :=
  prod.lift
    (prod.lift prod.fst (prod.snd ≫ prod.fst))
    (prod.snd ≫ prod.snd) }

variables [has_terminal.{v} C]

def mk_has_finite_product : has_finite_products.{v} C :=
{ has_limits_of_shape :=
  begin
    introsI,
    have : discrete (ulift.{v} (fin (card J))) ≌ discrete J :=
      discrete.equivalence_of_equiv (equiv.ulift.trans (enumerable.equiv J).symm),
    exact @has_limits_of_shape_of_equivalence _ _ C 𝒞 (discrete J) _
          this (fin.limits.has_limits_of_shape),
  end }

/-- The left unitor isomorphism for binary products with the terminal object. -/
@[simp] def prod.left_unitor
  (P : C) : ⊤_ C ×' P ≅ P :=
{ hom := prod.snd,
  inv := prod.lift (terminal.from P) (𝟙 _) }

/-- The right unitor isomorphism for binary products with the terminal object. -/
@[simp] def prod.right_unitor
  (P : C) : P ×' ⊤_ C ≅ P :=
{ hom := prod.fst,
  inv := prod.lift (𝟙 _) (terminal.from P) }
end

section

structure binary_coproduct_spec :=
(prod : C → C → C)
(map : Π {X X' Y Y'} (f : X ⟶ Y) (g : X' ⟶ Y'), prod X X' ⟶ prod Y Y')
(map_id : Π {X X'}, map (𝟙 X) (𝟙 X') = 𝟙 _)
(map_comp : Π {X₀ X₁ Y₀ Y₁ Z₀ Z₁} (f₀ : X₀ ⟶ Y₀) (g₀ : Y₀ ⟶ Z₀)
              (f₁ : X₁ ⟶ Y₁) (g₁ : Y₁ ⟶ Z₁),
              map f₀ f₁ ≫ map g₀ g₁ = map (f₀ ≫ g₀) (f₁ ≫ g₁))
(Δ : Π X, prod X X ⟶ X)
(ι₀ : Π X Y, X ⟶ prod X Y)
(ι₁ : Π X Y, Y ⟶ prod X Y)
(h₀ : Π {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), ι₀ X X' ≫ map f g = f ≫ ι₀ Y Y')
(h₁ : Π {X X' Y Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'), ι₁ X X' ≫ map f g = g ≫ ι₁ Y Y')
(h₂ : Π X, ι₀ X X ≫ Δ X = 𝟙 _)
(h₃ : Π X, ι₁ X X ≫ Δ X = 𝟙 _)
(h₄ : Π X Y, map (ι₀ X Y) (ι₁ X Y) ≫ Δ (prod X Y) = 𝟙 _)
(h₅ : Π {X Y} (f : X ⟶ Y), map f f ≫ Δ Y = Δ X ≫ f)

open binary_coproduct_spec

attribute [simp, reassoc] h₀ h₁ h₂ h₃ h₄ h₅

variables {C}

section binary_coproduct_spec

variable S : binary_coproduct_spec.{v} C
include S

@[extensionality]
lemma binary_coproduct_spec.ext {X Y Z : C} (f g : S.prod X Y ⟶ Z)
  (h₀ : S.ι₀ _ _ ≫ f = S.ι₀ _ _ ≫ g)
  (h₁ : S.ι₁ _ _ ≫ f = S.ι₁ _ _ ≫ g) :
  f = g :=
begin
  suffices : S.map (S.ι₀ X Y) (S.ι₁ X Y) ≫ S.Δ (S.prod X Y) ≫ f =
             S.map (S.ι₀ X Y) (S.ι₁ X Y) ≫ S.Δ (S.prod X Y) ≫ g,
  { simpa [S.h₄] using this, },
  iterate 2 { rw [← S.h₅] },
  iterate 2 { rw [← category.assoc,S.map_comp] },
  rw [h₀,h₁]
end

def binary_coproducts.cocone (F : discrete walking_pair ⥤ C) : cocone F :=
{ X := S.prod (F.obj walking_pair.left) (F.obj walking_pair.right),
  ι := { app := λ X, walking_pair.cases_on X (S.ι₀ _ _) (S.ι₁ _ _) } }

def binary_coproducts.is_colimit (F : discrete walking_pair ⥤ C) :
  is_colimit (binary_coproducts.cocone S F) :=
{ desc := (λ s, S.map (s.ι.app _) (s.ι.app _) ≫ S.Δ _),
  uniq' := by { tidy; rw ← w; refl },
  fac' := λ s j,
    by { cases j, obviously,
         { erw [S.h₀_assoc,S.h₂,category.comp_id] },
         { erw [S.h₁_assoc,S.h₃,category.comp_id] }, } }

def mk_binary_coproducts : has_binary_coproducts.{v} C :=
{ has_colimits_of_shape :=
  { has_colimit := λ F,
    { cocone := binary_coproducts.cocone S F,
      is_colimit := binary_coproducts.is_colimit S F } } }

end binary_coproduct_spec

variables [has_binary_coproducts.{v} C]

def cocone.unit (F : discrete punit ⥤ C) : cocone F :=
{ X := F.obj punit.star, ι := { app := λ ⟨ ⟩, 𝟙 _ } }

def is_colimit.unit (F : discrete punit.{v+1} ⥤ C) : limits.is_colimit (cocone.unit F) :=
{ desc := λ s, s.ι.app _,
  fac' := λ s, punit.rec $ by exact category.id_comp _ _,
  uniq' := λ s m h, by erw [← h,category.id_comp] }

def cocone.option {A} (F : discrete (option A) ⥤ C) (s : cocone (functor.of_function some ⋙ F)) : cocone F :=
{ X := coprod s.X (F.obj none),
  ι := { app := λ X, option.cases_on X (coprod.inr _ _) (λ val, s.ι.app _ ≫ coprod.inl _ _) } }

instance is_colimit.option {A} (F : discrete (option A) ⥤ C) (s : cocone $ functor.of_function some ⋙ F)
  [h : is_colimit s] : is_colimit (cocone.option F s) :=
{ desc := λ s', coprod.desc (h.desc (cocone.whisker (functor.of_function some) s'))
                            (s'.ι.app none),
  fac' := λ s, by { rintro ⟨ ⟩; dsimp [cocone.option]; simp, refl },
  uniq' := λ s' m h',
    by { ext ⟨ ⟩; simp *,
         { apply h.uniq (limits.cocone.whisker (functor.of_function some) s'),
           intro j,
           rw ← category.assoc, apply h' (some j) },
         { apply h' none } } }

def option.limits.has_colimits {A} (F : discrete (option A) ⥤ C)
  [limits.has_colimit.{v} $ functor.of_function some ⋙ F] :
  limits.has_colimit.{v} F :=
{ cocone := cocone.option F (limits.has_colimit.cocone _),
  is_colimit := @is_colimit.option _ _ _ _ _ _ (limits.has_colimit.is_colimit _) }

instance option.limits.has_colimits_of_shape {A : Type v}
  [limits.has_colimits_of_shape.{v} (discrete A) C] :
  limits.has_colimits_of_shape.{v} (discrete (option A)) C :=
{ has_colimit := λ F, option.limits.has_colimits F }

instance fin.limits.has_colimits_of_shape [has_initial.{v} C] {n : ℕ} :
  limits.has_colimits_of_shape.{v} (discrete (ulift (fin n))) C :=
begin
  induction n with n,
  { have : pempty ≃ ulift (fin 0), symmetry,
    calc  ulift (fin 0)
        ≃ fin 0  : equiv.ulift
    ... ≃ pempty : fin_zero_equiv_pempty,
    have : pempty ≌ discrete (ulift $ fin 0) :=
         equivalence.trans (functor.as_equivalence (functor.empty (discrete pempty)))
                           (discrete.equivalence_of_equiv this),
    refine has_colimits_of_shape_of_equivalence this },
  { have : option.{v} (ulift.{v 0} (fin n)) ≃ ulift.{v 0} (fin (nat.succ n)),
    calc  option.{v} (ulift (fin n))
        ≃ option (fin n)               :
            @ufunctor.map_equiv option.{v} option.{0} _ (ulift $ fin n) (fin n) (@equiv.ulift (fin n))
    ... ≃ fin n.succ                   : option_equiv_fin
    ... ≃ ulift.{v} (fin (nat.succ n)) : equiv.ulift.symm,
    resetI,
    refine has_colimits_of_shape_of_equivalence (discrete.equivalence_of_equiv this) }
end

local attribute [tidy] tactic.case_bash

/-- The braiding isomorphism which swaps a binary coproduct. -/
@[simp] def coprod.braiding (P Q : C) : P ⊕' Q ≅ Q ⊕' P :=
{ hom := coprod.desc coprod.inr coprod.inl,
  inv := coprod.desc coprod.inr coprod.inl }

/-- The braiding isomorphism is symmetric. -/
@[simp] lemma coprod.symmetry (P Q : C) :
  (coprod.braiding P Q).hom ≫ (coprod.braiding Q P).hom = 𝟙 _ :=
by tidy

/-- The associator isomorphism for binary coproducts. -/
@[simp] def coprod.associator
  (P Q R : C) : (P ⊕' Q) ⊕' R ≅ P ⊕' (Q ⊕' R) :=
{ hom :=
  coprod.desc
    (coprod.desc coprod.inl (coprod.inl ≫ coprod.inr))
    (coprod.inr ≫ coprod.inr),
  inv :=
  coprod.desc
    (coprod.inl≫ coprod.inl)
    (coprod.desc (coprod.inr ≫ coprod.inl) coprod.inr) }

variables [has_initial.{v} C]

def mk_has_finite_coproduct : has_finite_coproducts.{v} C :=
{ has_colimits_of_shape :=
  begin
    introsI,
    have : discrete (ulift.{v} (fin (enumerable.card J))) ≌ discrete J :=
      discrete.equivalence_of_equiv (equiv.ulift.trans (enumerable.equiv J).symm),
    exact @has_colimits_of_shape_of_equivalence _ _ C 𝒞 (discrete J) _
          this (fin.limits.has_colimits_of_shape),
  end }

/-- The left unitor isomorphism for binary coproducts with the initial object. -/
@[simp] def coprod.left_unitor
  (P : C) : ⊥_ C ⊕' P ≅ P :=
{ hom := coprod.desc (initial.to P) (𝟙 _),
  inv := coprod.inr }

/-- The right unitor isomorphism for binary coproducts with the initial object. -/
@[simp] def coprod.right_unitor
  (P : C) : P ⊕' ⊥_ C ≅ P :=
{ hom := coprod.desc (𝟙 _) (initial.to P),
  inv := coprod.inl }
end

end category_theory.limits
