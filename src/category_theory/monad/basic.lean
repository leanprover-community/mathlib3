/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Adam Topaz
-/
import category_theory.functor_category
import category_theory.fully_faithful

namespace category_theory
open category

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables (C : Type u₁) [category.{v₁} C]

/--
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
structure monad extends C ⥤ C :=
(η' [] : 𝟭 _ ⟶ to_functor)
(μ' [] : to_functor ⋙ to_functor ⟶ to_functor)
(assoc' : ∀ X : C, to_functor.map (nat_trans.app μ' X) ≫ μ'.app _ = μ'.app (to_functor.obj X) ≫ μ'.app _ . obviously)
(left_unit' : ∀ X : C, η'.app (to_functor.obj X) ≫ μ'.app _ = 𝟙 _ . obviously)
(right_unit' : ∀ X : C, to_functor.map (η'.app X) ≫ μ'.app _ = 𝟙 _ . obviously)

/--
The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
structure comonad :=
(G : C ⥤ C)
(ε [] : G ⟶ 𝟭 _)
(δ [] : G ⟶ (G ⋙ G))
(coassoc' : ∀ X : C, nat_trans.app δ _ ≫ G.map (δ.app X) = δ.app _ ≫ δ.app _ . obviously)
(left_counit' : ∀ X : C, δ.app X ≫ ε.app (G.obj X) = 𝟙 _ . obviously)
(right_counit' : ∀ X : C, δ.app X ≫ G.map (ε.app X) = 𝟙 _ . obviously)

restate_axiom comonad.coassoc'
restate_axiom comonad.left_counit'
restate_axiom comonad.right_counit'
attribute [simp, reassoc] comonad.left_counit comonad.right_counit

notation `ε_` := comonad.ε
notation `δ_` := comonad.δ

instance coe_monad : has_coe (monad C) (C ⥤ C) := ⟨λ T, T.to_functor⟩
instance coe_comonad : has_coe (comonad C) (C ⥤ C) := ⟨λ G, G.G⟩

@[simp] lemma monad_to_functor_eq_coe (T : monad C) : T.to_functor = T := rfl

variables {C}

def monad.η (T : monad C) : 𝟭 _ ⟶ (T : C ⥤ C) := T.η'
def monad.μ (T : monad C) : (T : C ⥤ C) ⋙ (T : C ⥤ C) ⟶ T := T.μ'

notation `η_` := monad.η
notation `μ_` := monad.μ

lemma monad.assoc (T : monad C) (X : C) :
  (T : C ⥤ C).map (T.μ.app X) ≫ T.μ.app _ = T.μ.app _ ≫ T.μ.app _ :=
T.assoc' X

@[simp, reassoc] lemma monad.left_unit (T : monad C) (X : C) :
  T.η.app ((↑T : C ⥤ C).obj X) ≫ T.μ.app X = 𝟙 ((↑T : C ⥤ C).obj X) :=
T.left_unit' X

@[simp, reassoc] lemma monad.right_unit (T : monad C) (X : C) :
  (T : C ⥤ C).map (T.η.app X) ≫ T.μ.app X = 𝟙 ((↑T : C ⥤ C).obj X) :=
T.right_unit' X

-- abbreviation monad.obj (M : monad C) := (M : C ⥤ C).obj
-- abbreviation monad.map (M : monad C) := (M : C ⥤ C).map

-- abbreviation comonad.obj (M : comonad C) := M.G.obj
-- abbreviation comonad.map (M : comonad C) := M.G.map

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
structure monad_hom (M N : monad C) extends nat_trans (M : C ⥤ C) N :=
(app_η' : ∀ {X}, (η_ M).app X ≫ app X = (η_ N).app X . obviously)
(app_μ' : ∀ {X}, (μ_ M).app X ≫ app X = ((M : C ⥤ C).map (app X) ≫ app (N.obj X)) ≫ (μ_ N).app X . obviously)

-- /-- A morphisms of comonads is a natural transformation compatible with η and μ. -/
-- structure comonad_hom (M N : C ⥤ C) [comonad M] [comonad N] extends nat_trans M N :=
-- (app_ε' : ∀ {X}, app X ≫ (ε_ N).app X = (ε_ M).app X . obviously)
-- (app_δ' : ∀ {X}, app X ≫ (δ_ N).app X = (δ_ M).app X ≫ app (M.obj X) ≫ N.map (app X) . obviously)

restate_axiom monad_hom.app_η'
restate_axiom monad_hom.app_μ'
attribute [simp, reassoc] monad_hom.app_η monad_hom.app_μ

instance : category (monad C) :=
{ hom := monad_hom,
  id := λ M, { to_nat_trans := 𝟙 (M : C ⥤ C) },
  comp := λ M N L f g,
  { to_nat_trans := { app := λ X, f.app X ≫ g.app X } } }

instance {M : monad C} : inhabited (monad_hom M M) := ⟨𝟙 M⟩

-- /--
-- We use this rather than `to_nat_trans` because `to_nat_trans` returns a `monad_hom` and Lean
-- struggles to unify this with `⟶` sometimes.
-- -/
-- def has_hom.hom.as_nat_trans {T₁ T₂ : monad C} (f : T₁ ⟶ T₂) : ↑T₁ ⟶ (↑T₂ : C ⥤ C) :=
-- f.to_nat_trans

-- @[simp] lemma to_nat_trans_eq_as_nat_trans {T₁ T₂ : monad C} (f : T₁ ⟶ T₂) :
--   f.to_nat_trans = f.as_nat_trans := rfl

@[simp] lemma id_as_nat_trans (T : monad C) : (𝟙 T : T ⟶ T).to_nat_trans = 𝟙 (T : C ⥤ C) := rfl
@[simp] lemma comp_to_nat_trans {T₁ T₂ T₃ : monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
  (f ≫ g).to_nat_trans =
    ((f.to_nat_trans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.to_nat_trans : (T₁ : C ⥤ C) ⟶ T₃) :=
rfl

-- -- restate_axiom monad_hom.app_η'
-- -- restate_axiom monad_hom.app_μ'
-- -- attribute [simp, reassoc] monad_hom.app_η monad_hom.app_μ

-- @[simp, reassoc] lemma monad_hom.app_η {M N : monad C} (h : M ⟶ N) {X} :
--   (η_ M).app X ≫ h.app X = sorry :=
-- begin

-- end

variable (C)

@[simps]
def monad_to_functor : monad C ⥤ (C ⥤ C) :=
{ obj := λ T, T,
  map := λ M N f, f.to_nat_trans }

instance : faithful (monad_to_functor C) := {}.

variable {C}

@[simps {rhs_md := semireducible}]
def iso.to_nat_iso {M N : monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
(monad_to_functor C).map_iso h

-- namespace comonad_hom
-- variables {M N L K : C ⥤ C} [comonad M] [comonad N] [comonad L] [comonad K]

-- @[ext]
-- theorem ext (f g : comonad_hom M N) :
--   f.to_nat_trans = g.to_nat_trans → f = g := by {cases f, cases g, simp}

-- restate_axiom comonad_hom.app_ε'
-- restate_axiom comonad_hom.app_δ'
-- attribute [simp, reassoc] comonad_hom.app_ε comonad_hom.app_δ

-- variable (M)
-- /-- The identity natural transformations is a morphism of comonads. -/
-- def id : comonad_hom M M := { ..𝟙 M }
-- variable {M}

-- instance : inhabited (comonad_hom M M) := ⟨id _⟩

-- /-- The composition of two morphisms of comonads. -/
-- def comp (f : comonad_hom M N) (g : comonad_hom N L) : comonad_hom M L :=
-- { app := λ X, f.app X ≫ g.app X }

-- @[simp] lemma id_comp (f : comonad_hom M N) : (comonad_hom.id M).comp f = f :=
-- by {ext, apply id_comp}
-- @[simp] lemma comp_id (f : comonad_hom M N) : f.comp (comonad_hom.id N) = f :=
-- by {ext, apply comp_id}
-- /-- Note: `category_theory.monad.bundled` provides a category instance for bundled comonads.-/
-- @[simp] lemma assoc (f : comonad_hom M N) (g : comonad_hom N L) (h : comonad_hom L K) :
--   (f.comp g).comp h = f.comp (g.comp h) := by {ext, apply assoc}

-- end comonad_hom

namespace monad

variable (C)

@[simps]
def id : monad C :=
{ to_functor := 𝟭 _,
  η' := 𝟙 _,
  μ' := 𝟙 _ }

end monad

namespace comonad

def id : comonad C :=
{ G := 𝟭 _,
  ε := 𝟙 _,
  δ := 𝟙_ }

end comonad

end category_theory
