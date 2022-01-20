/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Andrew Yang
-/
import category_theory.monoidal.functor

/-!
# Endofunctors as a monoidal category.

We give the monoidal category structure on `C ⥤ C`,
and show that when `C` itself is monoidal, it embeds via a monoidal functor into `C ⥤ C`.

## TODO

Can we use this to show coherence results, e.g. a cheap proof that `λ_ (𝟙_ C) = ρ_ (𝟙_ C)`?
I suspect this is harder than is usually made out.
-/

universes v u

namespace category_theory

variables (C : Type u) [category.{v} C]

/--
The category of endofunctors of any category is a monoidal category,
with tensor product given by composition of functors
(and horizontal composition of natural transformations).
-/
def endofunctor_monoidal_category : monoidal_category (C ⥤ C) :=
{ tensor_obj   := λ F G, F ⋙ G,
  tensor_hom   := λ F G F' G' α β, α ◫ β,
  tensor_unit  := 𝟭 C,
  associator   := λ F G H, functor.associator F G H,
  left_unitor  := λ F, functor.left_unitor F,
  right_unitor := λ F, functor.right_unitor F, }.

open category_theory.monoidal_category

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category

/--
Tensoring on the right gives a monoidal functor from `C` into endofunctors of `C`.
-/
@[simps]
def tensoring_right_monoidal [monoidal_category.{v} C] : monoidal_functor C (C ⥤ C) :=
{ ε := (right_unitor_nat_iso C).inv,
  μ := λ X Y,
  { app := λ Z, (α_ Z X Y).hom,
    naturality' := λ Z Z' f, by { dsimp, rw associator_naturality, simp, } },
  μ_natural' := λ X Y X' Y' f g, by { ext Z, dsimp, simp [associator_naturality], },
  associativity' := λ X Y Z, by { ext W, dsimp, simp [pentagon], },
  left_unitality' := λ X, by { ext Y, dsimp, rw [category.id_comp, triangle, ←tensor_comp], simp, },
  right_unitality' := λ X,
  begin
    ext Y, dsimp,
    rw [tensor_id, category.comp_id, right_unitor_tensor_inv, category.assoc, iso.inv_hom_id_assoc,
      ←id_tensor_comp, iso.inv_hom_id, tensor_id],
  end,
  ε_is_iso := by apply_instance,
  μ_is_iso := λ X Y,
    -- We could avoid needing to do this explicitly by
    -- constructing a partially applied analogue of `associator_nat_iso`.
  ⟨⟨{ app := λ Z, (α_ Z X Y).inv,
      naturality' := λ Z Z' f, by { dsimp, rw ←associator_inv_naturality, simp, } },
    by tidy⟩⟩,
  ..tensoring_right C }.

variable {C}
variables {M : Type*} [category M] [monoidal_category M] (F : monoidal_functor M (C ⥤ C))

@[simp, reassoc]
lemma μ_hom_inv_app (i j : M) (X : C) :
  (F.μ i j).app X ≫ (F.μ_iso i j).inv.app X = 𝟙 _ := (F.μ_iso i j).hom_inv_id_app X

@[simp, reassoc]
lemma μ_inv_hom_app (i j : M) (X : C) :
   (F.μ_iso i j).inv.app X ≫ (F.μ i j).app X = 𝟙 _ := (F.μ_iso i j).inv_hom_id_app X

@[simp, reassoc]
lemma ε_hom_inv_app (X : C) :
  F.ε.app X ≫ F.ε_iso.inv.app X = 𝟙 _ := F.ε_iso.hom_inv_id_app X

@[simp, reassoc]
lemma ε_inv_hom_app (X : C) :
  F.ε_iso.inv.app X ≫ F.ε.app X = 𝟙 _ := F.ε_iso.inv_hom_id_app X

@[simp, reassoc]
lemma ε_naturality {X Y : C} (f : X ⟶ Y) :
  F.ε.app X ≫ (F.obj (𝟙_M)).map f = f ≫ F.ε.app Y := (F.ε.naturality f).symm

@[simp, reassoc]
lemma ε_inv_naturality {X Y : C} (f : X ⟶ Y) :
  (F.obj (𝟙_M)).map f ≫ F.ε_iso.inv.app Y = F.ε_iso.inv.app X ≫ f :=
F.ε_iso.inv.naturality f

@[simp, reassoc]
lemma μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
  (F.obj n).map ((F.obj m).map f) ≫ (F.μ m n).app Y = (F.μ m n).app X ≫ (F.obj _).map f :=
(F.to_lax_monoidal_functor.μ m n).naturality f

-- This is a simp lemma in the reverse direction via `nat_trans.naturality`.
@[reassoc]
lemma μ_inv_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
  (F.μ_iso m n).inv.app X ≫ (F.obj n).map ((F.obj m).map f) =
    (F.obj _).map f ≫ (F.μ_iso m n).inv.app Y :=
((F.μ_iso m n).inv.naturality f).symm

-- This is not a simp lemma since it could be proved by the lemmas later.
@[reassoc]
lemma μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) :
  (F.map g).app ((F.obj m).obj X) ≫ (F.obj n').map ((F.map f).app X) ≫ (F.μ m' n').app X =
    (F.μ m n).app X ≫ (F.map (f ⊗ g)).app X :=
begin
  have := congr_app (F.to_lax_monoidal_functor.μ_natural f g) X,
  dsimp at this,
  simpa using this,
end

@[simp, reassoc]
lemma μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
  (F.obj n).map ((F.map f).app X) ≫ (F.μ m' n).app X =
    (F.μ m n).app X ≫ (F.map (f ⊗ 𝟙 n)).app X :=
begin
  rw ← μ_naturality₂ F f (𝟙 n) X,
  simp,
end

@[simp, reassoc]
lemma μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
  (F.map g).app ((F.obj m).obj X) ≫ (F.μ m n').app X =
    (F.μ m n).app X ≫ (F.map (𝟙 m ⊗ g)).app X :=
begin
  rw ← μ_naturality₂ F (𝟙 m) g X,
  simp,
end

@[simp, reassoc]
lemma μ_inv_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
  (F.μ_iso m n).inv.app X ≫ (F.obj n).map ((F.map f).app X) =
    (F.map (f ⊗ 𝟙 n)).app X ≫ (F.μ_iso m' n).inv.app X :=
begin
  rw [← is_iso.comp_inv_eq, category.assoc, ← is_iso.eq_inv_comp],
  simp,
end

@[simp, reassoc]
lemma μ_inv_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
  (F.μ_iso m n).inv.app X ≫ (F.map g).app ((F.obj m).obj X) =
    (F.map (𝟙 m ⊗ g)).app X ≫ (F.μ_iso m n').inv.app X :=
begin
  rw [← is_iso.comp_inv_eq, category.assoc, ← is_iso.eq_inv_comp],
  simp,
end

@[reassoc]
lemma left_unitality_app (n : M) (X : C) :
  (F.obj n).map (F.ε.app X) ≫ (F.μ (𝟙_M) n).app X
    ≫ (F.map (λ_ n).hom).app X = 𝟙 _ :=
begin
  have := congr_app (F.to_lax_monoidal_functor.left_unitality n) X,
  dsimp at this,
  simpa using this.symm,
end

@[reassoc, simp]
lemma obj_ε_app (n : M) (X : C) :
  (F.obj n).map (F.ε.app X) =
    (F.map (λ_ n).inv).app X ≫ (F.μ_iso (𝟙_M) n).inv.app X :=
begin
  refine eq.trans _ (category.id_comp _),
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc],
  convert left_unitality_app F n X,
  { simp },
  { ext, simpa }
end

@[reassoc, simp]
lemma obj_ε_inv_app (n : M) (X : C) :
  (F.obj n).map (F.ε_iso.inv.app X) =
    (F.μ (𝟙_M) n).app X ≫ (F.map (λ_ n).hom).app X  :=
begin
  rw [← cancel_mono ((F.obj n).map (F.ε.app X)), ← functor.map_comp],
  simpa,
end

@[reassoc]
lemma right_unitality_app (n : M) (X : C) :
  F.ε.app ((F.obj n).obj X) ≫ (F.μ n (𝟙_M)).app X ≫ (F.map (ρ_ n).hom).app X = 𝟙 _ :=
begin
  have := congr_app (F.to_lax_monoidal_functor.right_unitality n) X,
  dsimp at this,
  simpa using this.symm,
end

@[simp]
lemma ε_app_obj (n : M) (X : C) :
  F.ε.app ((F.obj n).obj X) =
    (F.map (ρ_ n).inv).app X ≫ (F.μ_iso n (𝟙_M)).inv.app X :=
begin
  refine eq.trans _ (category.id_comp _),
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc],
  convert right_unitality_app F n X,
  { simp },
  { ext, simpa }
end

@[simp]
lemma ε_inv_app_obj (n : M) (X : C) :
  F.ε_iso.inv.app ((F.obj n).obj X) =
    (F.μ n (𝟙_M)).app X ≫ (F.map (ρ_ n).hom).app X :=
begin
  rw [← cancel_mono (F.ε.app ((F.obj n).obj X)), ε_inv_hom_app],
  simpa
end

@[reassoc]
lemma associativity_app (m₁ m₂ m₃: M) (X : C) :
  (F.obj m₃).map ((F.μ m₁ m₂).app X) ≫ (F.μ (m₁ ⊗ m₂) m₃).app X ≫
    (F.map (α_ m₁ m₂ m₃).hom).app X =
  (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫ (F.μ m₁ (m₂ ⊗ m₃)).app X :=
begin
  have := congr_app (F.to_lax_monoidal_functor.associativity m₁ m₂ m₃) X,
  dsimp at this,
  simpa using this,
end

@[reassoc, simp]
lemma obj_μ_app (m₁ m₂ m₃ : M) (X : C) :
  (F.obj m₃).map ((F.μ m₁ m₂).app X) =
  (F.μ m₂ m₃).app ((F.obj m₁).obj X) ≫ (F.μ m₁ (m₂ ⊗ m₃)).app X ≫
    (F.map (α_ m₁ m₂ m₃).inv).app X ≫ (F.μ_iso (m₁ ⊗ m₂) m₃).inv.app X :=
begin
  rw [← associativity_app_assoc],
  dsimp,
  simp,
  dsimp,
  simp,
end

@[reassoc, simp]
lemma obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) :
  (F.obj m₃).map ((F.μ_iso m₁ m₂).inv.app X) =
  (F.μ (m₁ ⊗ m₂) m₃).app X ≫ (F.map (α_ m₁ m₂ m₃).hom).app X ≫
  (F.μ_iso m₁ (m₂ ⊗ m₃)).inv.app X ≫
  (F.μ_iso m₂ m₃).inv.app ((F.obj m₁).obj X) :=
begin
  rw ← is_iso.inv_eq_inv,
  convert obj_μ_app F m₁ m₂ m₃ X using 1,
  { ext, rw ← functor.map_comp, simp },
  { simp only [monoidal_functor.μ_iso_hom, category.assoc, nat_iso.inv_inv_app, is_iso.inv_comp],
    congr,
    { ext, simp },
    { ext, simpa } }
end

@[simp, reassoc]
lemma obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F.obj m).obj Y) :
  (F.obj (𝟙_M)).map f ≫ (F.μ m (𝟙_M)).app _ =
    F.ε_iso.inv.app _ ≫ f ≫ (F.map (ρ_ m).inv).app _ :=
begin
  rw [← is_iso.inv_comp_eq, ← is_iso.comp_inv_eq],
  simp,
end

@[simp]
lemma obj_μ_zero_app (m₁ m₂ : M) (X : C) :
  (F.obj m₂).map ((F.μ m₁ (𝟙_M)).app X) =
  (F.μ (𝟙_M) m₂).app ((F.obj m₁).obj X) ≫ (F.map (λ_ m₂).hom).app ((F.obj m₁).obj X) ≫
    (F.obj m₂).map ((F.map (ρ_ m₁).inv).app X) :=
begin
  rw [← obj_ε_inv_app_assoc, ← functor.map_comp],
  congr, simp,
end

/-- If `m ⊗ n ≅ 𝟙_M`, then `F.obj m` is a left inverse of `F.obj n`. -/
@[simps] noncomputable
def unit_of_tensor_iso_unit (m n : M) (h : m ⊗ n ≅ 𝟙_M) : F.obj m ⋙ F.obj n ≅ 𝟭 C :=
F.μ_iso m n ≪≫ F.to_functor.map_iso h ≪≫ F.ε_iso.symm

/-- If `m ⊗ n ≅ 𝟙_M` and `n ⊗ m ≅ 𝟙_M` (subject to some commuting constraints),
  then `F.obj m` and `F.obj n` forms a self-equivalence of `C`. -/
@[simps] noncomputable
def equiv_of_tensor_iso_unit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_M) (h₂ : n ⊗ m ≅ 𝟙_M)
  (H : (h₁.hom ⊗ 𝟙 m) ≫ (λ_ m).hom = (α_ m n m).hom ≫ (𝟙 m ⊗ h₂.hom) ≫ (ρ_ m).hom) : C ≌ C :=
{ functor := F.obj m,
  inverse := F.obj n,
  unit_iso := (unit_of_tensor_iso_unit F m n h₁).symm,
  counit_iso := unit_of_tensor_iso_unit F n m h₂,
  functor_unit_iso_comp' :=
  begin
    intro X,
    dsimp,
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, ε_inv_app_obj, category.assoc,
      obj_μ_inv_app, functor.map_comp, μ_inv_hom_app_assoc, obj_ε_app,
      unit_of_tensor_iso_unit_inv_app],
    simp [← nat_trans.comp_app, ← F.to_functor.map_comp, ← H, - functor.map_comp]
  end }

end category_theory
