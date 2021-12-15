/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.monoidal.End
import category_theory.monoidal.discrete

/-!
# Shift

A `shift` on a category is nothing more than an automorphism of the category. An example to
keep in mind might be the category of complexes ⋯ → C_{n-1} → C_n → C_{n+1} → ⋯ with the shift
operator re-indexing the terms, so the degree `n` term of `shift C` would be the degree `n+1`
term of `C`.

-/
namespace category_theory

noncomputable theory

universes v u

variables (C : Type u) (A : Type*) [category.{v} C]

local attribute [instance] endofunctor_monoidal_category
local attribute [reducible] endofunctor_monoidal_category discrete.add_monoidal
variables {M N : Type*} [category M] [category N] [monoidal_category M] [monoidal_category N]

section defs

section
variables {C A}
section monoid
variables [add_monoid A]
variables (F : monoidal_functor (discrete A) (C ⥤ C)) (G : monoidal_functor M N)
variable (F' : monoidal_functor M (C ⥤ C))
section
variables {D : Type*} [category D] {E : Type*} [category E]

@[simp, reassoc] lemma map_hom_inv_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
  (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ :=
by simp [← nat_trans.comp_app, ← functor.map_comp]

@[simp, reassoc] lemma map_inv_hom_app (F : C ⥤ D ⥤ E) {X Y : C} (e : X ≅ Y) (Z : D) :
  (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ :=
by simp [← nat_trans.comp_app, ← functor.map_comp]


end
namespace monoidal_functor

@[simp]
lemma μ_iso_hom (X Y : M) : (G.μ_iso X Y).hom = G.μ X Y := rfl
@[simp]
lemma ε_iso_hom : G.ε_iso.hom = G.ε := rfl

end monoidal_functor

@[simp, reassoc]
lemma μ_hom_inv_app (i j : M) (X : C) :
  (F'.μ i j).app X ≫ (F'.μ_iso i j).inv.app X = 𝟙 _ := (F'.μ_iso i j).hom_inv_id_app X

@[simp, reassoc]
lemma μ_inv_hom_app (i j : M) (X : C) :
   (F'.μ_iso i j).inv.app X ≫ (F'.μ i j).app X = 𝟙 _ := (F'.μ_iso i j).inv_hom_id_app X

@[simp, reassoc]
lemma ε_hom_inv_app (X : C) :
  F'.ε.app X ≫ F'.ε_iso.inv.app X = 𝟙 _ := F'.ε_iso.hom_inv_id_app X

@[simp, reassoc]
lemma ε_inv_hom_app (X : C) :
  F'.ε_iso.inv.app X ≫ F'.ε.app X = 𝟙 _ := F'.ε_iso.inv_hom_id_app X

@[simp, reassoc]
lemma ε_naturality {X Y : C} (f : X ⟶ Y) :
  F'.ε.app X ≫ (F'.obj (𝟙_M)).map f = f ≫ F'.ε.app Y := (F'.ε.naturality f).symm

@[simp, reassoc]
lemma ε_inv_naturality {X Y : C} (f : X ⟶ Y) :
  (F'.obj (𝟙_M)).map f ≫ F'.ε_iso.inv.app Y = F'.ε_iso.inv.app X ≫ f :=
F'.ε_iso.inv.naturality f

@[simp, reassoc]
lemma μ_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
  (F'.obj n).map ((F'.obj m).map f) ≫ (F'.μ m n).app Y = (F'.μ m n).app X ≫ (F'.obj _).map f :=
(F'.to_lax_monoidal_functor.μ m n).naturality f

@[simp, reassoc]
lemma μ_inv_naturality {m n : M} {X Y : C} (f : X ⟶ Y) :
  (F'.μ_iso m n).inv.app X ≫ (F'.obj n).map ((F'.obj m).map f) =
    (F'.obj _).map f ≫ (F'.μ_iso m n).inv.app Y :=
((F'.μ_iso m n).inv.naturality f).symm

@[simp, reassoc]
lemma μ_naturality₂ {m n m' n' : M} (f : m ⟶ m') (g : n ⟶ n') (X : C) :
  (F'.map g).app ((F'.obj m).obj X) ≫ (F'.obj n').map ((F'.map f).app X) ≫ (F'.μ m' n').app X =
    (F'.μ m n).app X ≫ (F'.map (f ⊗ g)).app X :=
begin
  have := congr_app (F'.to_lax_monoidal_functor.μ_natural f g) X,
  dsimp at this,
  simpa using this,
end

@[simp, reassoc]
lemma μ_naturalityₗ {m n m' : M} (f : m ⟶ m') (X : C) :
  (F'.obj n).map((F'.map f).app X) ≫ (F'.μ m' n).app X =
    (F'.μ m n).app X ≫ (F'.map (f ⊗ 𝟙 n)).app X :=
begin
  rw ← μ_naturality₂ F' f (𝟙 n) X,
  simp,
end

@[simp, reassoc]
lemma μ_naturalityᵣ {m n n' : M} (g : n ⟶ n') (X : C) :
  (F'.map g).app ((F'.obj m).obj X) ≫ (F'.μ m n').app X =
    (F'.μ m n).app X ≫ (F'.map (𝟙 m ⊗ g)).app X :=
begin
  rw ← μ_naturality₂ F' (𝟙 m) g X,
  simp,
end

@[reassoc]
lemma left_unitality_app (n : M) (X : C) :
  (F'.obj n).map (F'.ε.app X) ≫ (F'.μ (𝟙_M) n).app X
    ≫ (F'.map (λ_ n).hom).app X = 𝟙 _ :=
begin
  have := congr_app (F'.to_lax_monoidal_functor.left_unitality n) X,
  dsimp at this,
  simpa using this.symm,
end

@[simp]
lemma obj_ε_app (n : M) (X : C) :
  (F'.obj n).map (F'.ε.app X) =
    (F'.map (λ_ n).inv).app X ≫ (F'.μ_iso (𝟙_M) n).inv.app X :=
begin
  refine eq.trans _ (category.id_comp _),
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc],
  convert left_unitality_app F' n X,
  { simp },
  { ext, simpa }
end

@[simp, reassoc]
lemma obj_ε_inv_app (n : M) (X : C) :
  (F'.obj n).map (F'.ε_iso.inv.app X) =
    (F'.μ (𝟙_M) n).app X ≫ (F'.map (λ_ n).hom).app X  :=
begin
  rw [← cancel_mono ((F'.obj n).map (F'.ε.app X)), ← functor.map_comp],
  simpa,
end

@[reassoc]
lemma right_unitality_app (n : M) (X : C) :
  F'.ε.app ((F'.obj n).obj X) ≫ (F'.μ n (𝟙_M)).app X ≫ (F'.map (ρ_ n).hom).app X = 𝟙 _ :=
begin
  have := congr_app (F'.to_lax_monoidal_functor.right_unitality n) X,
  dsimp at this,
  simpa using this.symm,
end

@[simp]
lemma ε_app_obj (n : M) (X : C) :
  F'.ε.app ((F'.obj n).obj X) =
    (F'.map (ρ_ n).inv).app X ≫ (F'.μ_iso n (𝟙_M)).inv.app X :=
begin
  refine eq.trans _ (category.id_comp _),
  rw [← category.assoc, ← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc],
  convert right_unitality_app F' n X,
  { simp },
  { ext, simpa }
end

@[simp]
lemma ε_inv_app_obj (n : M) (X : C) :
  F'.ε_iso.inv.app ((F'.obj n).obj X) =
    (F'.μ n (𝟙_M)).app X ≫ (F'.map (ρ_ n).hom).app X :=
begin
  rw [← cancel_mono (F'.ε.app ((F'.obj n).obj X)), ε_inv_hom_app],
  simpa
end

@[reassoc]
lemma associativity_app (m₁ m₂ m₃: M) (X : C) :
  (F'.obj m₃).map ((F'.μ m₁ m₂).app X) ≫ (F'.μ (m₁ ⊗ m₂) m₃).app X ≫
    (F'.map (α_ m₁ m₂ m₃).hom).app X =
  (F'.μ m₂ m₃).app ((F'.obj m₁).obj X) ≫ (F'.μ m₁ (m₂ ⊗ m₃)).app X :=
begin
  have := congr_app (F'.to_lax_monoidal_functor.associativity m₁ m₂ m₃) X,
  dsimp at this,
  simpa using this,
end

@[simp, reassoc, priority 900]
lemma obj_μ_app (m₁ m₂ m₃ : M) (X : C) :
  (F'.obj m₃).map ((F'.μ m₁ m₂).app X) =
  (F'.μ m₂ m₃).app ((F'.obj m₁).obj X) ≫ (F'.μ m₁ (m₂ ⊗ m₃)).app X ≫
    (F'.map (α_ m₁ m₂ m₃).inv).app X ≫ (F'.μ_iso (m₁ ⊗ m₂) m₃).inv.app X :=
begin
  rw [← associativity_app_assoc],
  dsimp,
  simp,
  dsimp,
  simp,
end

@[simp, reassoc, priority 900]
lemma obj_μ_inv_app (m₁ m₂ m₃ : M) (X : C) :
  (F'.obj m₃).map ((F'.μ_iso m₁ m₂).inv.app X) =
  (F'.μ (m₁ ⊗ m₂) m₃).app X ≫ (F'.map (α_ m₁ m₂ m₃).hom).app X ≫
  (F'.μ_iso m₁ (m₂ ⊗ m₃)).inv.app X ≫
  (F'.μ_iso m₂ m₃).inv.app ((F'.obj m₁).obj X) :=
begin
  rw ← is_iso.inv_eq_inv,
  convert obj_μ_app F' m₁ m₂ m₃ X using 1,
  { ext, rw ← functor.map_comp, simp },
  { simp only [monoidal_functor.μ_iso_hom, category.assoc, nat_iso.inv_inv_app, is_iso.inv_comp],
    congr,
    { ext, simp },
    { ext, simpa } }
end
.

@[simp, reassoc]
lemma obj_zero_map_μ_app {m : M} {X Y : C} (f : X ⟶ (F'.obj m).obj Y) :
  (F'.obj (𝟙_M)).map f ≫ (F'.μ m (𝟙_M)).app _ =
    F'.ε_iso.inv.app _ ≫ f ≫ (F'.map (ρ_ m).inv).app _ :=
begin
  rw [← is_iso.inv_comp_eq, ← is_iso.comp_inv_eq],
  simp,
end

-- @[simp, reassoc] lemma eq_to_hom_μ {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
--   eq_to_hom (by rw [h₁, h₂]) ≫ (F.μ i' j').app X =
--     (F.μ i j).app X ≫ eq_to_hom (by rw [h₁, h₂]) :=
-- by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

-- @[simp, reassoc] lemma μ_inv_eq_to_hom {i j i' j' : A} (h₁ : i = i') (h₂ : j = j') (X : C) :
--   (F.μ_iso i j).inv.app X ≫ eq_to_hom (by rw [h₁, h₂]) =
--     eq_to_hom (by rw [h₁, h₂]) ≫ (F.μ_iso i' j').inv.app X :=
-- by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }


-- local attribute [reassoc] nat_trans.comp_app

@[simp]
lemma obj_μ_zero_app (m₁ m₂ : M) (X : C) :
  (F'.obj m₂).map ((F'.μ m₁ (𝟙_M)).app X) =
  (F'.μ (𝟙_M) m₂).app ((F'.obj m₁).obj X) ≫ (F'.map (λ_ m₂).hom).app ((F'.obj m₁).obj X) ≫
    (F'.obj m₂).map ((F'.map (ρ_ m₁).inv).app X) :=
begin
  rw [← obj_ε_inv_app_assoc, ← functor.map_comp],
  congr, simp,
end

@[simp]
lemma iso_whisker_right_μ_inv_eq (F : monoidal_functor (discrete A) (C ⥤ C)) (i j k : A) :
  iso_whisker_right (F.μ_iso i j).symm (F.obj k) =
    (F.μ_iso (i + j) k) ≪≫ F.to_functor.map_iso (α_ _ _ _) ≪≫ (F.μ_iso i (j + k)).symm ≪≫
      iso_whisker_left (F.obj i) (F.μ_iso j k).symm ≪≫ (functor.associator _ _ _).symm :=
begin
  ext1,
  dsimp,
  simp_rw [← category.assoc],
  rw [← is_iso.comp_inv_eq, ← is_iso.comp_inv_eq, category.assoc, ← is_iso.eq_inv_comp],
  ext,
  simp
end
.

@[simps]
def unit_of_tensor_iso_unit (m n : M) (h : m ⊗ n ≅ 𝟙_M) : F'.obj m ⋙ F'.obj n ≅ 𝟭 C :=
F'.μ_iso m n ≪≫ F'.to_functor.map_iso h ≪≫ F'.ε_iso.symm

.


@[simps]
def equiv_of_tensor_iso_unit (m n : M) (h₁ : m ⊗ n ≅ 𝟙_M) (h₂ : n ⊗ m ≅ 𝟙_M)
  (H : (h₁.hom ⊗ 𝟙 m) ≫ (λ_ m).hom = (α_ m n m).hom ≫ (𝟙 m ⊗ h₂.hom) ≫ (ρ_ m).hom) : C ≌ C :=
{ functor := F'.obj m,
  inverse := F'.obj n,
  unit_iso := (unit_of_tensor_iso_unit F' m n h₁).symm,
  counit_iso := unit_of_tensor_iso_unit F' n m h₂,
  functor_unit_iso_comp' :=
  begin
    intro X,
    dsimp,
    simp only [μ_naturalityᵣ_assoc, μ_naturalityₗ_assoc, ε_inv_app_obj, category.assoc,
      obj_μ_inv_app, functor.map_comp, μ_inv_hom_app_assoc, obj_ε_app,
      unit_of_tensor_iso_unit_inv_app],
    simp [← nat_trans.comp_app, ← F'.to_functor.map_comp, ← H, - functor.map_comp]
  end }


end monoid

section group
variables [add_group A]
variables (F : monoidal_functor (discrete A) (C ⥤ C))

@[simps functor inverse unit_iso_hom unit_iso_inv counit_iso_hom counit_iso_inv]
def add_neg_equiv (n : A) : C ≌ C :=
equiv_of_tensor_iso_unit F n (-n : A)
  (eq_to_iso (add_neg_self n)) (eq_to_iso (neg_add_self n)) (subsingleton.elim _ _)

end group

end

variables [add_monoid A]


variables (C A)

/-- A category has a shift, or translation, if it is equipped with an automorphism. -/
class has_shift (C : Type u) (A : Type*) [category.{v} C] [add_monoid A] :=
(shift : monoidal_functor (discrete A) (C ⥤ C))
-- (shift : Π (i : A), C ⥤ C)
-- (shift_add : Π i j, shift (i + j) ≅ shift i ⋙ shift j)
-- (iso_whisker_right_shift_add : ∀ i j k, iso_whisker_right (shift_add i j) (shift k) =
--   (shift_add (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫ (shift_add i (j+k)) ≪≫
--     iso_whisker_left _ (shift_add j k) ≪≫ (functor.associator _ _ _).symm)
-- (shift_functor_zero : shift 0 ≅ 𝟭 C)


variables [has_shift C A]

def shift_monoidal_functor : monoidal_functor (discrete A) (C ⥤ C) := has_shift.shift

variable {A}

/-- The shift autoequivalence, moving objects and morphisms 'up'. -/
abbreviation shift_functor (i : A) : C ⥤ C := (shift_monoidal_functor C A).obj i

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_functor_add (i j : A) :
  shift_functor C (i + j) ≅ shift_functor C i ⋙ shift_functor C j :=
((shift_monoidal_functor C A).μ_iso i j).symm

lemma iso_whisker_right_shift_functor_add (i j k : A) :
  iso_whisker_right (shift_functor_add C i j) (shift_functor C k) =
  (shift_functor_add C (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫
    (shift_functor_add C i (j+k)) ≪≫
    iso_whisker_left _ (shift_functor_add C j k) ≪≫ (functor.associator _ _ _).symm :=
by { convert iso_whisker_right_μ_inv_eq (shift_monoidal_functor C A) i j k, simp }

variables (A)

/-- Shifting by zero is the identity functor. -/
abbreviation shift_functor_zero : shift_functor C (0 : A) ≅ 𝟭 C :=
(shift_monoidal_functor C A).ε_iso.symm

end defs

-- Any better notational suggestions?
notation X`⟦`n`⟧`:20 := (shift_functor _ n).obj X
notation f`⟦`n`⟧'`:80 := (shift_functor _ n).map f

section examples
variables [has_shift C ℤ]

example {X Y : C} (f : X ⟶ Y) : X⟦(1 : ℤ)⟧ ⟶ Y⟦1⟧ := f⟦1⟧'
example {X Y : C} (f : X ⟶ Y) : X⟦(-2 : ℤ)⟧ ⟶ Y⟦-2⟧ := f⟦-2⟧'

end examples

section add_monoid

variables {C A} [add_monoid A] [has_shift C A] (X Y : C) (f : X ⟶ Y)

@[simp] lemma has_shift.shift_app (n : A) (X : C) : (has_shift.shift.obj n).obj X = X⟦n⟧ := rfl

/-- Shifting by `i + j` is the same as shifting by `i` and then shifting by `j`. -/
abbreviation shift_add (i j : A) : X⟦i + j⟧ ≅ X⟦i⟧⟦j⟧ := (shift_functor_add C i j).app _

-- @[simp] lemma has_shift.shift_add_app (i j : A) :
--   (has_shift.shift_add i j).app X = shift_add X i j := rfl

-- @[simp] lemma shift_functor_add_app (i j : A) :
--   (shift_functor_add C i j).app X = shift_add X i j := rfl

-- @[simp] lemma shift_functor_add_hom_app (i j : A) :
--   (shift_functor_add C i j).hom.app X = (shift_add X i j).hom := rfl

-- @[simp] lemma shift_functor_inv_hom_app (i j : A) :
--   (shift_functor_add C i j).inv.app X = (shift_add X i j).inv := rfl

@[simp]
lemma shift_add' (i j : A) :
  f⟦i + j⟧' = (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' ≫ (shift_add Y i j).inv :=
by { symmetry, apply nat_iso.naturality_2 }

@[reassoc] lemma shift_add_hom_comp (i j : A) :
  (shift_add X i j).hom ≫ f⟦i⟧'⟦j⟧' = f⟦i + j⟧' ≫ (shift_add Y i j).hom :=
by rw [shift_add', category.assoc, category.assoc, iso.inv_hom_id, category.comp_id]

@[simp]
lemma shift_shift_add_hom' (i j k : A) :
  (shift_add X i j).hom⟦k⟧' =
    (shift_add X (i+j) k).inv ≫ (eq_to_hom $ by rw add_assoc) ≫ (shift_add X i (j+k)).hom ≫
      (shift_add (X⟦i⟧) j k).hom :=
begin
  have := congr_arg iso.hom (iso_whisker_right_shift_functor_add C i j k),
  apply_fun (λ α, nat_trans.app α X) at this,
  simpa only [iso_whisker_left_hom, iso_whisker_right_hom, iso.symm_hom, functor.associator_inv_app,
    eq_to_hom_app, whisker_right_app, whisker_left_app, eq_to_iso.hom, category.comp_id,
    iso.trans_hom, nat_trans.comp_app] using this,
end

@[simp]
lemma shift_shift_add_inv' (i j k : A) :
  (shift_add X i j).inv⟦k⟧' =
    (shift_add (X⟦i⟧) j k).inv ≫ (shift_add X i (j+k)).inv ≫ (eq_to_hom $ by rw add_assoc) ≫
      (shift_add X (i+j) k).hom :=
begin
  have := congr_arg iso.inv (iso_whisker_right_shift_functor_add C i j k),
  apply_fun (λ α, nat_trans.app α X) at this,
  simpa only [iso_whisker_right_inv, whisker_right_app, functor.associator_hom_app,
    iso.trans_inv, eq_to_iso.inv, eq_to_hom_app, whisker_left_app, iso.symm_inv, category.id_comp,
    iso_whisker_left_inv, nat_trans.comp_app, category.assoc] using this,
end

lemma shift_functor_map_iso_shift_add (i j k : A) :
  (shift_functor C k).map_iso (shift_add X i j) =
    (shift_add X (i+j) k).symm ≪≫ (eq_to_iso $ by rw add_assoc) ≪≫ (shift_add X i (j+k)) ≪≫
      (shift_add (X⟦i⟧) j k) :=
by { ext, apply shift_shift_add_hom', }

lemma shift_add_assoc (i j k : A) :
  shift_add X (i + j) k =
    eq_to_iso (by rw add_assoc) ≪≫ shift_add X i (j + k) ≪≫
    shift_add _ j k ≪≫ (functor.map_iso _ (shift_add X i j)).symm :=
begin
  ext,
  simp only [iso.symm_hom, eq_to_iso.hom, iso.trans_hom, ← category.assoc],
  rw [iso.eq_comp_inv, ← iso.eq_inv_comp, functor.map_iso_hom, shift_shift_add_hom',
    category.assoc],
end

@[reassoc] lemma shift_add_hom_comp_eq_to_hom₁ (i i' j : A) (h : i = i') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i' j).hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[reassoc] lemma shift_add_hom_comp_eq_to_hom₂ (i j j' : A) (h : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw h) = eq_to_hom (by rw h) ≫ (shift_add X i j').hom :=
by { cases h, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc] lemma shift_add_hom_comp_eq_to_hom₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  (shift_add X i j).hom ≫ eq_to_hom (by rw [h₁, h₂]) =
    eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').hom :=
by { cases h₁, cases h₂, rw [eq_to_hom_refl, eq_to_hom_refl, category.id_comp, category.comp_id] }

@[reassoc] lemma eq_to_hom_comp_shift_add_inv₁ (i i' j : A) (h : i = i') :
  eq_to_hom (by rw h) ≫ (shift_add X i' j).inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁]

@[reassoc] lemma eq_to_hom_comp_shift_add_inv₂ (i j j' : A) (h : j = j') :
  eq_to_hom (by rw h) ≫ (shift_add X i j').inv = (shift_add X i j).inv ≫ eq_to_hom (by rw h) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₂]

@[simp, reassoc] lemma eq_to_hom_comp_shift_add_inv₁₂ (i j i' j' : A) (h₁ : i = i') (h₂ : j = j') :
  eq_to_hom (by rw [h₁, h₂]) ≫ (shift_add X i' j').inv =
    (shift_add X i j).inv ≫ eq_to_hom (by rw [h₁, h₂]) :=
by rw [iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, shift_add_hom_comp_eq_to_hom₁₂]

lemma shift_shift' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_add X i j).inv ≫ f⟦i + j⟧' ≫ (shift_add Y i j).hom :=
by { symmetry, apply nat_iso.naturality_1 }

variables (A) [is_equivalence (shift_functor C (0:A))]

/-- Shifting by zero is the identity functor. -/
abbreviation shift_zero  :
  X⟦0⟧ ≅ X := (shift_functor_zero C A).app _

lemma shift_zero' :
  f⟦(0 : A)⟧' = (shift_zero A X).hom ≫ f ≫ (shift_zero A Y).inv :=
by { symmetry, apply nat_iso.naturality_2 }

-- @[simp]
-- lemma shift_functor_zero_hom_app : (shift_functor_zero C A).hom.app X = (shift_zero A X).hom := rfl

-- @[simp]
-- lemma shift_functor_zero_inv_app : (shift_functor_zero C A).inv.app X = (shift_zero A X).inv := rfl

end add_monoid

section add_group

variables {A} [add_group A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_functor_comp_shift_functor_neg (i : A) :
  shift_functor C i ⋙ shift_functor C (-i) ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) i (-i : A) (eq_to_iso (add_neg_self _))

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_functor_neg_comp_shift_functor (i : A) :
  shift_functor C (-i) ⋙ shift_functor C i ≅ 𝟭 C :=
unit_of_tensor_iso_unit (shift_monoidal_functor C A) (-i : A) i (eq_to_iso (neg_add_self _))

section

variables (C)

/-- Shifting by `n` is a faithful functor. -/
instance shift_functor_faithful (i : A) : faithful (shift_functor C i) :=
faithful.of_comp_iso (shift_functor_comp_shift_functor_neg C i)

-- local attribute [instance] shift_functor_faithful

/-- Shifting by `n` is a full functor. -/
instance shift_functor_full (i : A) : full (shift_functor C i) :=
begin
  haveI : full (shift_functor C i ⋙ shift_functor C (-i)) :=
    full.of_iso (shift_functor_comp_shift_functor_neg C i).symm,
  exact full.of_comp_faithful _ (shift_functor C (-i))
end

/-- Shifting by `n` is an essentially surjective functor. -/
instance shift_functor_ess_surj (i : A) : ess_surj (shift_functor C i) :=
{ mem_ess_image := λ Y, ⟨Y⟦-i⟧, ⟨(shift_functor_neg_comp_shift_functor C i).app Y⟩⟩ }

/-- Shifting by `n` is an equivalence. -/
noncomputable instance shift_functor_is_equivalence (n : A) : is_equivalence (shift_functor C n) :=
equivalence.of_fully_faithfully_ess_surj _

end

variables {C}

/-- Shifting by `i` and then shifting by `-i` is the identity. -/
abbreviation shift_shift_neg (i : A) : X⟦i⟧⟦-i⟧ ≅ X := (shift_functor_comp_shift_functor_neg C i).app _

/-- Shifting by `-i` and then shifting by `i` is the identity. -/
abbreviation shift_neg_shift (i : A) : X⟦-i⟧⟦i⟧ ≅ X := (shift_functor_neg_comp_shift_functor C i).app _

-- @[simp] lemma shift_functor_comp_shift_functor_neg_hom_app (i : A) :
--   (shift_functor_comp_shift_functor_neg C i).hom.app X = (shift_shift_neg X i).hom := rfl

-- @[simp] lemma shift_functor_comp_shift_functor_neg_inv_app (i : A) :
--   (shift_functor_comp_shift_functor_neg C i).inv.app X = (shift_shift_neg X i).inv := rfl

-- @[simp] lemma shift_functor_neg_comp_shift_functor_hom_app (i : A) :
--   (shift_functor_neg_comp_shift_functor C i).hom.app X = (shift_neg_shift X i).hom := rfl

-- @[simp] lemma shift_functor_neg_comp_shift_functor_inv_app (i : A) :
--   (shift_functor_neg_comp_shift_functor C i).inv.app X = (shift_neg_shift X i).inv := rfl

variables {X Y}

lemma shift_shift_neg' (i : A) :
  f⟦i⟧'⟦-i⟧' = (shift_shift_neg X i).hom ≫ f ≫ (shift_shift_neg Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

lemma shift_neg_shift' (i : A) :
  f⟦-i⟧'⟦i⟧' = (shift_neg_shift X i).hom ≫ f ≫ (shift_neg_shift Y i).inv :=
by { symmetry, apply nat_iso.naturality_2 }

@[simp, reassoc] lemma shift_shift'_comp_shift_shift_neg (i : A) :
  f⟦i⟧'⟦-i⟧' ≫ (shift_shift_neg _ _).hom = (shift_shift_neg _ _).hom ≫ f :=
by rw [← iso.eq_comp_inv, shift_shift_neg', category.assoc]

@[simp, reassoc] lemma shift_shift_neg_inv_comp_shift_shift' (i : A) :
  (shift_shift_neg _ _).inv ≫ f⟦i⟧'⟦-i⟧' = f ≫ (shift_shift_neg _ _).inv :=
by rw [iso.inv_comp_eq, shift_shift_neg']

@[simp, reassoc] lemma shift_shift'_comp_shift_neg_shift (i : A) :
  f⟦-i⟧'⟦i⟧' ≫ (shift_neg_shift _ _).hom = (shift_neg_shift _ _).hom ≫ f :=
by rw [← iso.eq_comp_inv, shift_neg_shift', category.assoc]

@[simp, reassoc] lemma shift_neg_shift_inv_comp_shift_shift' (i : A) :
  (shift_neg_shift _ _).inv ≫ f⟦-i⟧'⟦i⟧' = f ≫ (shift_neg_shift _ _).inv :=
by rw [iso.inv_comp_eq, shift_neg_shift']

@[simp]
lemma shift_functor_zero_shift (X : C) (n : A) :
  (shift_zero A X).hom⟦n⟧' =
    (shift_add X 0 n).inv ≫ eq_to_hom (by simp) :=
begin
  convert (obj_ε_inv_app (shift_monoidal_functor C A) n X),
  simp,
end

@[simp]
lemma shift_zero_inv_shift (n : A) (X : C) :
  (shift_zero A X).inv⟦n⟧' = eq_to_hom (by simp) ≫ (shift_add X 0 n).hom :=
begin
  rw [← cancel_mono ((shift_zero A X).hom⟦n⟧'), ← functor.map_comp],
  simp,
  dsimp,
  simp,
end

@[simp, reassoc]
lemma shift_zero_shift (n : A) (X : C) :
  (shift_add X n 0).hom ≫ (shift_zero A (X⟦n⟧)).hom = eq_to_hom (by simp) :=
begin
  apply (shift_functor C (0 : A)).map_injective,
  simp
end

-- local attribute [semireducible] shift_shift_neg shift_neg_shift

lemma shift_equiv_triangle (n : A) (X : C) :
  (shift_shift_neg X n).inv⟦n⟧' ≫ (shift_neg_shift (X⟦n⟧) n).hom = 𝟙 (X⟦n⟧) :=
(add_neg_equiv (shift_monoidal_functor C A) n).functor_unit_iso_comp X

@[simp]
lemma shift_shift_neg_hom_shift (n : A) (X : C) :
  (shift_shift_neg X n).hom ⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).hom :=
by rw [← cancel_epi ((shift_shift_neg X n).inv⟦n⟧'), shift_equiv_triangle,
    ← functor.map_comp, iso.inv_hom_id, functor.map_id]

@[simp]
lemma shift_shift_neg_inv_shift (n : A) (X : C) :
  (shift_shift_neg X n).inv ⟦n⟧' = (shift_neg_shift (X⟦n⟧) n).inv :=
by { ext, rw [← shift_shift_neg_hom_shift, ← functor.map_comp, iso.hom_inv_id, functor.map_id] }

@[simp]
lemma shift_shift_neg_shift_eq (n : A) (X : C) :
  (shift_functor C n).map_iso (shift_shift_neg X n) = shift_neg_shift (X⟦n⟧) n :=
category_theory.iso.ext $ shift_shift_neg_hom_shift _ _

variables (C)

/-- Shifting by `n` and shifting by `-n` forms an equivalence. -/
@[simps]
def shift_equiv (n : A) : C ≌ C :=
{ functor := shift_functor C n,
  inverse := shift_functor C (-n),
  ..(add_neg_equiv (shift_monoidal_functor C A) n) }

variable {C}

open category_theory.limits

variables [has_zero_morphisms C]

@[simp]
lemma shift_zero_eq_zero (X Y : C) (n : A) : (0 : X ⟶ Y)⟦n⟧' = (0 : X⟦n⟧ ⟶ Y⟦n⟧) :=
by apply is_equivalence_preserves_zero_morphisms _ (shift_functor C n)

end add_group

section add_comm_monoid

variables {C A} [add_comm_monoid A] [has_shift C A]
variables (X Y : C) (f : X ⟶ Y)

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
def shift_comm (i j : A) : X⟦i⟧⟦j⟧ ≅ X⟦j⟧⟦i⟧ :=
(shift_add X i j).symm ≪≫ eq_to_iso (by rw add_comm) ≪≫ shift_add X j i

@[simp] lemma shift_comm_symm (i j : A) : (shift_comm X i j).symm = shift_comm X j i :=
begin
  ext, dsimp [shift_comm],
  simpa,
end

variables {X Y}

/-- When shifts are indexed by an additive commutative monoid, then shifts commute. -/
lemma shift_comm' (i j : A) :
  f⟦i⟧'⟦j⟧' = (shift_comm _ _ _).hom ≫ f⟦j⟧'⟦i⟧' ≫ (shift_comm _ _ _).hom :=
begin
  rw [shift_shift', shift_shift'],
  dsimp [shift_comm],
  simp only [← category.assoc, cancel_mono],
  simp only [iso.hom_inv_id_assoc, iso.cancel_iso_inv_left, category.assoc, μ_inv_hom_app_assoc],
  congr' 1,
  generalize_proofs h1 h2, revert h1 h2,
  generalize hij : i + j = ij, generalize hji : j + i = ji, intros h1 h2,
  obtain rfl : ij = ji, { rw [← hij, add_comm, hji] }, clear hij hji,
  rw [eq_to_hom_refl, eq_to_hom_refl, category.comp_id, category.id_comp],
end

@[reassoc] lemma shift_comm_hom_comp (i j : A) :
  (shift_comm X i j).hom ≫ f⟦j⟧'⟦i⟧' = f⟦i⟧'⟦j⟧' ≫ (shift_comm Y i j).hom :=
by rw [shift_comm', ← shift_comm_symm, iso.symm_hom, iso.inv_hom_id_assoc]

end add_comm_monoid

end category_theory
