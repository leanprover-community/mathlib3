import category_theory.concrete_category.operations

universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open category opposite limits

@[simp] lemma nat_trans.hcomp_id {C₁ C₂ C₃ : Type*} [category C₁] [category C₂] [category C₃]
  (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) : (𝟙 F) ◫ (𝟙 G) = 𝟙 (F ⋙ G) := by tidy

namespace concrete_category

variables (A : Type u₂) [category.{v₂} A] [concrete_category.{v₁} A]
  (C : Type u₁) [category.{v₁} C]

/-- The category of internal `A`-objects in the category `C`. -/
structure internal :=
(obj : C)
(presheaf : Cᵒᵖ ⥤ A)
(iso : yoneda.obj obj ≅ presheaf ⋙ forget A)

instance : category (internal A C) := induced_category.category (λ X, X.presheaf)

namespace internal

@[simps]
def presheaf_functor : internal A C ⥤ (Cᵒᵖ ⥤ A) := induced_functor _

@[simps]
def type_presheaf_functor : internal A C ⥤ (Cᵒᵖ ⥤ Type v₁) :=
presheaf_functor A C ⋙ (whiskering_right Cᵒᵖ A (Type v₁)).obj (forget A)

def obj_functor : internal A C ⥤ C :=
{ obj := λ X, X.obj,
  map := λ X Y f, yoneda.preimage ((X.iso.hom ≫ (f ◫ (𝟙 (forget A))) ≫ Y.iso.inv)),
  map_id' := λ X, yoneda.map_injective begin
    erw [functor.image_preimage, nat_trans.hcomp_id, id_comp, X.iso.hom_inv_id,
      yoneda.map_id],
  end,
  map_comp' := λ X Y Z f g, yoneda.map_injective begin
    simp only [functor.image_preimage, yoneda.map_comp, assoc, Y.iso.inv_hom_id_assoc],
    ext x : 2,
    simp only [nat_trans.comp_app, nat_trans.hcomp_id_app],
    erw [nat_trans.comp_app, functor.map_comp, assoc],
  end }

variables {A C} {Y Y' : C} (R : internal A C)

def presheaf_type := (type_presheaf_functor A C).obj R

lemma iso_hom_naturality (x : Y ⟶ R.obj) (f : Y' ⟶ Y) :
  R.iso.hom.app (op Y') (f ≫ x) = R.presheaf_type.map f.op (R.iso.hom.app (op Y) x) :=
congr_fun (R.iso.hom.naturality f.op) x

lemma iso_inv_naturality (x : R.presheaf_type.obj (op Y)) (f : Y' ⟶ Y) :
  R.iso.inv.app (op Y') (R.presheaf_type.map f.op x) = f ≫ R.iso.inv.app (op Y) x :=
congr_fun (R.iso.inv.naturality f.op) x

end internal

variables {A C}

open operations

namespace operation₀

variables (oper oper' : operation₀ A) (R : internal A C)

def on_internal_presheaf (Y : C) : R.presheaf_type.obj (op Y) :=
oper.app (R.presheaf.obj (op Y)) punit.star

lemma on_internal_presheaf_naturality {Y Y' : C} (f : Y' ⟶ Y) :
  oper.on_internal_presheaf R Y' = R.presheaf_type.map f.op (oper.on_internal_presheaf R Y) :=
congr_fun (oper.naturality (R.presheaf.map f.op)) punit.star

def on_internal_yoneda (Y : C) : Y ⟶ R.obj :=
R.iso.inv.app (op Y) (oper.on_internal_presheaf R Y)

lemma on_internal_yoneda_naturality {Y Y' : C} (f : Y' ⟶ Y) :
f ≫ oper.on_internal_yoneda R Y = oper.on_internal_yoneda R Y' :=
begin
  dsimp only [on_internal_yoneda],
  rw [← R.iso_inv_naturality, oper.on_internal_presheaf_naturality R f],
end

def on_internal_yoneda_presheaf : (functor.const Cᵒᵖ).obj punit ⟶ yoneda.obj R.obj :=
{ app := λ X s, oper.on_internal_yoneda R X.unop,
  naturality' := λ X Y f, begin
    ext x,
    dsimp at x,
    have eq : x = punit.star := subsingleton.elim _ _,
    subst eq,
    exact (oper.on_internal_yoneda_naturality R f.unop).symm,
  end }

def on_internal_obj [has_terminal C] : ⊤_ C ⟶ R.obj :=
oper.on_internal_yoneda R _

lemma on_internal_yoneda_eq [has_terminal C] {Y : C} :
  oper.on_internal_yoneda R Y = terminal.from Y ≫ oper.on_internal_obj R :=
begin
  dsimp only [on_internal_obj],
  simp only [on_internal_yoneda_naturality],
end

lemma ext [has_terminal C]
  (h : oper.on_internal_obj R = oper'.on_internal_obj R) :
  oper.on_internal_yoneda_presheaf R = oper'.on_internal_yoneda_presheaf R :=
begin
  ext Y x,
  dsimp only [on_internal_yoneda_presheaf],
  simp only [on_internal_yoneda_eq, h],
end

end operation₀

namespace operation₁

variables (oper oper' : operation₁ A) {R : internal A C}

variables {Y Y' : C}

@[protected]
def on_internal_presheaf
  (x : R.presheaf_type.obj (op Y)) : R.presheaf_type.obj (op Y) :=
oper.app (R.presheaf.obj (op Y)) x

lemma on_internal_presheaf_naturality (x : R.presheaf_type.obj (op Y)) (f : Y' ⟶ Y) :
    oper.on_internal_presheaf (R.presheaf_type.map f.op x)  =
  R.presheaf_type.map f.op (oper.on_internal_presheaf x) :=
congr_fun (oper.naturality (R.presheaf.map f.op)) x

def on_internal_yoneda (x : Y ⟶ R.obj) : Y ⟶ R.obj :=
R.iso.inv.app _ (oper.on_internal_presheaf (R.iso.hom.app (op Y) x))

lemma on_internal_yoneda_naturality (x : Y ⟶ R.obj) (f : Y' ⟶ Y) :
  f ≫ oper.on_internal_yoneda x = oper.on_internal_yoneda (f ≫ x) :=
begin
  dsimp only [on_internal_yoneda],
  simp only [R.iso_hom_naturality, on_internal_presheaf_naturality, R.iso_inv_naturality],
end

variable (R)

def on_internal_yoneda_presheaf :
  yoneda.obj R.obj ⟶ yoneda.obj R.obj :=
{ app := λ X x, oper.on_internal_yoneda x,
  naturality' := λ X Y f, begin
    ext x,
    symmetry,
    apply on_internal_yoneda_naturality,
  end, }

def on_internal_obj : R.obj ⟶ R.obj :=
oper.on_internal_yoneda (𝟙 R.obj)

lemma on_internal_yoneda_eq {Y : C} (x : Y ⟶ R.obj) :
  oper.on_internal_yoneda x = x ≫ oper.on_internal_obj R :=
begin
  dsimp only [on_internal_obj],
  simp only [on_internal_yoneda_naturality, comp_id],
end

lemma ext
  (h : oper.on_internal_obj R = oper'.on_internal_obj R) :
  oper.on_internal_yoneda_presheaf R = oper'.on_internal_yoneda_presheaf R :=
begin
  ext Y x,
  dsimp only [on_internal_yoneda_presheaf],
  simp only [on_internal_yoneda_eq, h],
end

end operation₁

namespace operation₂

variables (oper oper' : operation₂ A) {R : internal A C}

variables {Y Y' : C}

@[protected]
def on_internal_presheaf
  (x y : R.presheaf_type.obj (op Y)) : R.presheaf_type.obj (op Y) :=
oper.app (R.presheaf.obj (op Y)) ⟨x,y⟩

lemma on_internal_presheaf_naturality (x y : R.presheaf_type.obj (op Y)) (f : Y' ⟶ Y) :
    oper.on_internal_presheaf (R.presheaf_type.map f.op x) (R.presheaf_type.map f.op y) =
  R.presheaf_type.map f.op (oper.on_internal_presheaf x y) :=
congr_fun (oper.naturality (R.presheaf.map f.op)) ⟨x,y⟩

def on_internal_yoneda (x y : Y ⟶ R.obj) : Y ⟶ R.obj :=
R.iso.inv.app _ (oper.on_internal_presheaf (R.iso.hom.app (op Y) x) (R.iso.hom.app (op Y) y))

lemma on_internal_yoneda_naturality (x y : Y ⟶ R.obj) (f : Y' ⟶ Y) :
  f ≫ oper.on_internal_yoneda x y = oper.on_internal_yoneda (f ≫ x) (f ≫ y) :=
begin
  dsimp only [on_internal_yoneda],
  simp only [R.iso_hom_naturality, on_internal_presheaf_naturality, R.iso_inv_naturality],
end

variable (R)

def on_internal_yoneda_presheaf :
  concat₂ (yoneda.obj R.obj) (yoneda.obj R.obj) ⟶ yoneda.obj R.obj :=
{ app := λ X x, oper.on_internal_yoneda x.1 x.2,
  naturality' := λ X Y f, begin
    ext x,
    symmetry,
    apply on_internal_yoneda_naturality,
  end, }

def on_internal_obj [has_binary_product R.obj R.obj] : prod R.obj R.obj ⟶ R.obj :=
oper.on_internal_yoneda limits.prod.fst limits.prod.snd

lemma on_internal_yoneda_eq [has_binary_product R.obj R.obj] {Y : C} (x y : Y ⟶ R.obj) :
  oper.on_internal_yoneda x y = prod.lift x y ≫ oper.on_internal_obj R :=
begin
  dsimp only [on_internal_obj],
  simp only [on_internal_yoneda_naturality, prod.lift_fst, prod.lift_snd],
end

lemma ext [has_binary_product R.obj R.obj]
  (h : oper.on_internal_obj R = oper'.on_internal_obj R) :
  oper.on_internal_yoneda_presheaf R = oper'.on_internal_yoneda_presheaf R :=
begin
  ext Y x,
  dsimp only [on_internal_yoneda_presheaf],
  simp only [on_internal_yoneda_eq, h],
end

end operation₂

end concrete_category

end category_theory
