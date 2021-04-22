import category_theory.monoidal.free.basic
import category_theory.discrete_category

universes v u

namespace category_theory

variables {C : Type u}

section
variables (C)

inductive normal_monoidal_object : Type u
| unit : normal_monoidal_object
| tensor : normal_monoidal_object → C → normal_monoidal_object

notation `N` C := discrete (normal_monoidal_object C)

end

@[simp]
def inclusion' : normal_monoidal_object C → F C
| normal_monoidal_object.unit := free_monoidal_category.unit
| (normal_monoidal_object.tensor n a) := free_monoidal_category.tensor (inclusion' n) (free_monoidal_category.of a)

@[simp]
def inclusion : (N C) ⥤ F C :=
discrete.functor inclusion'

@[simp] def normalize_obj : F C → normal_monoidal_object C → normal_monoidal_object C
| free_monoidal_category.unit n := n
| (free_monoidal_category.of X) n := normal_monoidal_object.tensor n X
| (free_monoidal_category.tensor X Y) n := normalize_obj Y (normalize_obj X n)

@[simp] lemma normalize_obj_unitor (n : N C) : normalize_obj (𝟙_ (F C)) n = n :=
rfl

@[simp] lemma normalize_obj_tensor (X Y : F C) (n : N C) :
  normalize_obj (X ⊗ Y) n = normalize_obj Y (normalize_obj X n) :=
rfl

def F_hom_mk {X Y : F C} (f : X ⟶ᵐ Y) : X ⟶ Y :=
⟦f⟧

@[simp]
def normalize_map_aux : Π {X Y : F C},
  (X ⟶ᵐ Y) →
    ((discrete.functor (normalize_obj X) : _ ⥤ (N C)) ⟶ discrete.functor (normalize_obj Y))
| _ _ (free_monoidal_category_hom.id _) := 𝟙 _
| _ _ (free_monoidal_category_hom.α_hom _ _ _) := ⟨λ X, 𝟙 _⟩
| _ _ (free_monoidal_category_hom.α_inv _ _ _) := ⟨λ X, 𝟙 _⟩
| _ _ (free_monoidal_category_hom.l_hom _) := ⟨λ X, 𝟙 _⟩
| _ _ (free_monoidal_category_hom.l_inv _) := ⟨λ X, 𝟙 _⟩
| _ _ (free_monoidal_category_hom.ρ_hom _) := ⟨λ X, 𝟙 _⟩
| _ _ (free_monoidal_category_hom.ρ_inv _) := ⟨λ X, 𝟙 _⟩
| X Y (@free_monoidal_category_hom.comp _ U V W f g) := normalize_map_aux f ≫ normalize_map_aux g
| X Y (@free_monoidal_category_hom.tensor _ T U V W f g) :=
    ⟨λ X, (normalize_map_aux g).app (normalize_obj T X) ≫ (discrete.functor (normalize_obj W) : _ ⥤ N C).map ((normalize_map_aux f).app X), by tidy⟩

@[simp]
def normalize : F C ⥤ ((N C) ⥤ N C) :=
{ obj := λ X, discrete.functor (normalize_obj X),
  map := λ X Y, quotient.lift normalize_map_aux (by tidy) }

def full_normalize : F C ⥤ N C :=
{ obj := λ X, (normalize.obj X).obj normal_monoidal_object.unit,
  map := λ X Y f, (normalize.map f).app normal_monoidal_object.unit }

@[simp]
def tensor_func : F C ⥤ ((N C) ⥤ F C) :=
{ obj := λ X, discrete.functor (λ n, (inclusion.obj n) ⊗ X),
  map := λ X Y f, ⟨λ n, 𝟙 _ ⊗ f, by tidy⟩ }

lemma tensor_func_map_app {X Y : F C} (f : X ⟶ Y) (n) : (tensor_func.map f).app n =
  𝟙 _ ⊗ f :=
rfl

section
variables (C)

@[simp]
def normalize' : F C ⥤ ((N C) ⥤ F C) :=
normalize ⋙ (whiskering_right _ _ _).obj inclusion

@[simp]
def normalize_iso_app :
  Π (X : F C) (n : N C), (tensor_func.obj X).obj n ≅ ((normalize' C).obj X).obj n
| (free_monoidal_category.of X) n := iso.refl _
| free_monoidal_category.unit n := ρ_ _
| (free_monoidal_category.tensor X Y) n :=
  (α_ _ _ _).symm ≪≫ tensor_iso (normalize_iso_app X n) (iso.refl _) ≪≫ normalize_iso_app _ _

@[simp]
lemma normalize_iso_app_tensor (X Y : F C) (n : N C) :
  normalize_iso_app C (X ⊗ Y) n =
  (α_ _ _ _).symm ≪≫ tensor_iso (normalize_iso_app C X n) (iso.refl _) ≪≫ normalize_iso_app _ _ _ :=
rfl

@[simp]
lemma normalize_iso_app_unitor (n : N C) : normalize_iso_app C (𝟙_ (F C)) n = ρ_ _ :=
rfl

@[simp]
def normalize_iso_aux (X : F C) : tensor_func.obj X ≅ (normalize' C).obj X :=
nat_iso.of_components (normalize_iso_app C X) (by tidy)

lemma weird {n n' : N C} (f : n ⟶ n')(Z : F C) :
  inclusion.map f ⊗ 𝟙 Z = (discrete.functor (λ n, inclusion' n ⊗ Z)).map f :=
by tidy

def normalize_iso : tensor_func ≅ normalize' C :=
nat_iso.of_components (normalize_iso_aux C)
begin
  rintros X Y f,
  apply quotient.induction_on f,
  intro f,
  ext n,
  induction f generalizing n,
  { simp only [mk_id_eq_id, functor.map_id, category.id_comp, category.comp_id] },
  { dsimp,
    rw [monoidal_category.id_tensor_associator_inv_naturality_assoc,
      ←monoidal_category.pentagon_inv_assoc],
    simp only [monoidal_category.tensor_hom_inv_id_assoc, monoidal_category.tensor_id, category.id_comp, discrete.functor_map_id,
  monoidal_category.comp_tensor_id, iso.cancel_iso_inv_left, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    simp only [discrete.functor_map_id, monoidal_category.comp_tensor_id, category.assoc],
    rw [monoidal_category.pentagon_inv_assoc, ←monoidal_category.associator_inv_naturality_assoc],
    simp only [monoidal_category.tensor_id, iso.cancel_iso_inv_left],
    dsimp, simp only [category.comp_id],},
  { dsimp,
    rw monoidal_category.triangle_assoc_comp_right_assoc,
    simp only [discrete.functor_map_id, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    rw monoidal_category.triangle_assoc_comp_left_inv_assoc,
    simp only [monoidal_category.inv_hom_id_tensor_assoc, monoidal_category.tensor_id, category.id_comp, discrete.functor_map_id],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    rw [←(iso.inv_comp_eq _).2 (monoidal_category.right_unitor_tensor _ _),
      category.assoc, ←monoidal_category.right_unitor_naturality],
    simp only [discrete.functor_map_id, iso.cancel_iso_inv_left, category.assoc],
    dsimp, simp only [category.comp_id] },
  { dsimp,
    rw [←(iso.eq_comp_inv _).1 (monoidal_category.right_unitor_tensor_inv _ _)],
    simp only [iso.hom_inv_id_assoc, monoidal_category.right_unitor_conjugation, discrete.functor_map_id, category.assoc],
    dsimp, simp only [category.comp_id], },
  { dsimp at *,
    rw [monoidal_category.id_tensor_comp, category.assoc, f_ih_g ⟦f_g⟧, ←category.assoc,
      f_ih_f ⟦f_f⟧, category.assoc, ←functor.map_comp],
    congr' 2 },
  { dsimp at *,
    rw monoidal_category.associator_inv_naturality_assoc,
    slice_lhs 2 3 { rw [←monoidal_category.tensor_comp, f_ih_f ⟦f_f⟧],
      congr, skip,
      rw category.comp_id,
      rw [←@category.id_comp (F C) _ _ _ ⟦f_g⟧] },
    rw monoidal_category.tensor_comp,
    simp only [category.assoc],
    congr' 2,
    rw [←mk_tensor_eq_tensor, quotient.lift_mk],
    dsimp,
    rw [functor.map_comp, ←category.assoc, ←f_ih_g ⟦f_g⟧],
    rw [←@category.comp_id (F C) _ _ _ ⟦f_g⟧],
    rw ←category.id_comp ((discrete.functor inclusion').map _),
    rw monoidal_category.tensor_comp,
    dsimp,
    simp only [category.assoc, category.comp_id],
    congr' 1,
    convert (normalize_iso_aux C f_Z).hom.naturality ((normalize_map_aux f_f).app n),
    dsimp,
    exact weird _ _ _, }
end

def full_normalize_iso : 𝟭 (F C) ≅ full_normalize ⋙ inclusion :=
nat_iso.of_components
  (λ X, (λ_ X).symm ≪≫ ((normalize_iso C).app X).app normal_monoidal_object.unit)
  begin
    intros X Y f,
    dsimp,
    rw [monoidal_category.left_unitor_inv_naturality_assoc, category.assoc],
    congr' 1,
    have := nat_iso.naturality_2 (normalize_iso.{u} C) f,
    erw ←tensor_func_map_app f normal_monoidal_object.unit,
    rw ←this,
    dsimp,
    simp only [category.assoc],
    congr' 1,
    slice_lhs 2 3 { rw [←nat_trans.comp_app, ←nat_trans.comp_app], },
    simp only [nat_trans.id_app, category.comp_id, iso.inv_hom_id],
    dsimp, simp,
    congr' 1,
  end

end

instance coherence {X Y : F C} : subsingleton (X ⟶ Y) :=
begin
  constructor,
  intros f g,
  rw [←functor.id_map f, ←functor.id_map g],
  have : full_normalize.map f = full_normalize.map g := subsingleton.elim _ _,
  simp [←nat_iso.naturality_2 (full_normalize_iso.{u} C), this]
end

instance : groupoid.{u} (F C) :=
{ inv := λ X Y, inverse, ..(by apply_instance : category (F C)) }

end category_theory
