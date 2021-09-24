import category_theory.sites.sheaf
import category_theory.limits.has_limits
import category_theory.functor_category

universes v u
noncomputable theory

open opposite category_theory
open category_theory.limits
variables {C D E A : Type u} [category.{u} C] [category.{u} D] [category.{u} E] [category.{u} A]
variables [has_limits A] (F : C ⥤ D)

def pullback : (Dᵒᵖ ⥤ A) ⥤ (Cᵒᵖ ⥤ A) := (whiskering_left Cᵒᵖ Dᵒᵖ A).obj F.op

include F

-- set_option pp.universes true

lemma functor.id_op : (𝟭 C).op = 𝟭 Cᵒᵖ := rfl

lemma comma.map_left_id_eq (R : E ⥤ D) : comma.map_left F (𝟙 R) = 𝟭 _ := by {
  unfold comma.map_left,
  apply category_theory.functor.hext,
  { intros X,
    cases X,
    simp },
  {
    intros X Y f,
    cases X, cases Y, cases f,
    simp only [functor.id_map],
    congr,
    { simp [nat_trans.id_app'] },
    { simp [nat_trans.id_app'] },
    apply proof_irrel_heq
  }
}

lemma comma.map_right_id_eq (R : E ⥤ D) : comma.map_right F (𝟙 R) = 𝟭 _ := by {
  unfold comma.map_right,
  apply category_theory.functor.hext,
  { intros X,
    cases X,
    simp },
  {
    intros X Y f,
    cases X, cases Y, cases f,
    simp only [functor.id_map],
    congr,
    { simp [nat_trans.id_app'] },
    { simp [nat_trans.id_app'] },
    apply proof_irrel_heq
  }
}

lemma comma.map_left_comp_eq (L₁ L₂ L₃ : E ⥤ D) (f₁ : L₁ ⟶ L₂) (f₂ : L₂ ⟶ L₃):
  comma.map_left F (f₁ ≫ f₂) = comma.map_left F f₂ ⋙ comma.map_left F f₁
:= by {
  unfold comma.map_left,
  apply category_theory.functor.hext,
  {
    intros X, cases X, simp,
  }, {
    intros X Y f,
    cases X, cases Y, cases f,
    simp only [functor.comp_map],
    congr' 2,
    { simp },
    { simp },
  }
}

lemma comma.map_right_comp_eq (L₁ L₂ L₃ : E ⥤ D) (f₁ : L₁ ⟶ L₂) (f₂ : L₂ ⟶ L₃):
  comma.map_right F (f₁ ≫ f₂) = comma.map_right F f₁ ⋙ comma.map_right F f₂
:= by {
  unfold comma.map_right,
  apply category_theory.functor.hext,
  {
    intros X, cases X, simp,
  }, {
    intros X Y f,
    cases X, cases Y, cases f,
    simp only [functor.comp_map],
    congr' 2,
    { simp },
    { simp },
  }
}

def pushforward_obj (ℱ : Cᵒᵖ ⥤ A) : Dᵒᵖ ⥤ A := {
  obj := λ V,
    limit ((costructured_arrow.proj F (unop V)).op ⋙ ℱ),
  map := λ U V f,
    limit.pre ((costructured_arrow.proj F (unop U)).op ⋙ ℱ) (costructured_arrow.map f.unop).op,
  map_id' := λ U, by {
    ext,
    erw category.id_comp,
    dsimp only [costructured_arrow.map],
    simp only [limit.pre_π],
    congr,
    erw comma.map_right_id_eq F,
    change (𝟭 (_)).obj j = j,
    simp,
  },
  map_comp' := λ U V W f g, by {
    symmetry,
    convert limit.pre_pre ((costructured_arrow.proj F (unop U)).op ⋙ ℱ)
      (costructured_arrow.map f.unop).op (costructured_arrow.map g.unop).op,
    dsimp [costructured_arrow.map],
    simp[(category_theory.functor.const (discrete punit)).comp],
    rw comma.map_right_comp_eq,
    refl
  },
}

def pushforward : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A) := {
  obj := pushforward_obj F,
  map := _,
  map_id' := _,
  map_comp' := _,
}
