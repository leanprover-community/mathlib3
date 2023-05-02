import algebraic_geometry.pullbacks
import category_theory.limits.constructions.over.products
import category_theory.limits.full_subcategory

universes v u w
open algebraic_geometry category_theory category_theory.limits

lemma limits.prod.diag_map_eq_lift {C : Type*} [category C] [has_binary_products C]
  {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
  limits.diag X ≫ limits.prod.map f g = prod.lift f g :=
by simp only [limits.prod.lift_map, category.id_comp]

variables (C : Type*) [category C] [has_binary_products C] [has_terminal C]

local attribute [instance] over.construct_products.over_binary_product_of_pullback
  over.over_has_terminal

-- `mul_one` and `mul_right_inv` aren't necessary.
structure Group_ :=
(G : C)
(mul : G ⨯ G ⟶ G)
(one : ⊤_ C ⟶ G)
(inv : G ⟶ G)
(assoc : limits.prod.map mul (𝟙 G) ≫ mul = (limits.prod.associator G G G).hom
  ≫ limits.prod.map (𝟙 G) mul ≫ mul)
(one_mul : limits.prod.map one (𝟙 G) ≫ mul = limits.prod.snd)
(mul_one : limits.prod.map (𝟙 G) one ≫ mul = limits.prod.fst)
(mul_left_inv : limits.prod.lift inv (𝟙 G) ≫ mul = terminal.from G ≫ one)
(mul_right_inv : limits.prod.lift (𝟙 G) inv ≫ mul = terminal.from G ≫ one)

attribute [reassoc] Group_.one_mul Group_.mul_left_inv Group_.assoc
  Group_.mul_one Group_.mul_right_inv

abbreviation RepresentableGroupFunctor :=
full_subcategory ({ G : Cᵒᵖ ⥤ Group | (G ⋙ forget _).representable })

namespace RepresentableGroupFunctor

def comp_forget : RepresentableGroupFunctor C ⥤ (Cᵒᵖ ⥤ Type*) :=
full_subcategory_inclusion _ ⋙ (whiskering_right _ _ _).obj (forget _)

instance representable (G : RepresentableGroupFunctor C) :
  (G.1 ⋙ forget _).representable := G.2

instance group {G : RepresentableGroupFunctor C} {A : Cᵒᵖ} :
  group ((G.1 ⋙ forget _).obj A) :=
(G.1.obj A).group

variables {J : Type} [fintype J] (F : discrete J ⥤ RepresentableGroupFunctor C)

noncomputable def finite_product_repr_aux {J : Type} [fintype J]
  (F : discrete J ⥤ RepresentableGroupFunctor C) : discrete J ⥤ C :=
{ obj := λ i, ((F.obj i).1 ⋙ forget _).repr_X,
  map := λ X Y f, eq_to_hom (by discrete_cases; cases f; refl),
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g,
  begin
    discrete_cases,
    cases f,
    cases g,
    exact (category.comp_id _).symm,
  end }

end RepresentableGroupFunctor
namespace Group_
variables {C}

@[ext] structure hom (G H : Group_ C) :=
(hom : G.G ⟶ H.G)
(mul_comp : G.mul ≫ hom = limits.prod.map hom hom ≫ H.mul)
(one_comp : G.one ≫ hom = H.one)
(inv_comp : G.inv ≫ hom = hom ≫ H.inv)

restate_axiom hom.mul_comp hom.one_comp
-- why does this need to be on a new line lmao
restate_axiom hom.inv_comp
attribute [reassoc] hom.mul_comp hom.one_comp hom.inv_comp

@[simps] def hom.id (G : Group_ C) : G.hom G :=
{ hom := 𝟙 G.G,
  mul_comp := by simp only [category.comp_id, prod.map_id_id, category.id_comp],
  one_comp := by simp only [category.comp_id],
  inv_comp := by simp only [category.comp_id, category.id_comp]}

@[simps] def hom.comp {G H J : Group_ C} (f : G.hom H) (g : H.hom J) :
  G.hom J :=
{ hom := f.hom ≫ g.hom,
  mul_comp := by rw [f.mul_comp_assoc, g.mul_comp, prod.map_map_assoc],
  one_comp := by rw [f.one_comp_assoc, g.one_comp],
  inv_comp := by rw [f.inv_comp_assoc, g.inv_comp, category.assoc] }

instance : category (Group_ C) :=
{ hom := λ G H, G.hom H,
  id := λ G, hom.id G,
  comp := λ G H J f g, hom.comp f g }

@[simp] lemma id_hom (G : Group_ C) : (𝟙 G : G.hom G).hom = 𝟙 G.G := rfl

@[simp] lemma comp_hom {G H J : Group_ C} (f : G ⟶ H) (g : H ⟶ J) :
  (f ≫ g : G.hom J).hom = f.hom ≫ g.hom := rfl

variables (C)

def inclusion : Group_ C ⥤ C :=
{ obj := λ G, G.G,
  map := λ G H f, f.hom,
  map_id' := λ G, G.id_hom,
  map_comp' := λ G H J f g, comp_hom f g }

instance : faithful (inclusion C) :=
{ map_injective' := λ G H f g, f.ext g }

noncomputable instance (G : Group_ C) (Y : C) : group (Y ⟶ G.G) :=
{ mul := λ f g, limits.prod.lift f g ≫ G.mul,
  mul_assoc := λ f g h,
  begin
    show prod.lift (_ ≫ _) _ ≫ _ = prod.lift _ (_ ≫ _) ≫ _,
    rw ←category.comp_id h,
    simp only [←prod.lift_map, category.assoc, G.assoc],
    rw ←category.id_comp h,
    simp only [←limits.prod.diag_map_eq_lift, ←limits.prod.map_map,
      category.assoc, prod.associator_naturality_assoc],
    simp only [category.id_comp, category.comp_id, limits.prod.map_map_assoc,
      limits.prod.lift_map_assoc, limits.prod.associator_hom, limits.prod.lift_map,
      category.assoc, prod.lift_fst_comp_snd_comp, limits.prod.comp_lift_assoc,
      prod.lift_fst_assoc, prod.lift_snd_assoc],
    end,
  one := terminal.from Y ≫ G.one,
  one_mul := λ f,
  begin
    show prod.lift (_ ≫ _) _ ≫ _ = _,
    rw [←category.comp_id f, ←limits.prod.lift_map, category.assoc,
      one_mul, limits.prod.lift_snd, category.comp_id],
  end,
  mul_one := λ f,
  begin
    show prod.lift _ (_ ≫ _) ≫ _ = _,
    rw [←category.comp_id f, ←limits.prod.lift_map, category.assoc, mul_one,
      limits.prod.lift_fst, category.comp_id],
  end,
  inv := λ f, f ≫ G.inv,
  mul_left_inv := λ f,
  begin
    show prod.lift (_ ≫ _) _ ≫ _ = _ ≫ _,
    rw [←category.comp_id f, category.assoc, ←limits.prod.comp_lift, category.id_comp,
      category.assoc, G.mul_left_inv, ←category.assoc, terminal.comp_from],
  end }

variables {C}

lemma one_def (G : Group_ C) (Y : C) :
  (1 : Y ⟶ G.G) = terminal.from Y ≫ G.one := rfl

lemma mul_def {G : Group_ C} {Y : C} (g h : Y ⟶ G.G) :
  g * h = limits.prod.lift g h ≫ G.mul := rfl

lemma inv_def {G : Group_ C} {Y : C} (f : Y ⟶ G.G) :
  f⁻¹ = f ≫ G.inv := rfl

@[simps] def Group_to_Functor_obj_map
  (G : Group_ C) {X Y : C} (f : X ⟶ Y) :
  (Y ⟶ G.G) →* (X ⟶ G.G) :=
{ to_fun := λ g, f ≫ g,
  map_one' := by simp only [one_def, ←category.assoc, terminal.comp_from],
  map_mul' := λ x y, by simp only [mul_def, limits.prod.comp_lift_assoc] }

@[simps] noncomputable def Group_to_Functor_obj (G : Group_ C) :
  RepresentableGroupFunctor C :=
{ obj :=
  { obj := λ Y, Group.of (opposite.unop Y ⟶ G.G),
    map := λ X Y f, Group.of_hom (Group_to_Functor_obj_map G f.unop),
    map_id' := λ X,
    begin
      ext,
      simp only [unop_id, Group.of_hom_apply, Group_to_Functor_obj_map_apply,
        category.id_comp, id_apply],
    end,
    map_comp' := λ X Y Z f g,
    begin
      ext,
      simp only [unop_comp, Group.of_hom_apply, Group_to_Functor_obj_map_apply,
        category.assoc, comp_apply],
    end },
  property := ⟨⟨G.G, 𝟙 _, infer_instance⟩⟩ }

@[simps] noncomputable def Group_to_Functor_map
  {G H : Group_ C} (f : G ⟶ H) :
  Group_to_Functor_obj G ⟶ Group_to_Functor_obj H :=
{ app := λ X, Group.of_hom $ monoid_hom.mk' (λ g, g ≫ f.hom) (λ g h, show (_ ≫ _) ≫ _ = _ ≫ _,
    by simp only [category.assoc, f.mul_comp, ←limits.prod.lift_map]),
  naturality' := λ X Y g,
  begin
    ext,
    simp only [category.assoc, Group_to_Functor_obj_obj_map, comp_apply,
      Group.of_hom_apply, Group_to_Functor_obj_map_apply, monoid_hom.mk'_apply],
  end }

variables (C)

noncomputable def Group_to_Functor :
  Group_ C ⥤ RepresentableGroupFunctor C :=
{ obj := λ G, Group_to_Functor_obj G,
  map := λ G H f, Group_to_Functor_map f,
  map_id' := λ G,
  begin
    ext x y,
    simp only [id_hom, category.comp_id, Group_to_Functor_map_app, Group.of_hom_apply,
      monoid_hom.mk'_apply],
    erw [nat_trans.id_app, id_apply],
  end,
  map_comp' := λ G H J f g,
  begin
    ext x y,
    simp only [comp_hom, Group_to_Functor_map_app, Group.of_hom_apply, monoid_hom.mk'_apply],
    erw nat_trans.comp_app,
    simp only [Group_to_Functor_map_app, comp_apply, Group.of_hom_apply,
      monoid_hom.mk'_apply, category.assoc],
  end  }

noncomputable def Group_to_Functor_comp_forget_iso :
  Group_to_Functor C ⋙ RepresentableGroupFunctor.comp_forget C
    ≅ inclusion C ⋙ yoneda := iso.refl _

variables {C}

noncomputable instance group_yoneda_obj_op {G : RepresentableGroupFunctor C} {A : Cᵒᵖ} :
  group (opposite.unop A ⟶ (G.1 ⋙ forget _).repr_X) :=
equiv.group ((functor.repr_w (G.1 ⋙ forget _)).app A).to_equiv

noncomputable instance group_yoneda_obj {G : RepresentableGroupFunctor C} {A : C} :
    group (A ⟶ (G.1 ⋙ forget _).repr_X) :=
equiv.group ((G.1 ⋙ forget _).repr_w.app $ opposite.op A).to_equiv

lemma repr_w_map_inv {G : RepresentableGroupFunctor C} {A : Cᵒᵖ} (x : G.1.1 A) :
  ((G.1 ⋙ forget _).repr_w.inv.app A x⁻¹)
  = (((G.1 ⋙ forget _).repr_w.inv.app A x)⁻¹ : opposite.unop A ⟶ (G.1 ⋙ forget _).repr_X) :=
begin
  dsimp,
  rw [eq_inv_iff_mul_eq_one, equiv.mul_def],
  simp only [←iso.app_inv, ←iso.to_equiv_symm_fun],
  erw [equiv.apply_symm_apply, equiv.apply_symm_apply, inv_mul_self],
  refl,
end

@[simps] noncomputable def yoneda_map_hom (G : RepresentableGroupFunctor C) {A B : C} (f : A ⟶ B) :
  (B ⟶ (G.1 ⋙ forget _).repr_X) →* (A ⟶ (G.1 ⋙ forget _).repr_X) :=
{ to_fun := λ g, f ≫ g,
  map_one' :=
  begin
    have := congr_fun ((G.1 ⋙ forget _).repr_f.naturality f.op)
      (1 : B ⟶ (G.1 ⋙ forget _).repr_X),
    dsimp at this,
    simp only [←functor.repr_w_hom, equiv.one_def, ←iso.app_hom,
      ←iso.to_equiv_fun, equiv.apply_symm_apply, map_one] at this,
    simp only [equiv.one_def, ←this, equiv.symm_apply_apply],
  end,
  map_mul' := λ x y,
  begin
    have := congr_fun ((G.1 ⋙ forget _).repr_f.naturality f.op)
      (x * y : B ⟶ (G.1 ⋙ forget _).repr_X),
    rw ←equiv.apply_eq_iff_eq (as_iso $ (G.obj ⋙ forget Group).repr_f.app
      (opposite.op A)).to_equiv,
    simp only [iso.to_equiv_fun, as_iso_hom],
    simp only [←iso.to_equiv_fun, equiv.mul_def],
    dsimp at this,
    simp only [←functor.repr_w_hom, equiv.mul_def, ←iso.app_hom,
      ←iso.to_equiv_fun, equiv.apply_symm_apply, map_mul] at this,
    simp only [←functor.repr_w_hom, equiv.mul_def, ←iso.app_hom,
      ←iso.app_hom, ←iso.to_equiv_fun, ←iso.to_equiv_fun,
      equiv.apply_symm_apply, map_mul],
    rw this,
    have hx := congr_fun ((G.1 ⋙ forget _).repr_f.naturality f.op) x,
    have hy := congr_fun ((G.1 ⋙ forget _).repr_f.naturality f.op) y,
    dsimp at *,
    rw [hx, hy],
  end,  }

lemma comp_mul {G : RepresentableGroupFunctor C} {A B : C} (f : A ⟶ B)
  (g h : B ⟶ (G.1 ⋙ forget _).repr_X) :
  f ≫ (g * h) = f ≫ g * f ≫ h :=
(yoneda_map_hom G f).map_mul g h

lemma comp_one {G : RepresentableGroupFunctor C} {A B : C} (f : A ⟶ B) :
  f ≫ (1 : B ⟶ (G.1 ⋙ forget _).repr_X)  = 1 :=
(yoneda_map_hom G f).map_one

lemma comp_inv {G : RepresentableGroupFunctor C} {A B : C} (f : A ⟶ B)
  (g : B ⟶ (G.1 ⋙ forget _).repr_X) :
  f ≫ g⁻¹ = (f ≫ g)⁻¹ :=
(yoneda_map_hom G f).map_inv g

@[simps] noncomputable def Functor_to_Group_obj
  (G : RepresentableGroupFunctor C) : Group_ C :=
{ G := (G.1 ⋙ forget _).repr_X,
  mul := limits.prod.fst * limits.prod.snd,
  one := 1,
  inv := (𝟙 _)⁻¹,
  assoc :=
  begin
    simp only [comp_mul, limits.prod.map_fst, limits.prod.map_snd, category.comp_id,
      prod.associator_hom, prod.lift_map_assoc, category.assoc, mul_assoc,
      prod.lift_fst, prod.lift_snd_assoc, prod.lift_snd],
  end,
  one_mul :=
  begin
    simp only [comp_mul, limits.prod.map_fst, limits.prod.map_snd, category.comp_id,
      mul_left_eq_self, comp_one]
  end,
  mul_one :=
  begin
    simp only [comp_mul, comp_one, limits.prod.map_fst, category.comp_id, limits.prod.map_snd,
      mul_right_eq_self],
  end,
  mul_left_inv :=
  begin
    simp only [comp_mul, prod.lift_fst, prod.lift_snd, mul_left_inv,
      _root_.mul_left_inv, comp_one],
  end,
  mul_right_inv :=
  begin
    simp only [comp_mul, prod.lift_fst, prod.lift_snd, mul_right_inv, _root_.mul_right_inv,
      comp_one],
  end,}

variables {G H : RepresentableGroupFunctor C} (f : G ⟶ H) {X : C}
  (g : X ⟶ (G.1 ⋙ forget _).repr_X)

@[simps] noncomputable def Functor_to_Group_map
  {G H : RepresentableGroupFunctor C} (f : G ⟶ H) :
  Functor_to_Group_obj G ⟶ Functor_to_Group_obj H :=
{ hom := ((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj (forget _)).map f
    ≫ (H.1 ⋙ forget _).repr_w.inv).app (opposite.op $ (G.1 ⋙ forget _).repr_X) (𝟙 _),
  mul_comp :=
  begin
    simp only [Functor_to_Group_obj_mul, functor.repr_w_hom,
      whiskering_right_obj_map, functor_to_types.comp, whisker_right_app, forget_map_eq_coe],
    have := congr_fun (((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
      (forget _)).map f ≫ (H.1 ⋙ forget _).repr_w.inv).naturality
      (quiver.hom.op (limits.prod.fst * limits.prod.snd :
      (G.1 ⋙ forget _).repr_X ⨯ (G.1 ⋙ forget _).repr_X ⟶ (G.1 ⋙ forget _).repr_X))) (𝟙 _),
    dsimp at this,
    erw ←this,
    rw [category.comp_id, equiv.mul_def, ←functor.repr_w_hom, ←iso.app_hom, ←iso.to_equiv_fun,
      equiv.apply_symm_apply, map_mul, comp_mul, limits.prod.map_fst, limits.prod.map_snd],
    congr,
    { have hf := congr_fun (((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
        (forget _)).map f ≫ (H.1 ⋙ forget _).repr_w.inv).naturality
        (quiver.hom.op (limits.prod.fst : (G.1 ⋙ forget _).repr_X ⨯
        (G.1 ⋙ forget _).repr_X ⟶ (G.1 ⋙ forget _).repr_X))) (𝟙 _),
      dsimp at hf,
      erw ←hf,
      rw [category.comp_id, ←iso.app_inv, ←iso.to_equiv_symm_fun],
      erw equiv.apply_symm_apply,
      refl },
    { have hf := congr_fun (((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
        (forget _)).map f ≫ (H.1 ⋙ forget _).repr_w.inv).naturality
        (quiver.hom.op (limits.prod.snd : (G.1 ⋙ forget _).repr_X ⨯
        (G.1 ⋙ forget _).repr_X ⟶ (G.1 ⋙ forget _).repr_X))) (𝟙 _),
      dsimp at hf,
      erw ←hf,
      rw [category.comp_id, ←iso.app_inv, ←iso.to_equiv_symm_fun],
      erw equiv.apply_symm_apply,
      refl },
  end,
  one_comp :=
  begin
    simp only [Functor_to_Group_obj_one, functor.repr_w_hom, whiskering_right_obj_map,
      functor_to_types.comp, whisker_right_app, forget_map_eq_coe],
    have := congr_fun (((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
      (forget _)).map f ≫ (H.1 ⋙ forget _).repr_w.inv).naturality
      (quiver.hom.op (1 : ⊤_ C ⟶ (G.1 ⋙ forget _).repr_X))) (𝟙 _),
    dsimp at this,
    erw ←this,
    rw [category.comp_id, equiv.one_def, ←functor.repr_w_hom, ←iso.app_hom, ←iso.to_equiv_fun,
      equiv.apply_symm_apply, map_one],
    refl,
  end,
  inv_comp :=
  begin
    simp only [Functor_to_Group_obj_inv, functor.repr_w_hom, whiskering_right_obj_map,
      functor_to_types.comp, whisker_right_app, forget_map_eq_coe],
    have := congr_fun (((G.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
      (forget _)).map f ≫ (H.1 ⋙ forget _).repr_w.inv).naturality
      (quiver.hom.op ((𝟙 _)⁻¹ : (G.1 ⋙ forget _).repr_X ⟶ (G.1 ⋙ forget _).repr_X))) (𝟙 _),
    dsimp at this,
    erw ←this,
    rw [category.comp_id, equiv.inv_def, ←functor.repr_w_hom, ←iso.app_hom, ←iso.to_equiv_fun,
      equiv.apply_symm_apply, map_inv, repr_w_map_inv, comp_inv],
    erw category.comp_id,
    refl,
  end }

variables (C)

noncomputable def Functor_to_Group_ :
  RepresentableGroupFunctor C ⥤ Group_ C :=
{ obj := Functor_to_Group_obj,
  map := λ X Y f, Functor_to_Group_map f,
  map_id' := λ X,
  begin
    ext,
    simp only [Functor_to_Group_map_hom, functor.repr_w_hom,
      whiskering_right_obj_map, functor_to_types.comp, whisker_right_app, forget_map_eq_coe, id_hom],
    erw nat_trans.id_app,
    simp only [id_apply, ←functor.repr_w_hom, functor_to_types.hom_inv_id_app_apply],
    refl,
  end,
  map_comp' := λ X Y Z f g,
  begin
    ext,
    simp only [Functor_to_Group_map_hom, functor.repr_w_hom,
      whiskering_right_obj_map, functor_to_types.comp, whisker_right_app,
      forget_map_eq_coe, comp_hom],
    erw nat_trans.comp_app,
    have := congr_fun (((Y.1 ⋙ forget _).repr_w.hom ≫ ((whiskering_right _ _ _).obj
      (forget _)).map g ≫ (Z.1 ⋙ forget _).repr_w.inv).naturality
      (quiver.hom.op (Functor_to_Group_map f).hom)) (𝟙 _),
    dsimp at this,
    erw ←this,
    simp only [comp_apply, category.comp_id, ←functor.repr_w_hom,
      functor_to_types.inv_hom_id_app_apply],
    refl,
  end }

noncomputable def unit_iso :
  𝟭 (Group_ C) ≅ Group_to_Functor C ⋙ Functor_to_Group_ C :=
{ hom :=
  { app := λ X,
    { hom := (X.Group_to_Functor_obj.obj ⋙ forget Group).repr_w.inv.app (opposite.op X.G) (𝟙 _),
      mul_comp :=
      begin
        dsimp [Group_to_Functor, Functor_to_Group_],
        simp only [yoneda.naturality, category.comp_id, comp_mul, limits.prod.map_fst,
          limits.prod.map_snd],
        simp only [equiv.mul_def, iso.to_equiv_fun, iso.app_hom,
          functor_to_types.inv_hom_id_app_apply, iso.to_equiv_symm_fun, iso.app_inv, mul_def,
          prod.lift_fst_snd, category.id_comp],
      end,
      one_comp :=
      begin
        dsimp [Group_to_Functor, Functor_to_Group_],
        simp only [equiv.one_def, yoneda.naturality, category.comp_id, iso.to_equiv_symm_fun,
          iso.app_inv, one_def],
        erw [subsingleton.elim (terminal.from (⊤_ C)) (𝟙 _), category.id_comp],
      end,
      inv_comp :=
      begin
        dsimp [Group_to_Functor, Functor_to_Group_],
        simp only [equiv.inv_def, inv_def, yoneda.naturality, category.comp_id, iso.to_equiv_fun,
          iso.app_hom, iso.to_equiv_symm_fun, iso.app_inv, functor.repr_w_hom],
        congr,
        rw ←functor.repr_w_hom,
        sorry,
      end,
       },
    naturality' := sorry },
  inv :=
  { app := λ X,
    { hom := (((Group_to_Functor C).obj X).1 ⋙ forget _).repr_f.app
          (opposite.op (((Group_to_Functor C).obj X).1 ⋙ forget _).repr_X)
          (𝟙 _),
      mul_comp := sorry,
      one_comp := sorry,
      inv_comp := sorry },
    naturality' := sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable def counit_iso :
  Functor_to_Group_ C ⋙ Group_to_Functor C
    ≅ 𝟭 (RepresentableGroupFunctor C) :=
sorry

noncomputable def Group_RepresentableGroupFunctor_equivalence :
  Group_ C ≌ RepresentableGroupFunctor C :=
{ functor := Group_to_Functor C,
  inverse := Functor_to_Group_ C,
  unit_iso := unit_iso C,
  counit_iso := counit_iso C,
  functor_unit_iso_comp' := sorry }

end Group_

abbreviation CommGroup_ := full_subcategory
  (λ G : Group_ C, (limits.prod.braiding G.G G.G).hom ≫ G.mul = G.mul)

@[derive [faithful, full]] def CommGroup_.inclusion : CommGroup_ C ⥤ Group_ C :=
full_subcategory_inclusion _

abbreviation RepresentableCommGroupFunctor :=
  full_subcategory (λ G : Cᵒᵖ ⥤ CommGroup, (G ⋙ forget _).representable)

instance RepresentableCommGroupFunctor.comm_group (G : RepresentableCommGroupFunctor C) (X : Cᵒᵖ) :
  comm_group (G.1.obj X) := by apply_instance

@[derive faithful] def RepresentableCommGroupFunctor_to_RepresentableGroupFunctor :
  RepresentableCommGroupFunctor C ⥤ RepresentableGroupFunctor C :=
full_subcategory_inclusion _ ⋙ full_subcategory.lift _ ((whiskering_right _ _ _).obj
  (forget₂ _ _)) sorry
