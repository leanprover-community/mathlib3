import category_theory.concrete_category.internal
import algebra.category.Group.preadditive
import category_theory.internal_operation
import category_theory.limits.shapes.finite_products

universe u

noncomputable theory

def Ab.mk (A : Type*) (zero' : A) (neg' : A ⟶ A) (add' : A × A → A)
  (add_assoc' : ∀ (x y z : A), add' ⟨add' ⟨x, y⟩, z⟩ = add' ⟨x, add' ⟨y, z⟩⟩)
  (add_comm' : ∀ (x y : A), add' ⟨x, y⟩ = add' ⟨y, x⟩)
  (zero_add' : ∀ (x : A), add' ⟨zero', x⟩ = x)
  (add_left_neg' : ∀ (x : A), add' ⟨neg' x, x⟩ = zero') :
  Ab :=
⟨A,
{ zero := zero',
  neg := neg',
  add := λ x y, add' ⟨x, y⟩,
  add_assoc := add_assoc',
  add_comm := add_comm',
  zero_add := zero_add',
  add_zero := λ x, by { change add' ⟨x, zero'⟩ = x, rw [add_comm', zero_add'], },
  add_left_neg := add_left_neg', }⟩

namespace category_theory

open opposite limits

namespace concrete_category

namespace operations

def Ab_zero : operation₀ Ab :=
{ app := λ M, 0, }

def Ab_neg : operation₁ Ab :=
{ app := λ M x, -x, }

def Ab_add : operation₂ Ab :=
{ app := λ M x, x.1 + x.2, }

lemma Ab_add_comm : Ab_add.comm :=
by { ext M x, apply add_comm, }

lemma Ab_add_assoc : Ab_add.assoc :=
by { ext M x, apply add_assoc, }

lemma Ab_zero_add : Ab_add.zero_add Ab_zero :=
by { ext M x, apply zero_add, }

lemma Ab_add_left_neg : Ab_add.add_left_neg Ab_zero Ab_neg :=
by { ext M x, apply add_left_neg, }

end operations

namespace internal

namespace Ab

open concrete_category.operations limits

variables {C D : Type*} [category C] [category D] (M : internal Ab C)

instance add_comm_group_presheaf_type_obj {Y : Cᵒᵖ} :
add_comm_group (M.presheaf_type.obj Y) :=
by { dsimp [presheaf_type], apply_instance, }

instance add_comm_group_presheaf_comp_forget_obj {Y : Cᵒᵖ} :
add_comm_group ((M.presheaf ⋙ forget Ab).obj Y) :=
by { dsimp [presheaf_type], apply_instance, }

@[simps]
def mk (X : C)
  (yoneda_zero : (functor.const Cᵒᵖ).obj punit ⟶ yoneda.obj X)
  (yoneda_neg : yoneda.obj X ⟶ yoneda.obj X)
  (yoneda_add : concat₂ (yoneda.obj X) (yoneda.obj X) ⟶ yoneda.obj X)
  (yoneda_add_comm : yoneda_add = lift₂ pr₂ pr₁ ≫ yoneda_add)
  (yoneda_add_assoc : lift₂ (pr₁₂_₃ ≫ yoneda_add) pr₃_₃ ≫ yoneda_add =
    lift₂ pr₁_₃ (pr₂₃_₃ ≫ yoneda_add) ≫ yoneda_add)
  (yoneda_zero_add : lift₂ (to_functor_const_punit ≫ yoneda_zero) (𝟙 _) ≫ yoneda_add = 𝟙 _ )
  (yoneda_add_left_neg : lift₂ yoneda_neg (𝟙 _) ≫ yoneda_add = to_functor_const_punit ≫ yoneda_zero) :
  internal Ab C :=
{ obj := X,
  presheaf :=
  { obj := λ Y, begin
      refine Ab.mk ((yoneda.obj X).obj Y) (yoneda_zero.app Y punit.star)
        (yoneda_neg.app Y) (yoneda_add.app Y) _ _ _ _,
      { intros x y z,
        exact congr_fun (congr_app yoneda_add_assoc Y) ⟨x, ⟨y, z⟩⟩, },
      { intros x y,
        exact congr_fun (congr_app yoneda_add_comm Y) ⟨x, y⟩, },
      { exact congr_fun (congr_app yoneda_zero_add Y), },
      { exact congr_fun (congr_app yoneda_add_left_neg Y), },
    end,
    map := λ Y Y' f, ⟨(yoneda.obj X).map f,
      congr_fun (yoneda_zero.naturality f).symm punit.star,
      λ x y, congr_fun (yoneda_add.naturality f).symm ⟨x, y⟩⟩, },
  iso := by refl, }

@[simps]
def mk' (X : C) [has_terminal C] [has_binary_product X X] [has_binary_product X (prod X X)]
  (zero : ⊤_ C ⟶ X) (neg : X ⟶ X) (add : prod X X ⟶ X) (add_comm : internal_operation₂.comm add)
  (add_assoc : internal_operation₂.assoc add) (add_zero : internal_operation₂.zero_add add zero)
  (add_left_neg : internal_operation₂.add_left_neg add zero neg) :
  internal Ab C :=
Ab.mk X (internal_operation₀.yoneda_equiv X zero)
  (internal_operation₁.yoneda_equiv X neg)
  (internal_operation₂.yoneda_equiv X add)
  (internal_operation₂.yoneda_equiv_comm X add add_comm)
  (internal_operation₂.yoneda_equiv_assoc X add add_assoc)
  (internal_operation₂.yoneda_equiv_zero_add X add zero add_zero)
  (internal_operation₂.yoneda_equiv_add_left_neg X add zero neg add_left_neg)

def yoneda_operation_zero := Ab_zero.to_internal_yoneda_operation₀ M
def yoneda_operation_neg := Ab_neg.to_internal_yoneda_operation₁ M
def yoneda_operation_add := Ab_add.to_internal_yoneda_operation₂ M
def zero [has_terminal C] := (internal_operation₀.yoneda_equiv _).symm (yoneda_operation_zero M)
def neg := (internal_operation₁.yoneda_equiv _).symm (yoneda_operation_neg M)
def add [has_binary_product M.obj M.obj]:= (internal_operation₂.yoneda_equiv _).symm (yoneda_operation_add M)

lemma yoneda_operation_add_comm : yoneda_operation_add M = lift₂ pr₂ pr₁ ≫ yoneda_operation_add M :=
Ab_add.to_internal_yoneda_operation₂_comm M Ab_add_comm

lemma yoneda_operation_add_assoc :
  lift₂ (pr₁₂_₃ ≫ yoneda_operation_add M) pr₃_₃ ≫ yoneda_operation_add M =
    lift₂ pr₁_₃ (pr₂₃_₃ ≫ yoneda_operation_add M) ≫ yoneda_operation_add M :=
Ab_add.to_internal_yoneda_operation₂_assoc M Ab_add_assoc

lemma yoneda_operation_zero_add :
  lift₂ (to_functor_const_punit ≫ yoneda_operation_zero M) (𝟙 _) ≫
    yoneda_operation_add M = 𝟙 _  :=
Ab_add.to_internal_yoneda_operation₂_zero_add M Ab_zero Ab_zero_add

lemma yoneda_operation_add_left_neg :
lift₂ (yoneda_operation_neg M) (𝟙 _) ≫ yoneda_operation_add M =
  to_functor_const_punit ≫ yoneda_operation_zero M :=
Ab_add.to_internal_yoneda_operation₂_add_left_neg M Ab_zero Ab_neg Ab_add_left_neg

lemma add_comm [has_binary_product M.obj M.obj] : (add M).comm :=
internal_operation₂.yoneda_equiv_symm_comm M.obj _ (yoneda_operation_add_comm M)

lemma add_assoc [has_binary_product M.obj M.obj] [has_binary_product M.obj (prod M.obj M.obj)] :
  (add M).assoc :=
internal_operation₂.yoneda_equiv_symm_assoc M.obj _ (yoneda_operation_add_assoc M)

variable {M}

@[simp]
lemma iso_hom_app_yoneda_operation_add_app {Y : Cᵒᵖ} (x₁ x₂ : (yoneda.obj M.obj).obj Y) :
  M.iso.hom.app _ ((yoneda_operation_add M).app Y ⟨x₁, x₂⟩) =
  M.iso.hom.app Y x₁ + M.iso.hom.app Y x₂ :=
begin
  dsimp [yoneda_operation_add],
  simpa only [functor_to_types.inv_hom_id_app_apply],
end

lemma yoneda_operation_add_app_eq {Y : Cᵒᵖ} (x₁ x₂ : (yoneda.obj M.obj).obj Y)
  [has_binary_product M.obj M.obj] :
  (yoneda_operation_add M).app Y ⟨x₁, x₂⟩ = prod.lift x₁ x₂ ≫ add M :=
internal_operation₂_gen.app_eq_comp_yoneda_equiv (yoneda_operation_add M) _ _

lemma iso_inv_app_add {Y : Cᵒᵖ} (x₁ x₂ : M.presheaf.obj Y) :
  M.iso.inv.app Y (x₁ + x₂) =
    (yoneda_operation_add M).app Y ⟨M.iso.inv.app Y x₁, M.iso.inv.app Y x₂⟩ :=
begin
  have h : function.bijective (M.iso.hom.app Y),
  { rw ← is_iso_iff_bijective,
    apply_instance, },
  obtain ⟨y₁, hy₁⟩ := h.surjective x₁,
  obtain ⟨y₂, hy₂⟩ := h.surjective x₂,
  simp only [← hy₁, ← hy₂, functor_to_types.hom_inv_id_app_apply],
  apply h.1,
  rw iso_hom_app_yoneda_operation_add_app y₁ y₂,
  simp only [functor_to_types.inv_hom_id_app_apply],
end

def hom.mk' (X₁ X₂ : internal Ab C) [has_binary_product X₁.obj X₁.obj]
  [has_binary_product X₂.obj X₂.obj] (f : X₁.obj ⟶ X₂.obj)
  (hf : add X₁ ≫ f = limits.prod.map f f ≫ add X₂) :
  X₁ ⟶ X₂ :=
{ app := λ Y, add_monoid_hom.mk' ((internal_yoneda_operation₁_gen.on_internal_presheaf
    (internal_operation₁_gen.yoneda_equiv X₁.obj X₂.obj f)).app Y) (λ a b, begin
      dsimp at a b ⊢,
      have h := congr_fun (congr_app (_root_.congr_arg internal_yoneda_operation₂_gen.on_internal_presheaf
        (_root_.congr_arg (internal_operation₂_gen.yoneda_equiv _ _ _) hf)) Y) ⟨a, b⟩,
      dsimp at h,
      rw [iso_inv_app_add, yoneda_operation_add_app_eq, category.assoc, h,
        ← iso_hom_app_yoneda_operation_add_app, yoneda_operation_add_app_eq, prod.lift_map_assoc],
    end),
  naturality' := λ Y Y' g, begin
    ext x,
    exact congr_fun ((internal_yoneda_operation₁_gen.on_internal_presheaf
      (internal_operation₁_gen.yoneda_equiv X₁.obj X₂.obj f)).naturality g) x,
  end, }

variables (M₁ M₂ M₃ : internal Ab C)

structure yoneda_bilinear :=
(φ : internal_yoneda_operation₂_gen M₁.obj M₂.obj M₃.obj)
(right_distrib : internal_yoneda_operation₂_gen.right_distrib φ (Ab.yoneda_operation_add _)
    (Ab.yoneda_operation_add _))
(left_distrib : internal_yoneda_operation₂_gen.left_distrib φ (Ab.yoneda_operation_add _)
    (Ab.yoneda_operation_add _))

namespace yoneda_bilinear

variables (bil : yoneda_bilinear M₁ M₂ M₃) {M₁ M₂ M₃} {Y Y' : Cᵒᵖ}

@[simp]
lemma on_internal_presheaf_right_distrib
  (x₁ x₁' : M₁.presheaf_type.obj Y) (x₂ : M₂.presheaf_type.obj Y) :
bil.φ.on_internal_presheaf_curry (x₁ + x₁') x₂ =
  bil.φ.on_internal_presheaf_curry x₁ x₂ + bil.φ.on_internal_presheaf_curry x₁' x₂ :=
begin
  have h := congr_fun (nat_trans.congr_app bil.right_distrib Y)
    ⟨M₁.iso.inv.app _ x₁, M₁.iso.inv.app _ x₁', M₂.iso.inv.app _ x₂⟩,
  have h₂ := congr_arg (M₃.iso.hom.app _) h,
  simp only [functor_to_types.comp, lift₂_app, pr₁₂_₃_app, pr₃_₃_app, has_coe_to_fun_Type,
    pr₁₃_₃_app, pr₂₃_₃_app, iso_hom_app_yoneda_operation_add_app] at h₂,
  convert h₂;
  { dsimp, simp only [functor_to_types.inv_hom_id_app_apply], },
end

@[simp]
lemma on_internal_presheaf_left_distrib
  (x₁ : M₁.presheaf_type.obj Y) (x₂ x₂': M₂.presheaf_type.obj Y) :
bil.φ.on_internal_presheaf_curry x₁ (x₂ + x₂') =
  bil.φ.on_internal_presheaf_curry x₁ x₂ + bil.φ.on_internal_presheaf_curry x₁ x₂' :=
begin
  have h := congr_fun (nat_trans.congr_app bil.left_distrib Y)
    ⟨M₁.iso.inv.app _ x₁, M₂.iso.inv.app _ x₂, M₂.iso.inv.app _ x₂'⟩,
  have h₂ := congr_arg (M₃.iso.hom.app _) h,
  simp only [functor_to_types.comp, lift₂_app, pr₁_₃_app, pr₂₃_₃_app,
    has_coe_to_fun_Type, pr₁₂_₃_app, pr₁₃_₃_app, iso_hom_app_yoneda_operation_add_app] at h₂,
  convert h₂;
  { dsimp, simp only [functor_to_types.inv_hom_id_app_apply], },
end

end yoneda_bilinear

variable (M)

@[simps]
def apply_functor (F : C ⥤ D) [has_terminal C] [has_terminal D]
  [has_binary_product M.obj M.obj] [has_binary_product (F.obj M.obj) (F.obj M.obj)]
  [has_binary_product (F.obj M.obj) (prod (F.obj M.obj) (F.obj M.obj))]
  [preserves_limit (functor.empty.{0} C) F] [preserves_limit (pair M.obj M.obj) F] :
  internal Ab D :=
mk' (F.obj M.obj) ((zero M).map F) ((neg M).map F) ((add M).map F)
  ((add_comm M).map F) sorry sorry sorry

variables {M₁ M₂}

@[simps]
def apply_functor_map (F : C ⥤ D) [has_terminal C] [has_terminal D]
  [has_binary_product M₁.obj M₁.obj] [has_binary_product (F.obj M₁.obj) (F.obj M₁.obj)]
  [has_binary_product (F.obj M₁.obj) (prod (F.obj M₁.obj) (F.obj M₁.obj))]
  [preserves_limit (functor.empty.{0} C) F] [preserves_limit (pair M₁.obj M₁.obj) F]
  [has_binary_product M₂.obj M₂.obj] [has_binary_product (F.obj M₂.obj) (F.obj M₂.obj)]
  [has_binary_product (F.obj M₂.obj) (prod (F.obj M₂.obj) (F.obj M₂.obj))]
  [preserves_limit (pair M₂.obj M₂.obj) F] (f : M₁ ⟶ M₂) :
  apply_functor M₁ F ⟶ apply_functor M₂ F :=
{ app := λ Y, add_monoid_hom.mk' (((internal_operation₁_gen.yoneda_equiv _ _)
      (internal_operation₁_gen.map ((internal.obj_functor Ab C).map f) F)).app Y) sorry, }

end Ab

end internal

end concrete_category

namespace functor

open limits concrete_category

variables {C D : Type*} [category C] [category D] (F : C ⥤ D)
  [has_finite_products C] [has_finite_products D]
  [preserves_limits_of_shape (discrete walking_pair) F]
  [preserves_limit (empty.{0} C) F]

include F

@[simps]
def map_internal_Ab : internal Ab C ⥤ internal Ab D :=
{ obj := λ M, internal.Ab.apply_functor M F,
  map := λ M₁ M₂ f, internal.Ab.apply_functor_map F f,
  map_id' := λ M, begin
    ext Y x,
    dsimp [internal_operation₁_gen.map],
    simpa only [functor.map_id, category.comp_id],
  end,
  map_comp' := λ M₁ M₂ M₃ f g, begin
    ext Y x,
    dsimp [internal_operation₁_gen.map],
    erw [nat_trans.comp_app, functor.map_comp, functor.map_comp, ← category.assoc],
    refl,
  end, }

end functor

namespace concrete_category

namespace internal

namespace Ab

namespace equivalence

open operations

instance (M : Ab.{u}) (Y : Type.{u}ᵒᵖ) :
  add_comm_group ((yoneda.obj ((forget Ab).obj M)).obj Y) :=
by { dsimp, apply_instance, }

@[simps]
def functor : Ab.{u} ⥤ internal Ab Type.{u} :=
{ obj := λ M, mk ((forget Ab).obj M) { app := λ Y s, 0, } { app := λ Y x, -x, }
    { app := λ Y x, x.1 + x.2, }
    (by { ext Y x a, apply _root_.add_comm, })
    (by { ext Y x a, apply _root_.add_assoc, })
    (by { ext Y x a, apply zero_add, })
    (by { ext Y x a, apply add_left_neg, }),
  map := λ M₁ M₂ f,
  { app := λ Y, add_monoid_hom.mk' (λ g, f ∘ g) (by tidy), }, }

@[simps]
def inverse : internal Ab Type.{u} ⥤ Ab.{u} :=
internal.presheaf_functor _ _ ⋙ (evaluation _ _).obj (op punit)

def unit_iso : (𝟭 Ab.{u}) ≅ equivalence.functor ⋙ equivalence.inverse :=
nat_iso.of_components (λ M,
  { hom := add_monoid_hom.mk' (λ x s, x) (by tidy),
    inv := add_monoid_hom.mk' (λ x, x punit.star) (by tidy),
    hom_inv_id' := by tidy,
    inv_hom_id' := by tidy, }) (by tidy)

@[simps]
def counit_iso_inv (M : internal Ab Type.{u}) :
  M ⟶ (inverse ⋙ functor).obj M :=
{ app := λ Y, add_monoid_hom.mk' (λ f x,
  M.iso.hom.app _ ((by exact λ s, x) ≫ M.iso.inv.app _ f)) (λ f g, begin
    ext,
    dsimp at f g ⊢,
    rw [← iso_hom_app_yoneda_operation_add_app, iso_inv_app_add],
    congr' 1,
    let x' : punit ⟶ unop Y := λ s, x,
    have h := congr_fun ((yoneda_operation_add M).naturality x'.op) ⟨M.iso.inv.app _ f, M.iso.inv.app _ g⟩,
    exact h.symm,
  end),
  naturality' := sorry, }

@[simps]
def counit_iso_hom (M : internal Ab Type.{u}) :
  (inverse ⋙ functor).obj M ⟶ M :=
{ app := λ Y, add_monoid_hom.mk' (λ f, M.iso.hom.app _ (λ x, M.iso.inv.app _ (f x) punit.star))
    (begin sorry, end),
  naturality' := sorry, }

@[simps]
def counit_iso : equivalence.inverse ⋙ equivalence.functor ≅ 𝟭 (internal Ab Type.{u}) :=
nat_iso.of_components (λ M,
  { hom := counit_iso_hom M,
    inv := counit_iso_inv M,
    hom_inv_id' := begin
      ext Y : 2,
      refine (nat_trans.comp_app (counit_iso_hom M) (counit_iso_inv M) Y).trans _,
      ext f x,
      dsimp,
      simp only [comp_apply, add_monoid_hom.mk'_apply, functor_to_types.hom_inv_id_app_apply],
      erw id_apply,
      have h : is_iso (M.iso.inv.app (op punit)) := infer_instance,
      rw is_iso_iff_bijective at h,
      apply h.1,
      simp only [functor_to_types.hom_inv_id_app_apply],
      ext u,
      have hu := subsingleton.elim u punit.star,
      subst hu,
      refl,
    end,
    inv_hom_id' := begin
      ext Y : 2,
      refine (nat_trans.comp_app (counit_iso_inv M) (counit_iso_hom M) Y).trans _,
      ext f x,
      dsimp,
      simpa only [comp_apply, add_monoid_hom.mk'_apply, functor_to_types.hom_inv_id_app_apply,
        types_comp_apply, functor_to_types.inv_hom_id_app_apply],
    end, }) sorry

end equivalence

def equivalence : Ab.{u} ≌ internal Ab Type.{u} :=
{ functor := equivalence.functor,
  inverse := equivalence.inverse,
  unit_iso := equivalence.unit_iso,
  counit_iso := equivalence.counit_iso, }

end Ab

end internal

end concrete_category

end category_theory
