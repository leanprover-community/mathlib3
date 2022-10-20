import category_theory.concrete_category.operations
import algebra.category.Group.preadditive

noncomputable theory

namespace category_theory

open limits concrete_category concrete_category.operations opposite category

variables {C : Type*} [category C] (X Y Z W : C)

@[simps]
def yoneda.obj_prod_iso [has_binary_product X Y] :
  yoneda.obj (prod X Y) ≅ concat₂ (yoneda.obj X) (yoneda.obj Y) :=
{ hom := { app := λ Z φ, ⟨φ ≫ limits.prod.fst, φ ≫ limits.prod.snd⟩, },
  inv := { app := λ Z φ, prod.lift φ.1 φ.2, }, }

@[simps]
def yoneda.obj_prod₃_iso [has_binary_product Y Z] [has_binary_product X (prod Y Z)] :
  yoneda.obj (prod X (prod Y Z)) ≅ concat₃ (yoneda.obj X) (yoneda.obj Y) (yoneda.obj Z) :=
{ hom := { app := λ W φ, ⟨φ ≫ limits.prod.fst, φ ≫ limits.prod.snd ≫ limits.prod.fst, φ ≫ limits.prod.snd ≫ limits.prod.snd⟩, },
  inv := { app := λ W φ, prod.lift φ.1 (prod.lift φ.2.1 φ.2.2), }, }

def internal_operation₀ [has_terminal C] := ⊤_ C ⟶ X
def internal_yoneda_operation₀ := (functor.const Cᵒᵖ).obj punit ⟶ yoneda.obj X

@[simps]
def internal_operation₀.yoneda_equiv [has_terminal C] :
  internal_operation₀ X ≃ internal_yoneda_operation₀ X :=
{ to_fun := λ φ,
  { app := λ Y x, terminal.from _ ≫ φ,
    naturality' := λ Y Y' f, begin
      ext1 x,
      simp only [types_comp_apply, yoneda_obj_map, ← assoc],
      congr,
    end, },
  inv_fun := λ τ, τ.app (op (⊤_ C)) punit.star,
  left_inv := λ φ, by { dsimp, convert id_comp φ, },
  right_inv := λ τ, begin
    ext Y x,
    have h := congr_fun (τ.naturality (terminal.from (unop Y)).op) punit.star,
    dsimp at x ⊢ h,
    rw [← h, subsingleton.elim x punit.star],
  end, }

def internal_operation₁_gen := X ⟶ Y
abbreviation internal_operation₁ := internal_operation₁_gen X X
def internal_yoneda_operation₁_gen := yoneda.obj X ⟶ yoneda.obj Y
abbreviation internal_yoneda_operation₁ := internal_yoneda_operation₁_gen X X

@[simps]
def internal_operation₁_gen.yoneda_equiv :
  internal_operation₁_gen X Y ≃ internal_yoneda_operation₁_gen X Y :=
equiv.symm yoneda_equiv

@[simps]
def internal_operation₁.yoneda_equiv :
  internal_operation₁ X ≃ internal_yoneda_operation₁ X :=
equiv.symm yoneda_equiv

def internal_operation₂_gen [has_binary_product X Y] := prod X Y ⟶ Z
abbreviation internal_operation₂ [has_binary_product X X] := internal_operation₂_gen X X X

namespace internal_operation₂

variable {X}

@[simp]
def comm [has_binary_product X X] (oper : internal_operation₂ X) : Prop :=
(limits.prod.braiding X X).hom ≫ oper = oper

@[simp]
def assoc [has_binary_product X X] [has_binary_product X (prod X X)]
  (oper : internal_operation₂ X) : Prop :=
prod.lift (limits.prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.fst) ≫ oper) (limits.prod.snd ≫ limits.prod.snd) ≫ oper =
  prod.lift limits.prod.fst (limits.prod.snd ≫ oper) ≫ oper

@[simp]
def zero_add [has_binary_product X X] [has_terminal C]
  (oper : internal_operation₂ X) (zero : ⊤_ C ⟶ X) : Prop :=
  prod.lift (terminal.from X ≫ zero) (𝟙 X) ≫ oper = 𝟙 X

@[simp]
def add_left_neg [has_binary_product X X] [has_terminal C] (oper : internal_operation₂ X)
  (zero : ⊤_ C ⟶ X) (neg : X ⟶ X) : Prop :=
  prod.lift neg (𝟙 X) ≫ oper = terminal.from X ≫ zero

end internal_operation₂

def internal_yoneda_operation₂_gen := concat₂ (yoneda.obj X) (yoneda.obj Y) ⟶ yoneda.obj Z
abbreviation internal_yoneda_operation₂ := internal_yoneda_operation₂_gen X X X

@[simps]
def internal_yoneda_operation₂_gen.equiv [has_binary_product X Y] :
  internal_yoneda_operation₂_gen X Y Z ≃
  (yoneda.obj (prod X Y) ⟶ yoneda.obj Z) :=
{ to_fun := λ f, (yoneda.obj_prod_iso X Y).hom ≫ f,
  inv_fun := λ f, (yoneda.obj_prod_iso X Y).inv ≫ f,
  left_inv := λ f, by { simp only [iso.inv_hom_id_assoc], },
  right_inv := λ f, by { simp only [iso.hom_inv_id_assoc], }, }

@[simps]
def internal_operation₂_gen.yoneda_equiv [has_binary_product X Y] :
  internal_operation₂_gen X Y Z ≃ internal_yoneda_operation₂_gen X Y Z :=
yoneda_equiv.symm.trans (internal_yoneda_operation₂_gen.equiv X Y Z).symm

namespace internal_operation₂

@[simps]
def yoneda_equiv [has_binary_product X X] :
  internal_operation₂ X ≃ internal_yoneda_operation₂ X :=
  internal_operation₂_gen.yoneda_equiv X X X

lemma yoneda_equiv_comm [has_binary_product X X]
  (oper : internal_operation₂ X) (oper_comm : oper.comm) :
  (yoneda_equiv X) oper = lift₂ pr₂ pr₁ ≫ (yoneda_equiv X) oper :=
(yoneda_equiv X).symm.injective begin
  dsimp at oper_comm,
  simp only [yoneda_equiv_symm_apply, yoneda_equiv_apply_app, prod.lift_fst_snd,
    functor_to_types.comp, lift₂_app, pr₂_app, pr₁_app, oper_comm],
  dsimp,
  rw id_comp,
end

end internal_operation₂

def internal_operation₃_gen [has_binary_product Y Z] [has_binary_product X (prod Y Z)] :=
prod X (prod Y Z) ⟶ W
abbreviation internal_operation₃ [has_binary_product X X] [has_binary_product X (prod X X)] :=
internal_operation₃_gen X X X X

def internal_yoneda_operation₃_gen := concat₃ (yoneda.obj X) (yoneda.obj Y) (yoneda.obj Z) ⟶ yoneda.obj W
abbreviation internal_yoneda_operation₃ := internal_yoneda_operation₃_gen X X X X

@[simps]
def internal_yoneda_operation₃_gen.equiv [has_binary_product Y Z] [has_binary_product X (prod Y Z)] :
  internal_yoneda_operation₃_gen X Y Z W ≃
  (yoneda.obj (prod X (prod Y Z)) ⟶ yoneda.obj W) :=
{ to_fun := λ f, (yoneda.obj_prod₃_iso X Y Z).hom ≫ f,
  inv_fun := λ f, (yoneda.obj_prod₃_iso X Y Z).inv ≫ f,
  left_inv := λ f, by simp only [iso.inv_hom_id_assoc],
  right_inv := λ f, by simp only [iso.hom_inv_id_assoc], }

@[simps]
def internal_operation₃_gen.yoneda_equiv [has_binary_product Y Z] [has_binary_product X (prod Y Z)] :
  internal_operation₃_gen X Y Z W ≃ internal_yoneda_operation₃_gen X Y Z W :=
yoneda_equiv.symm.trans (internal_yoneda_operation₃_gen.equiv X Y Z W).symm

@[simps]
def internal_operation₃.yoneda_equiv [has_binary_product X X] [has_binary_product X (prod X X)] :
  internal_operation₃ X ≃ internal_yoneda_operation₃ X :=
internal_operation₃_gen.yoneda_equiv X X X X

namespace internal_operation₂

lemma yoneda_equiv_assoc [has_binary_product X X] [has_binary_product X (prod X X)]
  (oper : internal_operation₂ X) (oper_assoc : oper.assoc) :
  lift₂ (pr₁₂_₃ ≫ (yoneda_equiv X) oper) pr₃_₃ ≫ (yoneda_equiv X) oper =
    lift₂ pr₁_₃ (pr₂₃_₃ ≫ (yoneda_equiv X) oper) ≫ (yoneda_equiv X) oper :=
(internal_operation₃.yoneda_equiv X).symm.injective begin
  dsimp at oper_assoc,
  simp only [internal_operation₃.yoneda_equiv_symm_apply, functor_to_types.comp,
    lift₂_app, pr₁₂_₃_app, yoneda_equiv_apply_app, pr₃_₃_app, pr₁_₃_app, pr₂₃_₃_app,
    oper_assoc],
  congr,
  tidy,
end

lemma yoneda_equiv_zero_add [has_terminal C] [has_binary_product X X]
  (oper : internal_operation₂ X) (zero : internal_operation₀ X) (zero_oper : oper.zero_add zero) :
  lift₂
    (concrete_category.to_functor_const_punit ≫ internal_operation₀.yoneda_equiv X zero)
    (𝟙 _) ≫ (yoneda_equiv X) oper = 𝟙 _  :=
(internal_operation₁.yoneda_equiv X).symm.injective
  (by simpa only [internal_operation₁.yoneda_equiv_symm_apply, functor_to_types.comp, lift₂_app,
    internal_operation₀.yoneda_equiv_apply_app, nat_trans.id_app, types_id_apply, yoneda_equiv_apply_app]
    using zero_oper)

lemma yoneda_equiv_add_left_neg [has_terminal C] [has_binary_product X X]
  (oper : internal_operation₂ X) (zero : internal_operation₀ X) (neg : internal_operation₁ X)
    (oper_left_neg : oper.add_left_neg zero neg) :
  lift₂ (internal_operation₁.yoneda_equiv X neg)(𝟙 _) ≫ (yoneda_equiv X) oper =
    to_functor_const_punit ≫ internal_operation₀.yoneda_equiv X zero :=
(internal_operation₁.yoneda_equiv X).symm.injective
begin
  simp only [internal_operation₁.yoneda_equiv_symm_apply, functor_to_types.comp,
    lift₂_app, internal_operation₁.yoneda_equiv_apply_app, nat_trans.id_app,
    types_id_apply, yoneda_equiv_apply_app, internal_operation₀.yoneda_equiv_apply_app],
  convert oper_left_neg,
  apply id_comp,
end

end internal_operation₂

end category_theory
