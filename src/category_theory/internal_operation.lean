import category_theory.concrete_category.operations
import algebra.category.Group.preadditive
import category_theory.limits.preserves.shapes.binary_products

noncomputable theory

namespace category_theory

open limits concrete_category concrete_category.operations opposite category

variables {C D : Type*} [category C] [category D] (X Y Z W : C)

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

variable {X}

def internal_operation₀.map [has_terminal C] [has_terminal D]
  (oper : internal_operation₀ X) (F : C ⥤ D)
  [preserves_limit (functor.empty.{0} C) F] :
  internal_operation₀ (F.obj X) :=
(limits.preserves_terminal.iso F).inv ≫ F.map oper

variable (X)

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

variables {X Y}
def internal_operation₁_gen.map (oper : internal_operation₁_gen X Y) (F : C ⥤ D) :
  internal_operation₁_gen (F.obj X) (F.obj Y) :=
F.map oper

variables (X Y)
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

variables {X Y Z}

def internal_operation₂_gen.map [has_binary_product X Y]
  (oper : internal_operation₂_gen X Y Z) (F : C ⥤ D)
  [has_binary_product (F.obj X) (F.obj Y)]
  [preserves_limit (pair X Y) F] :
  internal_operation₂_gen (F.obj X) (F.obj Y) (F.obj Z) :=
(preserves_limit_pair.iso F X Y).inv ≫ F.map oper

variables (X Y Z)
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

lemma yoneda_equiv_symm_comm [has_binary_product X X]
  (oper : internal_yoneda_operation₂ X)
  (oper_comm : oper = lift₂ pr₂ pr₁ ≫ oper) : ((yoneda_equiv X).symm oper).comm :=
begin
  dsimp,
  convert congr_arg (yoneda_equiv X).symm oper_comm.symm,
  simp only [yoneda_equiv_symm_apply, functor_to_types.comp, lift₂_app, pr₂_app, pr₁_app],
  convert congr_fun (oper.naturality (prod.lift limits.prod.snd limits.prod.fst : prod X X ⟶ _).op).symm ⟨limits.prod.fst, limits.prod.snd⟩,
  tidy,
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

variables {X Y Z W}

def internal_operation₃_gen.map [has_binary_product Y Z] [has_binary_product X (prod Y Z)]
  (oper : internal_operation₃_gen X Y Z W) (F : C ⥤ D)
  [has_binary_product (F.obj Y) (F.obj Z)]
  [has_binary_product (F.obj X) (F.obj (prod Y Z))]
  [has_binary_product (F.obj X) (prod (F.obj Y) (F.obj Z))]
  [preserves_limit (pair Y Z) F] [preserves_limit (pair X (prod Y Z)) F] :
  internal_operation₃_gen (F.obj X) (F.obj Y) (F.obj Z) (F.obj W) :=
limits.prod.map (𝟙 _) (preserves_limit_pair.iso F Y Z).inv ≫
    (preserves_limit_pair.iso F X (prod Y Z)).inv ≫ F.map oper

variables (X Y Z W)

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

lemma yoneda_equiv_symm_assoc [has_binary_product X X] [has_binary_product X (prod X X)]
  (oper : internal_yoneda_operation₂ X)
  (oper_assoc : lift₂ (pr₁₂_₃ ≫ oper) pr₃_₃ ≫ oper = lift₂ pr₁_₃ (pr₂₃_₃ ≫ oper) ≫ oper) :
  ((yoneda_equiv X).symm oper).assoc :=
begin
  dsimp,
  convert congr_arg (internal_operation₃.yoneda_equiv X).symm oper_assoc,
  { sorry, },
  { sorry, },
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

namespace internal_yoneda_operation₂_gen

variables (bil : internal_yoneda_operation₂_gen X Y Z) {X Y Z}

@[simp]
def right_distrib (add₁ : internal_yoneda_operation₂ X) (add₃ : internal_yoneda_operation₂ Z) : Prop :=
  lift₂ (pr₁₂_₃ ≫ add₁) pr₃_₃ ≫ bil = lift₂ (pr₁₃_₃ ≫ bil) (pr₂₃_₃ ≫ bil) ≫ add₃

@[simp]
def left_distrib (add₂ : internal_yoneda_operation₂ Y) (add₃ : internal_yoneda_operation₂ Z) : Prop :=
  lift₂ pr₁_₃ (pr₂₃_₃ ≫ add₂) ≫ bil = lift₂ (pr₁₂_₃ ≫ bil) (pr₁₃_₃ ≫ bil) ≫ add₃

@[simp]
def one_smul (smul : internal_yoneda_operation₂_gen X Y Y) (one : internal_yoneda_operation₀ X) : Prop :=
  lift₂ (to_functor_const_punit ≫ one) (𝟙 _) ≫ smul = 𝟙 _

@[simp]
def smul_one (smul : internal_yoneda_operation₂_gen Y X Y) (one : internal_yoneda_operation₀ X) : Prop :=
  lift₂ (𝟙 _) (to_functor_const_punit ≫ one) ≫ smul = 𝟙 _

@[simp]
def mul_smul (smul : internal_yoneda_operation₂_gen X Y Y) (mul : internal_yoneda_operation₂ X) : Prop :=
lift₂ (pr₁₂_₃ ≫ mul) pr₃_₃ ≫ smul =
  lift₂ pr₁_₃ (pr₂₃_₃ ≫ smul) ≫ smul

end internal_yoneda_operation₂_gen

namespace internal_operation₂_gen

variables {X Y Z}

@[simp]
def right_distrib [has_binary_product X X] [has_binary_product Z Z] [has_binary_product X Y]
  [has_binary_product X (prod X Y)]
  (bil : internal_operation₂_gen X Y Z)
  (add₁ : internal_operation₂ X) (add₃ : internal_operation₂ Z) : Prop :=
prod.lift (prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.fst) ≫ add₁)
  (limits.prod.snd ≫ limits.prod.snd) ≫ bil =
prod.lift
  (prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.snd) ≫ bil)
  (limits.prod.snd ≫ bil) ≫ add₃

lemma yoneda_equiv_right_distrib
  [has_binary_product X X] [has_binary_product Z Z] [has_binary_product X Y]
  [has_binary_product X (prod X Y)]
  (bil : internal_operation₂_gen X Y Z)
  (add₁ : internal_operation₂ X) (add₃ : internal_operation₂ Z)
  (h : bil.right_distrib add₁ add₃) :
  (yoneda_equiv _ _ _ bil).right_distrib
    (internal_operation₂.yoneda_equiv _ add₁)
    (internal_operation₂.yoneda_equiv _ add₃) :=
(internal_operation₃_gen.yoneda_equiv X X Y Z).symm.injective begin
  simp only [internal_operation₃_gen.yoneda_equiv_symm_apply, functor_to_types.comp,
    lift₂_app, pr₁₂_₃_app, internal_operation₂.yoneda_equiv_apply_app, pr₃_₃_app,
    yoneda_equiv_apply_app, pr₁₃_₃_app, pr₂₃_₃_app],
  convert h,
  tidy,
end

@[simp]
def left_distrib [has_binary_product Y Y] [has_binary_product Z Z]
  [has_binary_product X Y]
  [has_binary_product X (prod Y Y)]
  (bil : internal_operation₂_gen X Y Z)
  (add₂ : internal_operation₂ Y) (add₃ : internal_operation₂ Z) : Prop :=
prod.lift limits.prod.fst (limits.prod.snd ≫ add₂) ≫ bil =
  prod.lift (prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.fst) ≫ bil)
    (prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.snd) ≫ bil) ≫ add₃

lemma yoneda_equiv_left_distrib
  [has_binary_product Y Y] [has_binary_product Z Z]
  [has_binary_product X Y]
  [has_binary_product X (prod Y Y)]
  (bil : internal_operation₂_gen X Y Z)
  (add₂ : internal_operation₂ Y) (add₃ : internal_operation₂ Z)
  (h : bil.left_distrib add₂ add₃) :
  (yoneda_equiv _ _ _ bil).left_distrib
    (internal_operation₂.yoneda_equiv _ add₂)
    (internal_operation₂.yoneda_equiv _ add₃) :=
(internal_operation₃_gen.yoneda_equiv X Y Y Z).symm.injective begin
  simp only [internal_operation₃_gen.yoneda_equiv_symm_apply, functor_to_types.comp,
    lift₂_app, pr₁_₃_app, pr₂₃_₃_app, internal_operation₂.yoneda_equiv_apply_app,
    yoneda_equiv_apply_app, pr₁₂_₃_app, pr₁₃_₃_app],
  convert h,
  tidy,
end

@[simp]
def one_smul [has_binary_product X Y] [has_terminal C]
  (smul : internal_operation₂_gen X Y Y) (one : ⊤_ C ⟶ X) : Prop :=
  prod.lift (terminal.from Y ≫ one) (𝟙 Y) ≫ smul = 𝟙 Y

lemma yoneda_equiv_one_smul [has_binary_product X Y] [has_terminal C]
  (smul : internal_operation₂_gen X Y Y) (one : internal_operation₀ X)
  (one_smul : smul.one_smul one) :
  (yoneda_equiv X Y Y smul).one_smul (internal_operation₀.yoneda_equiv X one) :=
(internal_operation₁.yoneda_equiv Y).symm.injective (by simpa using one_smul)

@[simp]
def smul_one [has_binary_product Y X] [has_terminal C]
  (smul : internal_operation₂_gen Y X Y) (one : ⊤_ C ⟶ X) : Prop :=
  prod.lift (𝟙 Y) (terminal.from Y ≫ one)  ≫ smul = 𝟙 Y

lemma yoneda_equiv_smul_one [has_binary_product Y X] [has_terminal C]
  (smul : internal_operation₂_gen Y X Y) (one : internal_operation₀ X)
  (smul_one : smul.smul_one one) :
  (yoneda_equiv Y X Y smul).smul_one (internal_operation₀.yoneda_equiv X one) :=
(internal_operation₁.yoneda_equiv Y).symm.injective (by simpa using smul_one)

@[simp]
def mul_smul [has_binary_product X Y] [has_binary_product X X] [has_binary_product X (prod X Y)]
  (smul : internal_operation₂_gen X Y Y) (mul : internal_operation₂ X) : Prop :=
prod.lift (prod.lift limits.prod.fst (limits.prod.snd ≫ limits.prod.fst) ≫ mul)
    (limits.prod.snd ≫ limits.prod.snd) ≫ smul =
  prod.lift limits.prod.fst (limits.prod.snd ≫ smul) ≫ smul

lemma yoneda_equiv_mul_smul [has_binary_product X Y] [has_binary_product X X] [has_binary_product X (prod X Y)]
  (smul : internal_operation₂_gen X Y Y) (mul : internal_operation₂ X)
  (mul_smul : smul.mul_smul mul) :
  (yoneda_equiv X Y Y smul).mul_smul (internal_operation₂.yoneda_equiv X mul) :=
(internal_operation₃_gen.yoneda_equiv X X Y Y).symm.injective begin
  simp only [internal_operation₃_gen.yoneda_equiv_symm_apply, functor_to_types.comp,
    lift₂_app, pr₁₂_₃_app, internal_operation₂.yoneda_equiv_apply_app, pr₃_₃_app,
    yoneda_equiv_apply_app, pr₁_₃_app, pr₂₃_₃_app],
  convert mul_smul,
  tidy,
end

end internal_operation₂_gen

end category_theory
