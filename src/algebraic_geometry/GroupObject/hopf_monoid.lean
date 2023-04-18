import category_theory.monoidal.braided category_theory.monoidal.Mon_ category_theory.monoidal.opposite
import category_theory.monoidal.internal.Module
import algebra.category.Module.monoidal
import algebraic_geometry.GroupObject.coalgebra

open category_theory category_theory.monoidal_category opposite

universes v v₁ v₂ v₃ u u₁ u₂ u₃

variables (C : Type*) [category C] [monoidal_category C]

@[simp] lemma op_tensor_hom {X Y X' Y' : Cᵒᵖ} (f : X ⟶ Y) (g : X' ⟶ Y') :
  f ⊗ g = (f.unop ⊗ g.unop).op := rfl

@[simp] lemma op_associator {X Y Z : Cᵒᵖ} :
  (α_ X Y Z) = (α_ X.unop Y.unop Z.unop).symm.op := rfl

@[simp] lemma op_left_unitor {X : Cᵒᵖ} :
  λ_ X = (λ_ X.unop).symm.op := rfl

@[simp] lemma op_right_unitor {X : Cᵒᵖ} :
  ρ_ X = (ρ_ X.unop).symm.op := rfl

/-  associator_naturality' := by { intros, apply quiver.hom.unop_inj, simp, },
  left_unitor_naturality' := by { intros, apply quiver.hom.unop_inj, simp, },
  right_unitor_naturality' := by { intros, apply quiver.hom.unop_inj, simp, },
  triangle' := by { intros, apply quiver.hom.unop_inj, coherence, },
  pentagon' := by { intros, apply quiver.hom.unop_inj, coherence, }, }-/


variables [symmetric_category C]

@[derive category] def BiMon_ := Mon_ (Mon_ C)ᵒᵖ

structure HopfMon_ extends Mon_ (Mon_ C)ᵒᵖ :=
(s : X.unop.X ⟶ X.unop.X)
(mul_left_inv' : mul.unop.hom ≫ (s ⊗ (𝟙 X.unop.X)) ≫ X.unop.mul = one.unop.hom ≫ X.unop.one)
(mul_right_inv' : mul.unop.hom ≫ ((𝟙 X.unop.X) ⊗ s) ≫ X.unop.mul = one.unop.hom ≫ X.unop.one)

restate_axiom HopfMon_.mul_left_inv'
restate_axiom HopfMon_.mul_right_inv'
attribute [simp, reassoc] HopfMon_.mul_left_inv HopfMon_.mul_right_inv

instance : category (HopfMon_ C) :=
show category (induced_category (Mon_ (Mon_ C)ᵒᵖ) HopfMon_.to_Mon_),
by apply_instance

def HopfMon_to_Mon_ : HopfMon_ C ⥤ Mon_ (Mon_ C)ᵒᵖ :=
induced_functor HopfMon_.to_Mon_

variables {R : Type u} [comm_ring R] (X : Bialgebra.{u} R)

open Module.Mon_Module_equivalence_Algebra
#check Mon_.trivial
#check tensor_product.lift.tmul
#check Mon_.Mon_monoidal
#check Module.monoidal_category
#check Mon_.trivial_mul
#check Module.monoidal_category
-- didn't help
lemma Mon_.tensor_unit : (𝟙_ (Mon_ C)) = Mon_.trivial C := rfl
@[simp] lemma Mon_.tensor_unit_one : (𝟙_ (Mon_ C)).one = 𝟙 _ := rfl
@[simp] lemma Mon_.tensor_unit_mul : (𝟙_ (Mon_ C)).mul = (λ_ (𝟙_ C)).hom := rfl
@[simp] lemma Mon_.tensor_one (X Y : Mon_ C) :
  (X ⊗ Y).one = (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) := rfl
@[simp] lemma Mon_.tensor_mul (X Y : Mon_ C) :
  (X ⊗ Y).mul = tensor_μ C (X.X, Y.X) (X.X, Y.X) ≫ (X.mul ⊗ Y.mul) := rfl
lemma Mon_.tensor_X (X Y : Mon_ C) : (X ⊗ Y).X = X.X ⊗ Y.X := rfl
@[simp] lemma Mon_.tensor_hom {M N P Q : Mon_ C} (f : M ⟶ N) (g : P ⟶ Q) :
  (f ⊗ g).hom = f.hom ⊗ g.hom := rfl
@[simp] lemma Mon_.associator (M N P : Mon_ C) :
  α_ M N P = Mon_.iso_of_iso (α_ M.X N.X P.X) Mon_.one_associator Mon_.mul_associator := rfl
@[simp] lemma Mon_.left_unitor (M : Mon_ C) :
  λ_ M = Mon_.iso_of_iso (λ_ M.X) Mon_.one_left_unitor Mon_.mul_left_unitor := rfl
@[simp] lemma Mon_.right_unitor (M : Mon_ C) :
  ρ_ M = Mon_.iso_of_iso (ρ_ M.X) Mon_.one_right_unitor Mon_.mul_right_unitor := rfl

-- rw otherwise have to @ quiver.hom.op. slow with dsimp.
@[simps] def bialgebra_to_bimonoid_one :
  (inverse_obj (Algebra.of R X)) ⟶ 𝟙_ (Mon_ (Module.{u} R)) :=
{ hom := Module.of_hom (bialgebra.counit R X).to_linear_map,
  one_hom' := by ext; show bialgebra.counit R X (algebra_map R X 1) = 1; simp only [map_one],
  mul_hom' :=
  begin
    ext,
    simpa only [tensor_product.algebra_tensor_module.curry_apply,
      linear_map.coe_restrict_scalars, linear_map.to_fun_eq_coe,
      tensor_product.curry_apply, Module.comp_def, linear_map.comp_apply,
      inverse_obj_mul, Module.of_hom_apply, alg_hom.to_linear_map_apply, map_mul,
      Module.monoidal_category.hom_apply, Mon_.tensor_unit_mul,
      Module.monoidal_category.left_unitor_hom_apply, linear_map.mul'_apply],
  end }

#check free_add_monoid
#check tensor_product
variables {X}

noncomputable def comul_rep (x : X) : list (X × X) :=
@quotient.out' _ (add_con_gen (tensor_product.eqv R X X)).to_setoid (bialgebra.comul R X x)

lemma mk_comul_rep (x : X) :
  (add_con_gen (tensor_product.eqv R X X)).mk' (comul_rep x) = bialgebra.comul R X x :=
quotient.out_eq' _

lemma fucksake (α : Type*) (M N : Module R) (f : M →ₗ[R] N) (l : list M) (i : α → M) :
  f l.sum = (l.map f).sum :=
begin
  exact map_list_sum f l,

end
lemma fucksake2 (l : free_add_monoid X) :
  free_add_monoid.lift free_add_monoid.of l = l :=
begin
  rw ←function.comp.left_id free_add_monoid.of,
  erw free_add_monoid.lift_restrict (add_monoid_hom.id _),
  refl,
end

lemma ugh (x : X) :
  bialgebra.comul R X x =
  free_add_monoid.lift ((add_con_gen (tensor_product.eqv R X X)).mk'
    ∘ free_add_monoid.of) (comul_rep x) :=
begin
  rw free_add_monoid.lift_restrict,
  exact (mk_comul_rep x).symm,
end
#check tensor_product.induction_on

instance (X : Algebra.{u} R) : smul_comm_class R (tensor_product R X X) (tensor_product R X X) :=
begin
  constructor,
  intros r x y,
  refine x.induction_on _ _ _,
  { simp only [zero_smul, smul_zero] },
  { intros x z,
    refine y.induction_on _ _ _,
    { simp only [smul_zero] },
    { intros w y,
      simp only [smul_eq_mul, algebra.mul_smul_comm],},
    { intros a b ha hb,
      simp only [smul_add, smul_eq_mul, algebra.mul_smul_comm, mul_add] at *,
      }},
  { intros,
    simp only [smul_eq_mul, algebra.mul_smul_comm] at *, }
end

lemma fucksakee (X : Algebra.{u} R) :
  tensor_μ (Module.{u} R) (Module.of R X, Module.of R X)
    (Module.of R X, Module.of R X) ≫ (Module.of_hom (linear_map.mul' R X)
    ⊗ Module.of_hom (linear_map.mul' R X))
  = Module.of_hom (linear_map.mul' R (tensor_product R X X)) :=
begin
  ext x y w z,
  dunfold tensor_μ,
  dsimp,
  simp only [linear_map.mul'_apply],
  refl,
end

variables (X)

@[simps] def bialgebra_to_bimonoid_mul :
  (inverse_obj (Algebra.of R X)) ⟶
    (inverse_obj (Algebra.of R X)) ⊗ (inverse_obj (Algebra.of R X)) :=
{ hom := Module.of_hom (bialgebra.comul R X).to_linear_map,
  one_hom' :=
  begin
    ext,
    show bialgebra.comul R X (algebra_map R X 1)
      = (inverse_obj (Algebra.of R X) ⊗ inverse_obj (Algebra.of R X)).one 1,
    simpa only [Mon_.tensor_one, inverse_obj_one, Algebra.coe_comp, function.comp_app,
      Module.monoidal_category.left_unitor_inv_apply, Module.monoidal_category.hom_apply,
      algebra.linear_map_apply, map_one],
  end,
  mul_hom' :=
  begin
    dsimp,
    erw fucksakee (Algebra.of R X),
    -- can't get the rest to typecheck as a separate lemma and can't be arsed
    ext,
    simp only [tensor_product.algebra_tensor_module.curry_apply,
      linear_map.coe_restrict_scalars, linear_map.to_fun_eq_coe,
      tensor_product.curry_apply, Module.comp_def, linear_map.comp_apply,
      Module.of_hom_apply, alg_hom.to_linear_map_apply, map_mul,
      linear_map.mul'_apply, Module.monoidal_category.hom_apply],
  end }

def bialgebra_to_bimonoid (X : Bialgebra R) : Mon_ (Mon_ (Module.{u} R))ᵒᵖ :=
{ X := opposite.op (inverse_obj $ Algebra.of R X),
  one := (bialgebra_to_bimonoid_one X).op,
  mul := (bialgebra_to_bimonoid_mul X).op,
  one_mul' :=
  begin
    rw [op_tensor_hom, ←op_comp, op_left_unitor, iso.op_hom],
    congr,
    simp only [iso.symm_hom, ←iso.comp_hom_eq_id, quiver.hom.unop_op, unop_id_op],
    ext,
    exact alg_hom.ext_iff.1 (bialgebra.counit_left.{u u} R X) _,
  end,
  mul_one' :=
  begin
    rw [op_tensor_hom, ←op_comp, op_right_unitor, iso.op_hom],
    congr,
    simp only [iso.symm_hom, ←iso.comp_hom_eq_id, quiver.hom.unop_op, unop_id_op],
    ext,
    exact alg_hom.ext_iff.1 (bialgebra.counit_right.{u u} R X) _,
  end,
  mul_assoc' :=
  begin
    simp only [op_tensor_hom, ←op_comp, op_associator, iso.op_hom],
    congr' 1,
    simp only [iso.symm_hom, iso.eq_comp_inv, quiver.hom.unop_op, unop_id_op],
    ext,
    exact alg_hom.ext_iff.1 (bialgebra.comul_coassoc.{u u} R X) x,
  end, }

abbreviation FFS := (@Module.Mon_Module_equivalence_Algebra.functor R _).obj
abbreviation FFS' {X Y : Mon_ (Module.{u} R)} (f : X ⟶ Y) :=
  (@Module.Mon_Module_equivalence_Algebra.functor R _).map f

def UGH (A : Mon_ (Module.{u} R)) : FFS A ≃ₗ[R] A.X :=
{ map_smul' := λ r x, rfl, .. add_equiv.refl _ }

def UGH2 (A : Mon_ (Module.{u} R)) :
  FFS (A ⊗ A) ≃ₗ[R] tensor_product R (FFS A) (FFS A) :=
tensor_product.congr (UGH A).symm (UGH A).symm

lemma Module_tensor_hom {M N P Q : Module.{u} R} (f : M ⟶ N)
  (g : P ⟶ Q) : f ⊗ g = Module.of_hom (tensor_product.map f g) := rfl
#check algebra.of_module
lemma associator_hom {M N P : Module.{u} R} :
  α_ M N P = (tensor_product.assoc R M N P).to_Module_iso := rfl
/-def UGH3 (A : Mon_ (Module.{u} R)) (f : A ⟶ A ⊗ A) :
  FFS A →ₗ[R] tensor_product R (FFS A) (FFS A) :=
(UGH2 A).to_linear_map ∘ₗ alg_hom.to_linear_map (FFS'.{u} f)-/
def bimonoid_to_bialgebra (X : Mon_ (Mon_ (Module.{u} R))ᵒᵖ) : Bialgebra R :=
{ carrier := X.X.unop.X,
  is_ring := by apply_instance,
  is_algebra :=
  begin
    refine @algebra.of_module R X.X.unop.X _ _ _ sorry sorry,

  end,
  is_bialgebra :=
  { comul' :=  by {convert X.mul.unop.hom, },--(UGH2 X.X.unop).to_linear_map.comp (FFS' (X.mul.unop)).to_linear_map,
    counit' := _,--(FFS' X.one.unop).to_linear_map,
    comul_coassoc' := _,
    /-begin
      dsimp,
      have := congr_arg quiver.hom.unop X.mul_assoc,
      dsimp at this,
      rw iso.eq_comp_inv at this,
      ext,
      rw Mon_.hom.ext_iff at this,
      rw Mon_.iso_of_iso at this,
      dsimp at this,
      rw associator_hom at this,
      rw Module_tensor_hom at this,
      dunfold FFS' UGH2 UGH FFS,
      dsimp,

      dunfold associator at this,
      any_goals {ext, refl},
      rw heq_iff_eq,
    end,-/
    counit_right' := _,
    counit_left' := _,
    comul_map_one' := _,
    comul_map_mul' := _,
    counit_map_one' := _,
    counit_map_mul' := _ } }
