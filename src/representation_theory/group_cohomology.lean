import representation_theory.group_cohomology_resolution
import algebra.homology.op
import category_theory.closed.functor_category
import algebra.category.Module.monoidal
universes v u

section
open category_theory
variables {k G : Type u} [comm_ring k] [group G] {V : Type u} [add_comm_group V] [module k V]
(n : ℕ) (ρ : representation k G V)
variables {C D : Type*} [groupoid D] [category C] [monoidal_category C] [monoidal_closed C]
noncomputable theory
instance : group (Mon.of G) := by assumption

noncomputable def finsupp.llift (S M R : Type*) [comm_semiring S] [semiring R] [algebra S R] [add_comm_monoid M]
  [module S M] [module R M] [is_scalar_tower S R M] (X : Type*) :
  (X → M) ≃ₗ[S] ((X →₀ R) →ₗ[R] M) :=
{ map_smul' :=
  begin
    intros,
    dsimp,
    ext,
    simp only [linear_map.coe_comp, function.comp_app, finsupp.lsingle_apply, finsupp.lift_apply, pi.smul_apply,
  finsupp.sum_single_index, zero_smul, one_smul, linear_map.smul_apply],
  end, ..finsupp.lift M R X }
end

lemma finsupp.llift_apply {S M R : Type*}[comm_semiring S] [semiring R] [algebra S R] [add_comm_monoid M]
  [module S M] [module R M] [is_scalar_tower S R M] {X : Type*}
  (f : X → M) : finsupp.llift S M R X f = finsupp.lift M R X f := rfl

open Rep category_theory group_cohomology.resolution

@[simps] def linear_arrow_congr (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f1 : X ≅ Y) (f2 : W ≅ Z) :
  (X ⟶ W) ≃ₗ[k] (Y ⟶ Z) :=
{ inv_fun := (linear.left_comp k W f1.hom).comp (linear.right_comp k Y f2.symm.hom),
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  ..(linear.right_comp k Y f2.hom).comp (linear.left_comp k W f1.symm.hom) }

section
variables {k G : Type u} [comm_ring k] [group G] {V : Type u} [add_comm_group V] [module k V]
(n : ℕ) (ρ : representation k G V)
variables {A B C : Rep k G}

lemma representation.inv_apply_apply (g : G) (x : V) :
  ρ g⁻¹ (ρ g x) = x :=
begin
  show (ρ g⁻¹ * ρ g) x = x,
  rw [←ρ.map_mul, inv_mul_self, ρ.map_one],
  refl,
end

lemma representation.apply_inv_apply (g : G) (x : V) :
  ρ g (ρ g⁻¹ x) = x :=
begin
  show (ρ g * ρ g⁻¹) x = x,
  rw [←ρ.map_mul, mul_inv_self, ρ.map_one],
  refl,
end

set_option profiler true

lemma tensor_hom_aux (f : A ⊗ B ⟶ C) (g : G) :
  (tensor_product.curry f.hom).comp (A.ρ g) =
  (B.ρ.lin_hom C.ρ g).comp (tensor_product.curry f.hom) :=
begin
  ext x y,
  have := linear_map.ext_iff.1 (f.comm g) (tensor_product.tmul k x (B.ρ g⁻¹ y)),
  simp only [linear_map.comp_apply, tensor_product.curry_apply, Action.tensor_rho,
    Action.comp_hom, Module.coe_comp, function.comp_apply,
    B.ρ.lin_hom_apply, Module.monoidal_category.hom_apply]
    at ⊢ this,
  erw representation.apply_inv_apply at this,
  exact this,
end

lemma Module.ihom_map_apply (A B C : Module.{u} k) (f : B ⟶ C) (g : Module.of k (A ⟶ B)) :
  (ihom A).map f g = g ≫ f := rfl

lemma Module.ihom_adjunction_eq (A : Module.{u} k) :
  ihom.adjunction A = adjunction.mk_of_hom_equiv
      { hom_equiv := λ N P, Module.monoidal_closed_hom_equiv A N P, } := rfl

lemma Module.as_hom_apply {M N : Type*} [add_comm_group M] [add_comm_group N]
  [module k M] [module k N] (f : M →ₗ[k] N) (x : M) :
  Module.as_hom f x = f x := rfl

lemma Module.ihom_ev_app (A B : Module.{u} k) :
  (ihom.ev A).app B = Module.as_hom (tensor_product.uncurry _ _ _ _ linear_map.id.flip) :=
begin
  ext x y,
  dsimp,
  rw [Module.as_hom_apply, tensor_product.uncurry_apply,
    linear_map.flip_apply, linear_map.id_apply,
    ←ihom.ihom_adjunction_counit, Module.ihom_adjunction_eq],
  exact tensor_product.lift.tmul _ _,
end

lemma Module.ihom_coev_app (A B : Module.{u} k) :
  (ihom.coev A).app B = Module.as_hom (tensor_product.curry (β_ B A).hom) :=
begin
  ext x y,
  dsimp,
  rw [Module.as_hom_apply, tensor_product.curry_apply, Module.monoidal_category.braiding_hom_apply,
    ←ihom.ihom_adjunction_unit, Module.ihom_adjunction_eq],
  refl,
end

noncomputable instance : monoidal_closed (Rep k G) :=
monoidal_closed.of_equiv (Action.functor_category_monoidal_equivalence _ _)

variables (k G)
abbreviation e := Action.functor_category_equivalence (Module.{u} k) (Mon.of G)
abbreviation e_m := Action.functor_category_monoidal_equivalence (Module.{u} k) (Mon.of G)
variables {k G} (A)

def ihom_iso :
  ihom A ≅ (e k G).functor ⋙ functor.closed_ihom
    ((e k G).functor.obj A) ⋙ (e k G).inverse :=
iso.refl _

def ihom_iso' :
  ihom A ⋙ (e k G).functor ≅ (e k G).functor ⋙ functor.closed_ihom ((e k G).functor.obj A) := iso.refl _

variables {A}

lemma ihom_coev_app :
  (ihom.coev A).app B = ((e k G).unit_iso.app B).hom ≫
  (e k G).inverse.map (((e k G).functor.obj A).closed_unit.app _ ≫
    ((e k G).functor.obj A).closed_ihom.map
    ((e_m k G).μ A B)) := rfl

lemma ihom_coev_app_eq :
  Action.hom.hom ((ihom.coev A).app B) =
    tensor_product.curry (tensor_product.comm k B A).to_linear_map :=
begin
  rw ihom_coev_app,
  simp only [Action.functor_category_equivalence_unit_iso, iso.app_hom, functor.map_comp, Action.comp_hom,
  Action.functor_category_equivalence.unit_iso_hom_app_hom],
  erw category.id_comp,
  dunfold functor.closed_unit,
  dunfold functor.closed_ihom,
  dsimp,
  simp only [whiskering_right₂_obj_obj_map_app],
  ext x y,
  dsimp,
  rw Module.ihom_coev_app,
  rw Module.ihom_map_apply,
  dsimp,
  rw Module.as_hom_apply,
  simp only [tensor_product.curry_apply, Module.monoidal_category.braiding_hom_apply],
  dunfold e_m Action.functor_category_monoidal_equivalence monoidal.from_transported,
  dsimp,
  sorry,
end

lemma curry (f : A ⊗ B ⟶ C) :
  monoidal_closed.curry f = ((e k G).unit_iso.app _).hom ≫
  (e k G).inverse.map (monoidal_closed.curry ((e_m k G).μ A B ≫ (e k G).functor.map f)) :=
rfl

lemma ihom_counit_app :
  (ihom.ev A).app B = ((e k G).unit_iso.app _).hom ≫
  ((e k G).inverse.map ((e_m k G).μ _ _)) ≫ (e k G).inverse.map
    (((e k G).functor.obj A).closed_counit.app ((e k G).functor.obj B)) ≫
    ((e k G).unit_iso.app _).inv
   :=
begin
  simp only [←category.assoc],
  rw iso.eq_comp_inv,
  simp only [Action.functor_category_equivalence_unit_iso, iso.app_hom, category.assoc],
  sorry,
end

variables (A B C)


variables (M N O : Module.{u} k) (f : N ⟶ M) (g : Module.of k (M ⟶ O))
#check Module.monoidal_closed_uncurry

lemma Module.pre_app (A B C : Module.{u} k) (f : B ⟶ A) :
  (monoidal_closed.pre f).app C = linear_map.lcomp k _ f :=
begin
  refine monoidal_closed.uncurry_injective _,
  simp only [monoidal_closed.uncurry_pre, Module.ihom_ev_app],
  ext g x y,
  dsimp,
  rw Module.monoidal_closed_uncurry,
  exact tensor_product.uncurry_apply _ _ _,
end

lemma Rep.ihom_obj_ρ (A B : Rep k G) :
  ((ihom A).obj B).ρ = ((Action.functor_category_equivalence _ _).inverse.obj
  (((Action.functor_category_equivalence _ _).functor.obj A).closed_ihom.obj
  ((Action.functor_category_equivalence _ _).functor.obj B))).ρ := rfl

lemma Rep.ihom_obj_ρ_eq (A B : Rep k G) :
  ((ihom A).obj B).ρ = A.ρ.lin_hom B.ρ :=
begin
  ext g x y,
  rw Rep.ihom_obj_ρ,
  dsimp [functor.closed_ihom],
  simp only [whiskering_right₂_obj_obj_obj_map, functor.comp_map,
    groupoid.inv_functor_map, op_inv, functor.op_map, quiver.hom.unop_op, unop_inv,
    Action.functor_category_equivalence.functor_obj_map, monoidal_closed.internal_hom_map,
    Module.ihom_map_apply, Module.pre_app, single_obj.inv_as_inv],
  refl,
end

lemma Rep.ihom_map_def (A : Rep k G) {B C : Rep k G} (f : B ⟶ C) :
  ((ihom A).map f) = ((Action.functor_category_equivalence _ _).inverse.map
  (((Action.functor_category_equivalence _ _).functor.obj A).closed_ihom.map
  ((Action.functor_category_equivalence _ _).functor.map f))) := rfl

lemma Rep.ihom_map_eq (A B C : Rep k G) (f : B ⟶ C) :
  ((ihom A).map f).hom = linear_map.llcomp k A B C f.hom :=
begin
  rw Rep.ihom_map_def,
  dsimp [functor.closed_ihom],
  simp only [whiskering_right₂_obj_obj_map_app, Action.functor_category_equivalence.functor_map_app],
  ext x y,
  dsimp,
  rw Module.ihom_map_apply,
  refl,
end

lemma Rep.Action_ρ_eq_ρ (A : Rep k G) :
  Action.ρ A = Rep.ρ A := rfl

lemma Rep.comm_apply (A B : Rep k G) (f : A ⟶ B) (g : G) (x : A) :
  f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
linear_map.ext_iff.1 (f.comm g) _

lemma ihom2_comm (f : B ⟶ C) (g : G) :
  (linear_map.llcomp k A B C f.hom).comp (A.ρ.lin_hom B.ρ g)
  = (A.ρ.lin_hom C.ρ g).comp (linear_map.llcomp k A B C f.hom) :=
begin
  ext x y,
  simp only [representation.lin_hom_apply,
    linear_map.llcomp_apply, linear_map.comp_apply, Rep.comm_apply],
end

def ihom2_map (f : B ⟶ C) :
  Rep.of (A.ρ.lin_hom B.ρ) ⟶ Rep.of (A.ρ.lin_hom C.ρ) :=
{ hom := linear_map.llcomp k A B C f.hom,
  comm' := λ g,
  begin
    sorry,
  end
  }

lemma ihom2_id :
  ihom2_map A B B (𝟙 B) = 𝟙 (Rep.of (A.ρ.lin_hom B.ρ)) :=
begin
  ext,
  dsimp,
  refl,
end

lemma ihom2_comp (B C D : Rep k G)
  (f : B ⟶ C) (g : C ⟶ D) :
  ihom2_map _ _ _ (f ≫ g) =
  ihom2_map _ _ _ f ≫ ihom2_map A _ _ g :=
by ext; refl

def ihom2 : Rep k G ⥤ Rep k G :=
{ obj := λ B, Rep.of (A.ρ.lin_hom B.ρ),
  map := λ B C f, ihom2_map _ _ _ f,
  map_id' := λ X, ihom2_id _ _,
  map_comp' := λ B C D f g, ihom2_comp _ _ _ _ _ _ }

def ihom_iso_ihom2 :
  ihom A ≅ ihom2 A :=
nat_iso.of_components (λ X, Action.mk_iso (iso.refl _)
  (λ g, by {rw Rep.Action_ρ_eq_ρ, rw Rep.ihom_obj_ρ_eq A X, refl}))
  (λ X Y f, by { ext, rw Action.comp_hom, rw Rep.ihom_map_eq, refl, })

def ihom2_adjunction :
  monoidal_category.tensor_left A ⊣ (ihom2 A) :=
(ihom.adjunction A).of_nat_iso_right (ihom_iso_ihom2 A)

def ihom2_hom_equiv :
  ((ihom2_adjunction A).hom_equiv B C).trans (adjunction.equiv_homset_right_of_nat_iso (ihom_iso_ihom2 A).symm) =
  (ihom.adjunction A).hom_equiv B C :=
rfl

lemma ihom2_hom_equiv_eq  (f : B ⟶ Rep.of (A.ρ.lin_hom C.ρ)) :
  (((ihom2_adjunction A).hom_equiv B C).symm f).hom = tensor_product.uncurry k A B C f.hom.flip :=
begin
  dunfold ihom2_adjunction ihom_iso_ihom2,
  dsimp,
  ext,
  sorry,
end

lemma Rep.monoidal_closed_uncurry {A B C : Rep k G}
  (f : B ⟶ (A ⟶[Rep k G] C)) :
  (monoidal_closed.uncurry f).hom = tensor_product.uncurry k A B C f.hom.flip :=
begin
  rw monoidal_closed.uncurry,
  rw ←ihom2_hom_equiv,
  dsimp,
  simp only [adjunction.hom_equiv_naturality_left_symm, monoidal_category.tensor_left_map, adjunction.hom_equiv_counit,
  Action.comp_hom, Action.tensor_hom, Action.id_hom],
  dsimp [ihom2_adjunction, ihom_iso_ihom2],
  simp only [category.comp_id],
  ext,
  dsimp,
  dunfold adjunction.of_nat_iso_right,
  dsimp,
  rw monoidal_closed.uncurry_natural_left,
  sorry,
end

/-lemma Rep.ihom_ev_app (A B : Rep k G) (x : A) (y : (ihom A).obj B) :
  ((ihom.ev A).app B : A ⊗ (ihom A).obj B ⟶ B).hom (tensor_product.tmul k x y) =
  Action.hom.hom ((Action.functor_category_equivalence _ _).inverse.map
  ((ihom.ev ((Action.functor_category_equivalence _ _).functor.obj A)).app
    ((Action.functor_category_equivalence _ _).functor.obj B)))
    (tensor_product.tmul k x y) := sorry-/

noncomputable def linear_monoidal_closed_hom_equiv :
  (A ⊗ B ⟶ C) ≃ₗ[k] (B ⟶ (A ⟶[Rep k G] C)) :=
{ map_add' := λ f g, rfl,
  map_smul' := λ r f, rfl, ..(ihom.adjunction A).hom_equiv _ _ }

noncomputable def linear_monoidal_closed_hom_equiv' :
  (A ⊗ B ⟶ C) ≃ₗ[k] (A ⟶ (B ⟶[Rep k G] C)) :=
(linear_arrow_congr _ (β_ _ _) (iso.refl _)).trans
  (linear_monoidal_closed_hom_equiv B A C)

noncomputable def as_linear_map : (B ⟶[Rep k G] C) ≃ₗ[k] (B →ₗ[k] C) :=
linear_equiv.refl _ _

variables {A B C}

#exit
  @coe_fn (B.V →ₗ[k] C.V) _ _ ((linear_monoidal_closed_hom_equiv' A B C f).hom x : B.V →ₗ[k] C.V) y
  = f.hom (tensor_product.tmul k x y) :=
tensor_product.curry_apply _ _ _

def Rep.of_tprod_iso {V W : Type u} [add_comm_group V] [add_comm_group W] [module k V]
 [module k W] (ρ : representation k G V) (τ : representation k G W) :
Rep.of ρ ⊗ Rep.of τ ≅ Rep.of (ρ.tprod τ) :=
Action.mk_iso (iso.refl _) $
begin
  intro g,
  ext x y,
  dsimp,
  refl,
end

noncomputable def of_mul_action_hom_equiv_inv (x : A) :
  Rep.of_mul_action k G G ⟶ A :=
{ hom := finsupp.lift _ _ _ (λ g, A.ρ g x),
    comm' := λ g,
    begin
      ext,
      dsimp,
      dunfold Rep.of_mul_action,
      show finsupp.sum (finsupp.map_domain _ _) _ = _,
      rw finsupp.map_domain_single, rw finsupp.sum_single_index,
      rw one_smul,
      rw finsupp.sum_single_index,
      rw one_smul,
      rw smul_eq_mul,
      rw A.ρ.map_mul,
      refl,
      rw zero_smul,
      rw zero_smul,
end }

lemma of_mul_action_hom_equiv_right_inv (x : A) :
  (of_mul_action_hom_equiv_inv x).hom (finsupp.single 1 1) = x :=
begin
  unfold of_mul_action_hom_equiv_inv,
  dsimp,
  rw finsupp.sum_single_index,
  rw one_smul,
  rw A.ρ.map_one,
  refl,
  rw zero_smul,
end

@[simps] noncomputable def of_mul_action_hom_equiv (A : Rep k G) :
  (Rep.of_mul_action k G G ⟶ A) ≃ₗ[k] A :=
{ to_fun := λ f, f.hom (finsupp.single 1 1),
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ x,
  { hom := finsupp.lift _ _ _ (λ g, A.ρ g x),
    comm' := λ g,
    begin
      ext,
      dsimp,
      dunfold Rep.of_mul_action,
      show finsupp.sum (finsupp.map_domain _ _) _ = _,
      rw finsupp.map_domain_single, rw finsupp.sum_single_index,
      rw one_smul,
      rw finsupp.sum_single_index,
      rw one_smul,
      rw smul_eq_mul,
      rw A.ρ.map_mul,
      refl,
      rw zero_smul,
      rw zero_smul,
    end },
  left_inv := λ f,
  begin
    ext,
    dsimp,
    rw finsupp.sum_single_index,
    rw one_smul,
    have := linear_map.ext_iff.1 (f.comm a) (finsupp.single 1 1),
      simp only [Module.coe_comp, function.comp_apply, linear_map.to_fun_eq_coe,
      linear_map.comp_apply, Rep.of_ρ] at this,
    dunfold Rep.of_mul_action at this,
    erw ←this,
    dsimp,
    show f.hom (finsupp.map_domain _ _) = _,
    rw finsupp.map_domain_single,
    rw smul_eq_mul,
    rw mul_one,
    rw zero_smul
  end,
  right_inv := λ x, of_mul_action_hom_equiv_right_inv x }
#check linear_equiv.trans

lemma of_mul_action_equiv_symm_single (x : A) (g : G) :
  ((of_mul_action_hom_equiv A).symm x).hom (finsupp.single g 1) = A.ρ g x :=
begin
  dsimp,
  rw finsupp.sum_single_index,
  rw one_smul,
  rw zero_smul,
end

variables (k G A)

noncomputable def finally :=
((linear_arrow_congr k ((equiv_tensor k G n).trans (Rep.of_tprod_iso _ _).symm) (iso.refl _)) ≪≫ₗ
((linear_monoidal_closed_hom_equiv' _ _ _) ≪≫ₗ (of_mul_action_hom_equiv _)))
≪≫ₗ (finsupp.llift k A k (fin n → G)).symm

lemma huh (f : Rep.of_mul_action k G (fin (n + 1) → G) ⟶ A) (x : fin n → G) :
  finally k G n A f x = f.hom (finsupp.single (fin.partial_prod x) 1) :=
begin
  unfold finally,
  simp only [linear_equiv.trans_apply],
  erw finsupp.lift_symm_apply,
  rw of_mul_action_hom_equiv_apply,
  erw tensor_hom_apply,
  rw linear_arrow_congr_apply,
  dsimp [Rep.of_tprod_iso],
  rw of_tensor_single',
  simp only [finsupp.lift_apply, finsupp.smul_single', mul_one, finsupp.sum_single_index, finsupp.single_eq_zero, one_smul],
end

lemma huh2 (f : (fin n → G) → A) (x : fin (n + 1) → G) :
  ((finally k G n A).symm f).hom (finsupp.single x 1) = A.ρ (x 0) (f (λ (i : fin n), (x ↑i)⁻¹ * x i.succ)) :=
begin
  unfold finally,
  simp only [linear_equiv.trans_symm,
    linear_equiv.symm_symm, linear_equiv.trans_apply],
  rw linear_arrow_congr_symm_apply,
  rw iso.refl_symm,
  rw iso.refl_hom,
  rw linear_map.comp_apply,
  rw linear.right_comp_apply,
  rw category.comp_id,
  rw linear.left_comp_apply,
  rw Action.comp_hom,
  rw iso.trans_hom,
  rw Rep.of_tprod_iso,
  rw Action.comp_hom,
  rw iso.symm_hom,
  rw Action.mk_iso_inv_hom,
  rw iso.refl_inv,
  erw category.comp_id,
  rw Module.coe_comp,
  rw function.comp_apply,
  unfold equiv_tensor,
  rw Action.mk_iso_hom_hom,
  rw linear_equiv.to_Module_iso_hom,
  erw to_tensor_aux_single,
  rw tensor_hom_symm_apply,
  rw of_mul_action_equiv_symm_single,
  rw Rep.of_ρ,
  rw Rep.of_ρ,
  rw finsupp.llift_apply,
  rw representation.lin_hom_apply,
  simp only [linear_map.comp_apply],
  rw monoid_hom.one_apply,
  rw finsupp.lift_apply,
  erw finsupp.sum_single_index,
  rw one_smul,
  rw zero_smul,
end

variables (k G A)

noncomputable abbreviation hom_resolution := homological_complex.unop
  ((((linear_yoneda k (Rep k G)).obj A).right_op.map_homological_complex _).obj
  (group_cohomology.resolution k G))

noncomputable def inhomog : cochain_complex (Module k) ℕ :=
{ X := λ n, Module.of k ((fin n → G) → A),
  d := λ i j, (finally k G i A).symm.to_Module_iso.hom ≫
    (hom_resolution k G A).d i j
    ≫ (finally k G j A).to_Module_iso.hom,
  shape' := λ i j hij,
  begin
    --dsimp,
    ext,
    dsimp,
    rw (group_cohomology.resolution k G).shape _ _ hij,
    rw limits.zero_comp,
    rw map_zero,
    refl,
  end,
  d_comp_d' := λ i j l hij hjl,
  begin
    ext x y,
    dsimp,
    rw linear_equiv.symm_apply_apply,
    rw (group_cohomology.resolution k G).d_comp_d_assoc,
    rw limits.zero_comp,
    rw map_zero,
    refl
  end}

variables {k G n A}

def F (j : ℕ) (g : fin (n + 1) → G) (k : fin n) : G :=
if (k : ℕ) < j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) else
if (k : ℕ) = j then g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k)
else g (fin.add_nat 1 k)

lemma F_lt_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n) (h : (k : ℕ) < j) :
  F j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) := if_pos h

lemma F_eq_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n) (h : (k : ℕ) = j) :
  F j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) * g (fin.add_nat 1 k) :=
begin
  have : ¬(k : ℕ) < j, by linarith,
  unfold F,
  rw [if_neg this, if_pos h],
end

lemma F_neg_apply (j : ℕ) (g : fin (n + 1) → G) (k : fin n)
  (h : ¬(k : ℕ) < j) (h' : ¬(k : ℕ) = j) :
  F j g k = g (fin.add_nat 1 k) :=
begin
  unfold F,
  rw [if_neg h, if_neg h'],
end

def d_to_fun (f : (fin n → G) → A) : (fin (n + 1) → G) → A :=
λ g, A.ρ (g 0) (f (λ i, g (fin.add_nat 1 i)))
  + (finset.range (n + 1)).sum (λ j, (-1 : k) ^ (j + 1) • f (F j g))
#check fin.cast_succ
#check fin.
#check lt_trans (fin.is_lt _) n.lt_succ_self

lemma fucksake_fin (i : fin n) :
  i.cast_succ = (↑(↑i : ℕ)) :=
begin
  ext,
  rw fin.coe_coe_of_lt (lt_trans (fin.is_lt _) n.lt_succ_self),
  refl,
end

#check @finset.sum_bij ℕ (fin (n + 1)) ℕ _ finset.univ (finset.range (n + 1))
 _ _ (λ i hi, i) (λ a ha, finset.mem_range.2 a.2) _ (λ a b ha hb hab, by ext; exact hab)
  (λ a ha, ⟨⟨a, finset.mem_range.1 ha⟩, finset.mem_univ _, rfl⟩)
#check fin.succ_above
lemma urhm (f : (fin n → G) → A) (g : fin (n + 1) → G) (a : fin (n + 1)) :
  (-1 : k) ^ (a.succ : ℕ) • ((finally k G n A).symm f).hom
  (finsupp.single (fin.partial_prod g ∘ a.succ.succ_above) 1)
  = (-1 : k) ^ ((a : ℕ) + 1) • f (F (a : ℕ) g) :=
begin
  rw huh2,
  simp only [fin.coe_succ, function.comp_app, fin.succ_succ_above_zero, fin.partial_prod_zero, map_one, fin.coe_eq_cast_succ,
  fin.succ_succ_above_succ, linear_map.one_apply],
  simp only [fin.partial_prod_succ],
  congr,
  ext,
  by_cases (x : ℕ) < a,
  { rw fin.succ_above_below,
    rw fin.succ_above_below,
    rw inv_mul_cancel_left,
    rw F_lt_apply _ _ _ h,
    refl,
    assumption,
    rw fin.lt_def,
    simp only [fin.val_eq_coe, fin.coe_cast_succ, fin.coe_succ],
    exact lt_trans h (nat.lt_succ_self _) },
  { by_cases hx : (x : ℕ) = a,
    { rw F_eq_apply _ _ _ hx,

      rw fin.succ_above_below,
      rw fin.succ_above_above,
      rw fin.cast_succ_fin_succ,
      rw fin.partial_prod_succ,
      rw mul_assoc,
      rw inv_mul_cancel_left,
      rw fin.add_nat_one,
      refl,
      rw fin.le_iff_coe_le_coe,
      rw ←hx,
      refl,
      rw fin.lt_iff_coe_lt_coe,
      dsimp,
      rw hx,
      rw fin.coe_succ,
      exact nat.lt_succ_self _,
      },
    { rw F_neg_apply _ _ _ h hx,
      rw fin.succ_above_above,
      rw fin.succ_above_above,
      rw fin.partial_prod_succ,
      rw fin.cast_succ_fin_succ,
      rw fin.partial_prod_succ,
      rw inv_mul_cancel_left,
      rw fin.add_nat_one,
      exact not_lt.1 h,
      rw fin.le_iff_coe_le_coe,
      rw fin.coe_succ,
      exact nat.succ_le_of_lt (lt_of_le_of_ne (not_lt.1 h) (ne.symm hx))
      }
  }
end
 /-
lemma free_me (f : (fin n → G) → A) (g : fin (n + 1) → G)
  (a : fin (n + 1)) : (-1 : k) ^ (a.succ : ℕ) • ((finally k G n A).symm f).hom
  (finsupp.single (fin.partial_prod g ∘ a.succ.succ_above) 1) = (-1 : k) ^
  ((a : ℕ) + 1) • f (F ((λ (i : fin (n + 1)) (hi : i ∈ finset.univ), ↑i) a ha) g)
-/
lemma d_eq (f : (fin n → G) → A) (g : fin (n + 1) → G) :
  (inhomog k G A).d n (n + 1) f g = d_to_fun f g :=
begin
  dsimp [inhomog],
  rw huh,
  rw Action.comp_hom,
  rw Module.coe_comp,
  rw function.comp_apply,
  rw group_cohomology.resolution.d_eq,
  rw group_cohomology.resolution.d_of,
  rw linear_map.map_sum,
  simp_rw ←finsupp.smul_single_one _ ((-1 : k) ^ _),
  simp_rw map_smul,
  unfold d_to_fun,
  erw fin.sum_univ_succ,
  rw fin.coe_zero,
  rw pow_zero,
  rw one_smul,
  rw huh2,
  congr' 1,
  { simp only [function.comp_apply, fin.zero_succ_above],
    rw fin.partial_prod_succ,
    dsimp,
    rw fin.partial_prod_zero,
    rw one_mul,
    simp only [fin.partial_prod_succ, mul_inv_rev],
    simp only [fin.cast_succ_fin_succ, fin.partial_prod_succ],
    congr,
    ext,
    simp only [←fucksake_fin, mul_assoc, inv_mul_cancel_left],
    rw fin.add_nat_one,
    },
  { refine @finset.sum_bij _ (fin (n + 1)) ℕ _ finset.univ (finset.range (n + 1))
 _ _ (λ i hi, i) (λ a ha, finset.mem_range.2 a.2) _ (λ a b ha hb hab, by ext; exact hab)
  (λ a ha, ⟨⟨a, finset.mem_range.1 ha⟩, finset.mem_univ _, rfl⟩),
    intros a ha,
    exact urhm _ _ _,
      }
end

--  F j g k = g (fin.cast_lt k (lt_trans k.2 $ lt_add_one _)) := if_pos h

#exit
homological_complex.unop ((((linear_yoneda k (Rep k G)).obj A).right_op.map_homological_complex _).obj
  (group_cohomology.resolution k G))

noncomputable def inhomog_X_iso (n : ℕ) :
  (inhomog k G A).X n ≅ Module.of k (((fin n → G) →₀ k) →ₗ[k] A) :=
((linear_arrow_congr k ((equiv_tensor k G n).trans (Rep.of_tprod_iso _ _).symm) (iso.refl _)) ≪≫ₗ
((tensor_hom.{u} _ _ _) ≪≫ₗ (of_mul_action_hom_equiv _))).to_Module_iso


#exit
lemma fucksake2 (A B : Rep k G) (f : A →ₗ[k] B) (g : G) :
  (fucksake A B f).comp ((Rep.of ((representation.of_mul_action k G G).tprod A.ρ)).ρ g) =
  (B.ρ g).comp (fucksake A B f) :=
begin
  ext,
  dsimp,
  rw representation.of_mul_action_def,
  rw finsupp.lmap_domain_apply,
  rw finsupp.map_domain_single,
  dunfold fucksake,
  rw tensor_product.lift.tmul,



end
--lemma fucksake2 (A B : Rep k G) (f : A →ₗ[k] B) (g : G) :
def base_change_hom_equiv' (A B : Rep k G) :
  (Rep.of_mul_action k G G ⊗ A ⟶ B) ≃ₗ[k] (A →ₗ[k] B) :=
{ to_fun := λ f, f.hom.comp (tensor_product.mk k _ _ (finsupp.single 1 1)),
  map_add' := λ x y, rfl,
  map_smul' := λ r f, rfl,
  inv_fun := λ f,
  { hom := tensor_product.lift (finsupp.lift _ _ _ (λ g, (B.ρ g).comp f)),
    comm' := λ g,
    begin
      ext h x,
      dsimp,
      rw tensor_product.lift.tmul,
      -- (finsupp.map_domain _ (finsupp.single h 1)) (A.ρ g x),
--      show finsupp.lift _ _ _ _ _ _ = _,
    end },
  left_inv := _,
  right_inv := _ }

open_locale tensor_product

variables {R : Type*} {A : Type*} {M : Type*} {N : Type*} {P : Type*} [comm_semiring R]
  [semiring A] [algebra R A] [add_comm_monoid M] [module R M] [module A M]
  [is_scalar_tower R A M] [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]
  [module A P] [is_scalar_tower R A P]

@[simps] def tensor_product.uncurry_nc (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (tensor_product.lift (f.restrict_scalars R)).comp
  (algebra.lsmul R _ c) x = (algebra.lsmul R _ c).comp (tensor_product.lift (f.restrict_scalars R)) x,
    from linear_map.ext_iff.1 $ tensor_product.ext' $ λ x y,
    by simp only [linear_map.comp_apply, algebra.lsmul_coe, tensor_product.smul_tmul',
      tensor_product.lift.tmul, linear_map.coe_restrict_scalars_eq_coe,
      f.map_smul, linear_map.smul_apply],
  .. tensor_product.lift (f.restrict_scalars R) }

@[simps] def tensor_product.curry_nc (f : (M ⊗[R] N) →ₗ[A] P) : M →ₗ[A] (N →ₗ[R] P) :=
{ map_smul' := λ c x,
  begin
    ext,
    simp only [linear_map.to_fun_eq_coe, tensor_product.curry_apply,
      linear_map.coe_restrict_scalars_eq_coe, ring_hom.id_apply, linear_map.smul_apply,
      ←f.map_smul],
    refl,
  end, ..tensor_product.curry (f.restrict_scalars R) }

@[simps] def tensor_product.lift_nc_equiv : (M →ₗ[A] (N →ₗ[R] P)) ≃ₗ[R] (M ⊗[R] N) →ₗ[A] P :=
{ to_fun := tensor_product.uncurry_nc,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := tensor_product.curry_nc,
  left_inv := sorry,
  right_inv := sorry }

variables (R A N P)

def base_change_hom_equiv :
  (A ⊗[R] N →ₗ[A] P) ≃ₗ[R] (N →ₗ[R] P) :=
{ to_fun := λ f, (f.restrict_scalars R).comp (tensor_product.mk R A N 1),
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := λ f, tensor_product.uncurry_nc
    ((linear_map.ring_lmap_equiv_self A R (N →ₗ[R] P)).symm f),
  left_inv := λ f,
  begin
    ext x,
    dsimp,
    rw tensor_product.lift.tmul,
    dsimp,
    simp only [one_smul],
  end,
  right_inv := λ f,
  begin
    ext x,
    dsimp,
    rw tensor_product.lift.tmul,
    dsimp,
    simp only [one_smul],
  end }

instance jfkdh (W : Rep k G) :
  @is_scalar_tower k (monoid_algebra k G) W.ρ.as_module _ _
  (by haveI : module k W.ρ.as_module := Rep.module W; apply_instance) :=
{ smul_assoc := λ x y z,
  begin
    show representation.as_algebra_hom W.ρ (x • y) z =
      x • (representation.as_algebra_hom W.ρ y z),
    refine y.induction_on _ _ _,
    { intro g,
      simp only [monoid_algebra.of_apply, finsupp.smul_single', mul_one,
        representation.as_algebra_hom_single, linear_map.smul_apply, one_smul] },
    { intros f g hf hg,
      simp only [alg_hom.map_smul, linear_map.smul_apply] },
    { intros r f hf,
      simp only [alg_hom.map_smul, linear_map.smul_apply], }
  end }

/-instance huh (M : Module (monoid_algebra k G)) :
  @is_scalar_tower k (monoid_algebra k G) M _ _
    (by haveI : module k M := Module.module_of_algebra_Module M; apply_instance) :=
sorry-/

variables (k G V)

def linear_equiv_of_fully_faithful (k : Type*) {C D : Type*} [category C] [category D]
  [semiring k] [preadditive C] [preadditive D] [linear k C] [linear k D]
  (F : C ⥤ D) [full F] [faithful F] [F.additive] [F.linear k] (X Y : C) :
  (X ⟶ Y) ≃ₗ[k] (F.obj X ⟶ F.obj Y) :=
{ map_add' := by intros; simp,
  map_smul' := by intros; simp, .. equiv_of_fully_faithful F }

instance kjfa : (@equivalence_Module_monoid_algebra k G _ _).functor.additive :=
{ map_add' := by intros; refl }

instance fdjk : (@equivalence_Module_monoid_algebra k G _ _).functor.linear k :=
{ map_smul' := λ X Y f r, linear_map.ext (λ x, show _ = representation.as_algebra_hom _ _ _,
    by simpa) }

variables (B : Rep k G)
noncomputable def woohoo := linear_equiv_of_fully_faithful k
  (@equivalence_Module_monoid_algebra k G _ _).functor
  (Rep.of $ (representation.of_mul_action k G (fin (n + 1) → G))) B
#check woohoo
/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrow_congr (R : Sort*) {S M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₂₁] [add_comm_monoid M₂₂]
  [module S M₁] [module S M₂] [module R M₂₁] [module R M₂₂] [module S M₂₁] [module S M₂₂]
  [is_scalar_tower R S M₂₁] [is_scalar_tower R S M₂₂]
  (e₁ : M₁ ≃ₗ[S] M₂) (e₂ : M₂₁ ≃ₗ[S] M₂₂) :
  (M₁ →ₗ[S] M₂₁) ≃ₗ[R] (M₂ →ₗ[S] M₂₂) :=
{ to_fun := λ f : M₁ →ₗ[S] M₂₁, (e₂ : M₂₁ →ₗ[S] M₂₂).comp $ f.comp (e₁.symm : M₂ →ₗ[S] M₁),
  inv_fun := λ f, (e₂.symm : M₂₂ →ₗ[S] M₂₁).comp $ f.comp (e₁ : M₁ →ₗ[S] M₂),
  left_inv := λ f, by { ext x, simp only [linear_equiv.symm_apply_apply,
    function.comp_app, linear_map.coe_comp, linear_equiv.coe_coe]},
  right_inv := λ f, by { ext x, simp only [function.comp_app,
    linear_equiv.apply_symm_apply, linear_map.coe_comp, linear_equiv.coe_coe]},
  map_add' := λ f g, by { ext x, simp only [map_add, linear_map.add_apply,
    function.comp_app, linear_map.coe_comp, linear_equiv.coe_coe]},
  map_smul' := λ c f, by { ext x,
    simp only [linear_map.coe_comp, function.comp_app, linear_map.smul_apply,
      ring_hom.id_apply, linear_map.map_smul_of_tower]} }

#check ((woohoo k G n B).trans
(linear_arrow_congr k
  (group_cohomology.resolution.of_mul_action_basis_aux k G n).to_Module_iso
  (iso.refl (to_Module_monoid_algebra.obj B))).symm)
#check linear_equiv.arrow_congr


#check linear_map.module

#check ({ map_smul' := _, ..add_equiv.refl _ } : (Module.of (monoid_algebra k G) (monoid_algebra k G ⊗ ((fin n → G) →₀ k))
  ⟶ to_Module_monoid_algebra.obj B) ≃ₗ[k] monoid_algebra k G ⊗ ((fin n → G) →₀ k) →ₗ[monoid_algebra k G] B.ρ.as_module)

def huh : restrict_scalars k (monoid_algebra k G) B.ρ.as_module ≃ₗ[k] B :=
{ map_smul' := λ r x,
  begin
    show representation.as_algebra_hom _ _ _ = _,
    simp,
  end, ..add_equiv.refl _ }


/-#exit
({ map_smul' := _, ..add_equiv.refl _ } : (Module.of (monoid_algebra k G) (monoid_algebra k G ⊗ ((fin n → G) →₀ k))
  ⟶ to_Module_monoid_algebra.obj B) ≃ₗ[k] monoid_algebra k G ⊗ ((fin n → G) →₀ k) →ₗ[monoid_algebra k G] B.ρ.as_module).trans
  (@base_change_hom_equiv.{u u u u} k (monoid_algebra k G) _ _
_ _ _ _ _ _ _ B.ρ.as_module_module _)-/
#check restrict_scalars
noncomputable def please :
  (@Module.of (monoid_algebra k G) _ (tensor_product k (monoid_algebra k G)
  ((fin n → G) →₀ k)) _ tensor_product.left_module ⟶ to_Module_monoid_algebra.obj B)
  ≃ₗ[k] (((fin n → G) →₀ k) →ₗ[k] B) :=
linear_equiv.symm
((@base_change_hom_equiv.{u u u u} k (monoid_algebra k G) _ _
_ _ _ _ _ _ _ B.ρ.as_module_module _).symm.trans
({ map_smul' := sorry, ..add_equiv.refl _ } : _ ≃ₗ[k] _))

#check linear_arrow_congr k (equiv_tensor k G n) (iso.refl B)


#exit
def equiv_inhomogeneous_cochain :
  (Rep.of_mul_action k G (fin (n + 1) → G) ⟶ B) ≃ₗ[k] ((fin n → G) → B) :=
((linear_equiv_of_fully_faithful k
  (@equivalence_Module_monoid_algebra k G _ _).functor
  (Rep.of $ (representation.of_mul_action k G (fin (n + 1) → G))) B).trans
((linear_arrow_congr k
  (group_cohomology.resolution.of_mul_action_basis_aux k G n).to_Module_iso
  (iso.refl (to_Module_monoid_algebra.obj B))).symm)).trans _


  #exit
  (linear_equiv.symm
((@base_change_hom_equiv.{u u u u} k (monoid_algebra k G) _ _
_ _ _ _ _ _ _ B.ρ.as_module_module _).symm.trans
({ map_smul' := sorry, ..add_equiv.refl _ } : _ ≃ₗ[k] _)))

#exit
begin
refine linear_equiv.trans _
(@base_change_hom_equiv.{u u u u} k (monoid_algebra k G) _ _
_ _ _ _ _ _ _ B.ρ.as_module_module _),
exact ring_hom.id _,
exact ring_hom.id _,
sorry,
sorry,
sorry,
sorry,
refine ({ map_smul' := _, ..add_equiv.refl _ }),
intros,
simp only [add_equiv.to_fun_eq_coe, add_equiv.refl_apply, ring_hom.id_apply],
refine linear_map.ext (λ y, _),
show representation.as_algebra_hom _ _ _ = _,
simp,
end



#check finsupp.lift
#check (((woohoo k G n B).trans
(linear_arrow_congr k
  (group_cohomology.resolution.of_mul_action_basis_aux k G n).to_Module_iso
  (iso.refl (to_Module_monoid_algebra.obj B))).symm).trans (please _ _ _ _)).trans
  (finsupp.llift k B k (fin n → G)).symm

#check linear_equiv.trans
#exit

#check (linear_equiv.arrow_congr
  (group_cohomology.resolution.of_mul_action_basis_aux k G n) (linear_equiv.refl _ B.ρ.as_module)).symm.to_Module_iso
/-def uhm : ((@equivalence_Module_monoid_algebra k G _ _).functor.obj
  (Rep.of $ (representation.of_mul_action k G (fin (n + 1) → G))) →ₗ[monoid_algebra k G]
  (@equivalence_Module_monoid_algebra k G _ _).functor.obj B)
  ≃ₗ[monoid_algebra k G] ((representation.of_mul_action k G (fin (n + 1) → G)).as_module
    →ₗ[monoid_algebra k G] B.ρ.as_module) :=
linear_equiv.refl _ _-/

#check woohoo k G B
#exit
noncomputable def fucksake :
  ((representation.of_mul_action k G G).tprod (1 : G →* (V →ₗ[k] V))).as_module
  ≃ₗ[monoid_algebra k G] tensor_product k (monoid_algebra k G) V :=
tensor_product.congr _ _
--linear_equiv.refl (monoid_algebra k G) (tensor_product k (monoid_algebra k G) V)

noncomputable def fucksake2 :
  to_Module_monoid_algebra.obj (Rep.of_mul_action k G G ⊗ Rep.of (1 : G →* (V →ₗ[k] V)))
  ≅ Module.of _ ((representation.of_mul_action k G G).tprod (1 : G →* (V →ₗ[k] V))).as_module :=
iso.refl _

noncomputable def imgonnascream : Module.of (monoid_algebra k G)
  ((representation.of_mul_action k G G).tprod (1 : G →* (V →ₗ[k] V))).as_module
  ≅ @Module.of (monoid_algebra k G) _ (tensor_product k (monoid_algebra k G) V) _
    tensor_product.left_module :=
iso.refl _

noncomputable def fucksake3 :
  to_Module_monoid_algebra.obj (Rep.of_mul_action k G G ⊗ Rep.of (1 : G →* (V →ₗ[k] V)))
  ≅ @Module.of (monoid_algebra k G) _ (tensor_product k (monoid_algebra k G) V) _
    tensor_product.left_module :=
sorry
--def ummm2 : (Rep.of_mul_action k G G ⊗ V ⟶ W) ≃ₗ[k]
--  (tensor_product k (monoid_algebra k G) V →ₗ[monoid_algebra k G] W.ρ.as_module) :=

#check (linear.left_comp k V (to_tensor k G n))
#check linear
#check equivalence

def fucksake (V W : Rep k G) : (V ⟶ W) ≃ₗ[k]
  (V.ρ.as_module →ₗ[monoid_algebra k G] W.ρ.as_module) :=


#check tensor_hom (Rep.of_mul_action k G G) (Rep.of 1) V
noncomputable def hmmmm : (of_mul_action k G (fin (n + 1) → G) ⟶ V) ≃ₗ[k] ((fin n → G) → V) :=
(Rep.arrow_congr (equiv_tensor k G n) (iso.refl _)).trans
_
