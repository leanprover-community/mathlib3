import representation_theory.group_cohomology_resolution

universes v u
noncomputable theory
open category_theory
set_option profiler true
--from here not sure if I need any of this
noncomputable def finsupp.llift (S M R : Type*) [comm_semiring S] [semiring R]
  [algebra S R] [add_comm_monoid M] [module S M] [module R M] [is_scalar_tower S R M] (X : Type*) :
  (X → M) ≃ₗ[S] ((X →₀ R) →ₗ[R] M) :=
{ map_smul' :=
  begin
    intros,
    dsimp,
    ext,
    simp only [linear_map.coe_comp, function.comp_app, finsupp.lsingle_apply,
      finsupp.lift_apply, pi.smul_apply, finsupp.sum_single_index, zero_smul, one_smul,
      linear_map.smul_apply],
  end, ..finsupp.lift M R X }

@[simp] lemma finsupp.llift_apply {S M R : Type*} [comm_semiring S] [semiring R]
  [algebra S R] [add_comm_monoid M] [module S M] [module R M] [is_scalar_tower S R M] {X : Type*}
  (f : X → M) (x : X →₀ R) :
  finsupp.llift S M R X f x = finsupp.lift M R X f x := rfl

@[simp] lemma finsupp.llift_symm_apply {S M R : Type*} [comm_semiring S] [semiring R]
  [algebra S R] [add_comm_monoid M] [module S M] [module R M] [is_scalar_tower S R M] {X : Type*}
  (f : (X →₀ R) →ₗ[R] M) (x : X) :
  (finsupp.llift S M R X).symm f x = f (finsupp.single x 1) := rfl

open Rep category_theory group_cohomology.resolution
set_option profiler true
def linear.arrow_congr (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) :
  (X ⟶ W) ≃ₗ[k] (Y ⟶ Z) :=
{ inv_fun := (linear.left_comp k W f₁.hom).comp (linear.right_comp k Y f₂.symm.hom),
  left_inv := λ x, by simp only [iso.symm_hom, linear_map.to_fun_eq_coe, linear_map.coe_comp,
    function.comp_app, linear.left_comp_apply, linear.right_comp_apply, category.assoc,
    iso.hom_inv_id, category.comp_id, iso.hom_inv_id_assoc],
  right_inv := λ x, by simp only [iso.symm_hom, linear_map.coe_comp, function.comp_app,
    linear.right_comp_apply, linear.left_comp_apply, linear_map.to_fun_eq_coe,
    iso.inv_hom_id_assoc, category.assoc, iso.inv_hom_id, category.comp_id],
  ..(linear.right_comp k Y f₂.hom).comp (linear.left_comp k W f₁.symm.hom) }

lemma linear.arrow_congr_apply (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : X ⟶ W) :
  linear.arrow_congr k f₁ f₂ f = (f₁.inv ≫ f) ≫ f₂.hom := rfl

lemma linear.arrow_congr_symm_apply (k : Type*) {C : Type*} [category C] [semiring k]
  [preadditive C] [linear k C] {X Y W Z : C} (f₁ : X ≅ Y) (f₂ : W ≅ Z) (f : Y ⟶ Z) :
  (linear.arrow_congr k f₁ f₂).symm f = f₁.hom ≫ f ≫ f₂.inv := rfl

section

variables {k G : Type*} [comm_ring k] [group G] {V : Type} [add_comm_group V] [module k V]
(n : ℕ) (ρ : representation k G V)

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

lemma representation.one_apply (g : G) (x : V) :
  (1 : representation k G V) g x = x := rfl

end
--now we get to stuff I probably do need

namespace Rep
variables {k G : Type u} [comm_ring k] [group G] {A B C : Rep k G}

@[simp] lemma monoidal_category.braiding_hom_apply (x : A) (y : B) :
  Action.hom.hom (β_ A B).hom (tensor_product.tmul k x y) = tensor_product.tmul k y x := rfl

@[simp] lemma monoidal_category.braiding_inv_apply (x : A) (y : B) :
  Action.hom.hom (β_ A B).inv (tensor_product.tmul k y x) = tensor_product.tmul k x y := rfl

variables (A B C)

noncomputable def monoidal_closed.linear_hom_equiv :
  (A ⊗ B ⟶ C) ≃ₗ[k] (B ⟶ (A ⟶[Rep k G] C)) :=
{ map_add' := λ f g, rfl,
  map_smul' := λ r f, rfl, ..(ihom.adjunction A).hom_equiv _ _ }

noncomputable def monoidal_closed.linear_hom_equiv_comm :
    (A ⊗ B ⟶ C) ≃ₗ[k] (A ⟶ (B ⟶[Rep k G] C)) :=
(linear.arrow_congr k (β_ A B) (iso.refl _)) ≪≫ₗ
  monoidal_closed.linear_hom_equiv _ _ _

variables {A B C}

lemma monoidal_closed.linear_hom_equiv_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.linear_hom_equiv A B C f).hom =
  (tensor_product.curry f.hom).flip :=
monoidal_closed_curry _

lemma monoidal_closed.linear_hom_equiv_comm_hom (f : A ⊗ B ⟶ C) :
  (monoidal_closed.linear_hom_equiv_comm A B C f).hom =
 tensor_product.curry f.hom :=
begin
  dunfold monoidal_closed.linear_hom_equiv_comm,
  refine linear_map.ext (λ x, linear_map.ext (λ y, _)),
  simp only [linear_equiv.trans_apply, monoidal_closed.linear_hom_equiv_hom,
    linear.arrow_congr_apply, iso.refl_hom, iso.symm_hom, linear_map.to_fun_eq_coe,
    linear_map.coe_comp, function.comp_app, linear.left_comp_apply, linear.right_comp_apply,
    category.comp_id, Action.comp_hom, linear_map.flip_apply, tensor_product.curry_apply,
    Module.coe_comp, function.comp_app, Rep.monoidal_category.braiding_inv_apply],
end

lemma monoidal_closed.linear_hom_equiv_symm_hom (f : B ⟶ (A ⟶[Rep k G] C)) :
  ((monoidal_closed.linear_hom_equiv A B C).symm f).hom =
  tensor_product.uncurry k A B C f.hom.flip :=
monoidal_closed_uncurry _

lemma monoidal_closed.linear_hom_equiv_comm_symm_hom (f : A ⟶ (B ⟶[Rep k G] C)) :
  ((monoidal_closed.linear_hom_equiv_comm A B C).symm f).hom =
  tensor_product.uncurry k A B C f.hom :=
begin
  dunfold monoidal_closed.linear_hom_equiv_comm,
  refine tensor_product.algebra_tensor_module.curry_injective
    (linear_map.ext (λ x, linear_map.ext (λ y, _))),
  simp only [linear_equiv.trans_symm, linear_equiv.trans_apply, linear.arrow_congr_symm_apply,
    iso.refl_inv, linear_map.coe_comp, function.comp_app, category.comp_id, Action.comp_hom,
    monoidal_closed.linear_hom_equiv_symm_hom, tensor_product.algebra_tensor_module.curry_apply,
    linear_map.coe_restrict_scalars, linear_map.to_fun_eq_coe, linear_map.flip_apply,
    tensor_product.curry_apply, Module.coe_comp, function.comp_app,
    Rep.monoidal_category.braiding_hom_apply, tensor_product.uncurry_apply],
end

variables (A)

@[simps] noncomputable def of_mul_action_hom_thing (x : A) :
  Rep.of_mul_action k G G ⟶ A :=
{ hom := finsupp.lift _ _ _ (λ g, A.ρ g x),
    comm' := λ g,
    begin
      refine finsupp.lhom_ext' (λ x, linear_map.ext_ring _),
      simp only [linear_map.comp_apply, Module.comp_def, finsupp.lsingle_apply,
        finsupp.lift_apply],
      show finsupp.sum (finsupp.map_domain _ _) _ = _,
      rw [finsupp.map_domain_single,  finsupp.sum_single_index, one_smul, finsupp.sum_single_index,
        one_smul, smul_eq_mul, A.ρ.map_mul, linear_map.mul_apply],
      { refl },
      { rw zero_smul },
      { rw zero_smul },
end }

lemma of_mul_action_hom_thing_apply (x : A) :
  (of_mul_action_hom_thing A x).hom (finsupp.single 1 1) = x :=
begin
  dsimp only [of_mul_action_hom_thing_hom, finsupp.lift_apply],
  rw [finsupp.sum_single_index, one_smul, A.ρ.map_one],
  { refl },
  { rw zero_smul },
end

@[simps] noncomputable def of_mul_action_hom_equiv (A : Rep k G) :
  (Rep.of_mul_action k G G ⟶ A) ≃ₗ[k] A :=
{ to_fun := λ f, f.hom (finsupp.single 1 1),
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ x, of_mul_action_hom_thing A x,
  left_inv := λ f,
  begin
    refine Action.hom.ext _ _ (finsupp.lhom_ext' (λ (x : G), linear_map.ext_ring _)),
    simp only [linear_map.comp_apply, finsupp.lsingle_apply,
      of_mul_action_hom_thing_hom, finsupp.lift_apply],
    rw [finsupp.sum_single_index, one_smul],
    have := linear_map.ext_iff.1 (f.comm x) (finsupp.single 1 1),
    simp only [Module.coe_comp, function.comp_apply, linear_map.to_fun_eq_coe,
      linear_map.comp_apply, Rep.of_ρ] at this,
    erw ←this,
    show f.hom (finsupp.map_domain _ _) = _,
    rw [finsupp.map_domain_single, smul_eq_mul, mul_one],
    { rw zero_smul },
  end,
  right_inv := λ x, of_mul_action_hom_thing_apply A x }

lemma of_mul_action_equiv_symm_single (x : A) (g : G) :
  ((of_mul_action_hom_equiv A).symm x).hom (finsupp.single g 1) = A.ρ g x :=
begin
  simp only [of_mul_action_hom_equiv_symm_apply, of_mul_action_hom_thing_hom,
    finsupp.lift_apply, finsupp.sum_single_index, zero_smul, one_smul],
end

def representation.of_tprod_iso {V W : Type u} [add_comm_group V] [add_comm_group W]
  [module k V] [module k W] (ρ : representation k G V) (τ : representation k G W) :
  Rep.of (ρ.tprod τ) ≅ Rep.of ρ ⊗ Rep.of τ := iso.refl _

def Rep.of_tprod_iso (A B : Rep k G) :
  Rep.of (A.ρ.tprod B.ρ) ≅ A ⊗ B := iso.refl _

lemma representation.of_tprod_iso_apply {V W : Type u} [add_comm_group V] [add_comm_group W]
  [module k V] [module k W] (ρ : representation k G V) (τ : representation k G W)
  (x : tensor_product k V W) :
  (representation.of_tprod_iso ρ τ).hom.hom x = x := rfl

lemma representation.of_tprod_iso_inv_apply {V W : Type u} [add_comm_group V] [add_comm_group W]
  [module k V] [module k W] (ρ : representation k G V) (τ : representation k G W)
  (x : tensor_product k V W) :
  (representation.of_tprod_iso ρ τ).inv.hom x = x := rfl

variables (A) (n : ℕ)

noncomputable def finally :=
linear.arrow_congr k ((equiv_tensor k G n).trans
  ((representation.of_mul_action k G G).of_tprod_iso 1)) (iso.refl _) ≪≫ₗ
  ((monoidal_closed.linear_hom_equiv_comm _ _ _) ≪≫ₗ (of_mul_action_hom_equiv _))
≪≫ₗ (finsupp.llift k A k (fin n → G)).symm

--might not need
lemma equiv_tensor_hom_apply (f : fin (n + 1) → G) (m : k) :
(equiv_tensor k G n).hom.hom (finsupp.single f m) = tensor_product.tmul k (finsupp.single (f 0) m)
  (finsupp.single (λ (i : fin n), (f ↑i)⁻¹ * f i.succ) 1) := to_tensor_aux_single _ _

lemma equiv_tensor_inv_apply (g : G) (m : k) (x : (fin n → G) →₀ k) :
  (equiv_tensor k G n).inv.hom (tensor_product.tmul k (finsupp.single g m) x)
  = ((finsupp.lift ((fin (n + 1) → G) →₀ k) k (fin n → G))
  (λ (f : fin n → G), finsupp.single (g • fin.partial_prod f) m)) x :=
of_tensor_aux_single _ _ _

lemma finally_apply (f : Rep.of_mul_action k G (fin (n + 1) → G) ⟶ A) (x : fin n → G) :
  finally A n f x = f.hom (finsupp.single (fin.partial_prod x) 1) :=
begin
  unfold finally,
  simp only [linear_equiv.trans_apply, finsupp.llift_symm_apply, of_mul_action_hom_equiv_apply,
    monoidal_closed.linear_hom_equiv_comm_hom, tensor_product.curry_apply,
    linear.arrow_congr_apply, iso.refl_hom, category.comp_id, iso.trans_inv, Action.comp_hom,
    Module.comp_def, linear_map.comp_apply, linear_map.to_fun_eq_coe,
    representation.of_tprod_iso_apply, iso.refl_inv],
  dsimp only [equiv_tensor_inv_def, of_tensor,
    representation.of_tprod_iso_inv_apply],
  rw [of_tensor_aux_single, finsupp.lift_apply, finsupp.sum_single_index,
    one_smul, one_smul],
  { rw zero_smul },
end

lemma finally_symm_apply (f : (fin n → G) → A) (x : fin (n + 1) → G) :
  ((finally A n).symm f).hom (finsupp.single x 1)
    = A.ρ (x 0) (f (λ (i : fin n), (x ↑i)⁻¹ * x i.succ)) :=
begin
  unfold finally,
  simp only [linear_equiv.trans_symm, linear_equiv.symm_symm, linear_equiv.trans_apply,
    of_mul_action_hom_equiv_symm_apply, linear.arrow_congr_symm_apply, Action.comp_hom,
    iso.refl_inv, category.comp_id, monoidal_closed.linear_hom_equiv_comm_symm_hom, iso.trans_hom,
    Module.comp_def, linear_map.comp_apply],
  dsimp only [representation.of_tprod_iso_apply, equiv_tensor_def, to_tensor],
  rw [to_tensor_aux_single, tensor_product.uncurry_apply, of_mul_action_hom_thing_hom,
    finsupp.lift_apply, finsupp.sum_single_index, one_smul, ihom_obj_ρ_eq, Rep.of_ρ,
    representation.lin_hom_apply, linear_map.comp_apply, linear_map.comp_apply,
    finsupp.llift_apply, finsupp.lift_apply],
  erw [finsupp.sum_single_index, one_smul],
  { rw zero_smul },
  { rw zero_smul }
end

variables (A)

noncomputable abbreviation hom_resolution := homological_complex.unop
  ((((linear_yoneda k (Rep k G)).obj A).right_op.map_homological_complex _).obj
  (group_cohomology.resolution k G))

variables {A}

-- weird that simplifying the type of x made this not time out when i simp only in it in inhomog
lemma hom_resolution_d_apply (i j : ℕ) (x : (group_cohomology.resolution k G).X i ⟶ A) :
  A.hom_resolution.d i j x = (group_cohomology.resolution k G).d j i ≫ x :=
rfl

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

lemma fucksake_fin (i : fin n) :
  i.cast_succ = (↑(↑i : ℕ)) :=
begin
  ext,
  rw fin.coe_coe_of_lt (lt_trans (fin.is_lt _) n.lt_succ_self),
  refl,
end

lemma urhm (f : (fin n → G) → A) (g : fin (n + 1) → G) (a : fin (n + 1)) :
  (-1 : k) ^ (a.succ : ℕ) • ((finally A n).symm f).hom
  (finsupp.single (fin.partial_prod g ∘ a.succ.succ_above) 1)
  = (-1 : k) ^ ((a : ℕ) + 1) • f (F (a : ℕ) g) :=
begin
  simp only [finally_symm_apply, fin.coe_succ, function.comp_app, fin.succ_succ_above_zero,
    fin.partial_prod_zero, map_one, fin.coe_eq_cast_succ, fin.succ_succ_above_succ,
    linear_map.one_apply, fin.partial_prod_succ],
  congr,
  ext,
  by_cases (x : ℕ) < a,
  { rw [fin.succ_above_below, fin.succ_above_below, inv_mul_cancel_left, F_lt_apply _ _ _ h],
    { refl },
    { assumption },
    { simp only [fin.lt_def, fin.val_eq_coe, fin.coe_cast_succ,
      fin.coe_succ, lt_trans h (nat.lt_succ_self _)] }},
  { by_cases hx : (x : ℕ) = a,
    { rw [F_eq_apply _ _ _ hx, fin.succ_above_below, fin.succ_above_above, fin.cast_succ_fin_succ,
        fin.partial_prod_succ, mul_assoc, inv_mul_cancel_left, fin.add_nat_one],
      { refl },
      { simpa only [fin.le_iff_coe_le_coe, ←hx] },
      { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ, fin.coe_succ,
        hx, nat.lt_succ_self _] }},
    { rw [F_neg_apply _ _ _ h hx, fin.succ_above_above, fin.succ_above_above,
        fin.partial_prod_succ, fin.cast_succ_fin_succ, fin.partial_prod_succ, inv_mul_cancel_left,
        fin.add_nat_one],
      { exact not_lt.1 h },
      { rw [fin.le_iff_coe_le_coe, fin.coe_succ],
        exact nat.succ_le_of_lt (lt_of_le_of_ne (not_lt.1 h) (ne.symm hx)) }}
  }
end

lemma d_eq (f : (fin n → G) → A) (g : fin (n + 1) → G) :
  ((finally A n).to_Module_iso.inv ≫
    (hom_resolution A).d n (n + 1)
    ≫ (finally A (n + 1)).to_Module_iso.hom) f g = d_to_fun f g :=
begin
  simp only [linear_equiv.to_Module_iso_hom, linear_equiv.to_Module_iso_inv,
    hom_resolution_d_apply, Module.coe_comp, linear_equiv.coe_coe, function.comp_app],
  rw [finally_apply, Action.comp_hom, Module.coe_comp, function.comp_apply,
    group_cohomology.resolution.d_eq, group_cohomology.resolution.d_of, linear_map.map_sum],
  simp only [←finsupp.smul_single_one _ ((-1 : k) ^ _), map_smul],
  rw [d_to_fun, fin.sum_univ_succ, fin.coe_zero, pow_zero, one_smul, finally_symm_apply],
  congr' 1,
  { simp only [function.comp_apply, fin.zero_succ_above, fin.partial_prod_succ,
      fin.cast_succ_zero, fin.partial_prod_zero, one_mul, fin.coe_eq_cast_succ, mul_inv_rev,
      fin.add_nat_one],
    simp only [fin.cast_succ_fin_succ, fin.partial_prod_succ],
    congr,
    ext,
    simp only [←fucksake_fin, mul_assoc, inv_mul_cancel_left], },
  { refine @finset.sum_bij _ (fin (n + 1)) ℕ _ finset.univ (finset.range (n + 1))
 _ _ (λ i hi, i) (λ a ha, finset.mem_range.2 a.2) _ (λ a b ha hb hab, by ext; exact hab)
  (λ a ha, ⟨⟨a, finset.mem_range.1 ha⟩, finset.mem_univ _, rfl⟩),
    intros a ha,
    exact urhm _ _ _,
      }
end

lemma d_eq' (f : (fin n → G) → A) :
  ((finally A n).to_Module_iso.inv ≫
    (hom_resolution A).d n (n + 1)
    ≫ (finally A (n + 1)).to_Module_iso.hom) f = d_to_fun f :=
by ext; exact d_eq _ _

variables (A n)

def d : ((fin n → G) → A) →ₗ[k] (fin (n + 1) → G) → A :=
{ to_fun := d_to_fun,
  map_add' := λ f g,
  begin
    ext x,
    simp only [pi.add_apply, ←d_eq, map_add],
  end,
  map_smul' := λ r f,
  begin
    ext x,
    simpa only [pi.smul_apply, ←d_eq, map_smul],
  end }

lemma d_apply (x : (fin n → G) → A) : A.d n x = d_to_fun x :=
rfl

lemma d_eq'' : ((finally A n).to_Module_iso.inv ≫
  (hom_resolution A).d n (n + 1)
  ≫ (finally A (n + 1)).to_Module_iso.hom) = A.d n :=
by ext; exact d_eq _ _

@[simps] noncomputable def inhomog : cochain_complex (Module k) ℕ :=
cochain_complex.of (λ n, Module.of k ((fin n → G) → A))
(λ n, d A n) (λ n,
begin
  ext x y,
  simp only [Module.coe_comp, function.comp_app, d_apply, linear_map.zero_apply, pi.zero_apply],
  rw ←d_eq', rw ←d_eq',
  simp only [Module.coe_comp, function.comp_app, linear_equiv.to_Module_iso_hom,
    linear_equiv.to_Module_iso_inv, linear_equiv.coe_coe, linear_equiv.symm_apply_apply],
  have := linear_map.ext_iff.1 (A.hom_resolution.d_comp_d n (n + 1) (n + 2)),
  simp only [Module.coe_comp, function.comp_app] at this,
  rw this,
  simp only [linear_map.zero_apply, map_zero, pi.zero_apply],
end)

def inhomog_iso :
  A.inhomog ≅ A.hom_resolution :=
homological_complex.hom.iso_of_components
(λ i, (finally A i).to_Module_iso.symm) $
begin
  intros i j hij,
  dunfold inhomog,
  cases hij,
  erw cochain_complex.of_d,
  rw ←d_eq'',
  rw iso.symm_hom,
  rw iso.symm_hom,
  simp only [category.assoc],
  erw iso.hom_inv_id,
  rw category.comp_id,
  refl,
end

#exit

lemma inhomog_coh_iso :
  A.inhomog.homology n ≅ ((Ext k (Rep k G) n).obj
    (opposite.op $ Rep.of representation.trivial)).obj A :=
(homology_obj_iso_of_homotopy_equiv (homotopy_equiv.of_iso (inhomog_iso _)) _) ≪≫
(homological_complex.homological_complex.homology_unop_iso _)
≪≫ (group_cohomology.Ext_iso k G A n).symm
