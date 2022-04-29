import algebra.group.cohomology.std_resn
import algebra.group.cohomology.ext
import linear_algebra.tensor_product
import ring_theory.tensor_product
import algebra.group.cohomology.shenyang
universes v u
noncomputable theory

variables (G : Type u) [group G]
open_locale tensor_product

namespace group_ring
section
variables (M : Type u) [add_comm_group M] [distrib_mul_action G M] (n : ℕ)
variables {G n}

def to_prod (f : fin n → G) : fin (n + 1) → G :=
λ i, ((list.of_fn f).take i).prod

lemma to_prod_zero (f : fin n → G) :
  to_prod f 0 = 1 :=
begin
  unfold to_prod,
  simp only [fin.coe_zero, list.take_zero, list.prod_nil],
end

lemma to_prod_succ (f : fin n → G) (j : fin n) :
  to_prod f j.succ = to_prod f j.cast_succ * (f j) :=
begin
  unfold to_prod,
  simp only [fin.coe_succ, fin.coe_cast_succ],
  rw list.take_succ,
  simp only [mul_right_inj, list.prod_append, list.nth_of_fn],
  rw [list.of_fn_nth_val, dif_pos j.is_lt, fin.eta],
  erw option.to_list_some,
  rw list.prod_singleton
end

lemma to_prod_succ' (f : fin (n + 1) → G) (j : fin (n + 1)) :
  to_prod f j.succ = f 0 * to_prod (fin.tail f) j :=
begin
  unfold to_prod,
  simp only [mul_right_inj, fin.coe_eq_cast_succ, list.take, fin.coe_succ,
    fin.coe_cast_succ, list.of_fn_succ, list.prod_cons],
  refl,
end

variables (G n)

def to_tensor_aux (x : fin (n + 1) → G) (m : ℤ) : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
finsupp.single (x 0) m ⊗ₜ[ℤ] finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1

@[simps] def to_tensor_add_hom : group_ring (fin (n + 1) → G) →+ group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ to_fun := finsupp.lift_add_hom (λ x,
  { to_fun := to_tensor_aux G n x,
    map_zero' := by simp only [to_tensor_aux, tensor_product.zero_tmul, finsupp.single_zero],
    map_add' := λ f g, by { unfold to_tensor_aux, rw [finsupp.single_add, tensor_product.add_tmul] } }),
  map_zero' := by { simp only [finsupp.lift_add_hom_apply, finsupp.sum_zero_index], },
  map_add' := λ f g, by {simp only [finsupp.sum_add_index', finsupp.lift_add_hom_apply]} }

lemma to_tensor_add_hom_single (f : fin (n + 1) → G) (m : ℤ) :
  to_tensor_add_hom G n (finsupp.single f m) =
    (finsupp.single (f 0) m) ⊗ₜ (finsupp.single (λ i, (f i)⁻¹ * f i.succ) 1) :=
begin
  dsimp,
  rw [finsupp.sum_single_index],
  refl,
  { simp only [to_tensor_aux, tensor_product.zero_tmul, finsupp.single_zero] },
end

def to_tensor : group_ring (fin (n + 1) → G) →ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
group_ring.mk_linear (to_tensor_add_hom G n) $ λ g x,
begin
  refine map_smul_of_map_smul_of _ _ _ _,
  intros h x,
  simp only [of_apply, single_smul_single, one_smul, one_mul, to_tensor_add_hom_single],
  dsimp,
  simp only [mul_inv_rev, tensor_product.smul_tmul', smul_eq_mul],
  erw [monoid_algebra.single_mul_single, one_mul],
  congr,
  ext,
  assoc_rw inv_mul_cancel_left,
end

def of_tensor_add_hom :
  group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) →+ group_ring (fin (n + 1) → G) :=
(tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, group_ring.of (fin (n + 1) → G) (g • to_prod f)))).to_add_monoid_hom

lemma of_tensor_add_hom_single (g : G) (m : ℤ) (x : (fin n → G) →₀ ℤ) :
  of_tensor_add_hom G n ((finsupp.single g m) ⊗ₜ x) =
  m • finsupp.lift (group_ring (fin (n + 1) → G)) ℤ (fin n → G)
    (λ f, of _ (g • to_prod f)) x :=
begin
  unfold of_tensor_add_hom,
  dsimp,
  rw tensor_product.lift.tmul,
  dsimp,
  rw finsupp.sum_single_index,
  refl,
  { rw zero_smul }
end

def of_tensor : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ)
  →ₗ[group_ring G] group_ring (fin (n + 1) → G) :=
group_ring.mk_linear (of_tensor_add_hom G n) $
λ g x,
begin
  refine tensor_product.induction_on x _ _ _,
  { simp only [smul_zero, map_zero] },
  { intros x y,
    let F := (of_tensor_add_hom G n).comp (((tensor_product.mk ℤ (group_ring G)
      _).flip y).to_add_monoid_hom.comp $ distrib_mul_action.to_add_monoid_hom (group_ring G)
      (of G g)),
    let G := (distrib_mul_action.to_add_monoid_hom _ (of G g)).comp
      ((of_tensor_add_hom G n).comp ((tensor_product.mk ℤ (group_ring G)
      _).flip y).to_add_monoid_hom),
    refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _ F G _) x,
    intros h z,
    dsimp,
    rw [monoid_algebra.single_mul_single, one_mul, of_tensor_add_hom_single,
      of_tensor_add_hom_single],
    simp only [←linear_map.map_smul],
    dsimp,
    rw finsupp.smul_sum,
    congr,
    ext1 f, ext1 j,
    rw [smul_comm, single_smul_single, one_mul, smul_smul] },
  { intros x y hx hy,
    simp only [smul_add, add_monoid_hom.map_add, hx, hy] },
end

example : 1+1= 2 := rfl

lemma equiv_tensor_left_inv_aux (f : fin (n + 1) → G) :
  f 0 • to_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
begin
  ext,
  cases x with x hn,
  revert hn,
  induction x with x hx,
  { intro hn,
    dsimp,
    rw [to_prod_zero, mul_one] },
  { intro hn,
    dsimp at hx ⊢,
    rw [←fin.succ_mk _ _ (nat.succ_lt_succ_iff.1 hn), to_prod_succ],
    specialize hx (lt_trans (nat.lt_succ_self x) hn),
    erw [←mul_assoc, hx],
    convert mul_inv_cancel_left _ _,
    ext,
    simp only [fin.coe_of_nat_eq_mod, fin.coe_mk, nat.mod_eq_of_lt
      (lt_trans (nat.lt_succ_self _) hn)] }
end

lemma equiv_tensor_right_inv_aux (g : G) (f : fin n → G) (i : fin n) :
  ((g • to_prod f) i)⁻¹ * (g • to_prod f) i.succ = f i :=
begin
  cases i with i hn,
  revert hn,
  induction i with i hi,
  { intro hn,
    dsimp,
    rw [←fin.succ_mk, to_prod_succ],
    simp only [fin.mk_zero, to_prod_zero, mul_one, mul_left_eq_self,
      inv_mul_cancel_left, fin.cast_succ_mk] },
  { intro hn,
    specialize hi (lt_trans (nat.lt_succ_self i) hn),
    simp only [mul_inv_rev, fin.coe_eq_cast_succ, fin.succ_mk, fin.cast_succ_mk,
      smul_eq_mul, pi.smul_apply] at hi ⊢,
    rw [←fin.succ_mk _ _ (lt_trans (nat.lt_succ_self _) hn), ←fin.succ_mk,
      to_prod_succ, to_prod_succ],
    simp only [mul_inv_rev, fin.cast_succ_mk],
    assoc_rw [hi, inv_mul_cancel_left] }
end

def equiv_tensor : group_ring (fin (n + 1) → G) ≃ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ inv_fun := of_tensor G n,
  left_inv := λ x, by {
    refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _
      ((of_tensor G n).comp (to_tensor G n)).to_add_monoid_hom (add_monoid_hom.id _) _) x,
    intros x y,
    dsimp,
    erw [to_tensor_add_hom_single, of_tensor_add_hom_single],
    rw [finsupp.lift_apply, finsupp.sum_single_index, one_smul, of_apply,
      finsupp.smul_single_one, equiv_tensor_left_inv_aux],
    { rw zero_smul }},
  right_inv := λ x, by
  { refine tensor_product.induction_on x _ _ _,
    { simp only [linear_map.to_fun_eq_coe, map_zero] },
    { intros y z,
      dsimp,
      let F := ((to_tensor G n).comp (of_tensor G n)).to_add_monoid_hom.comp ((tensor_product.mk ℤ
        (group_ring G) _).flip z).to_add_monoid_hom,
      refine add_monoid_hom.ext_iff.1 (@finsupp.add_hom_ext _ _ _ _ _ F ((tensor_product.mk ℤ
        (group_ring G) _).flip z).to_add_monoid_hom _) y,
      intros x m,
      dsimp [of_tensor],
      rw [of_tensor_add_hom_single, linear_map.map_smul_of_tower, finsupp.lift_apply],
      simp only [mul_one, finsupp.smul_single', of_apply, linear_map.map_finsupp_sum],
      unfold to_tensor,
      simp only [mk_linear_apply, to_tensor_add_hom_single, equiv_tensor_right_inv_aux],
      dsimp,
      simp only [to_prod_zero, mul_one],
      conv_rhs {rw ←finsupp.sum_single z},
      rw [←finsupp.smul_single_one x m, ←tensor_product.smul_tmul'],
      erw tensor_product.tmul_sum,
      refine congr_arg _ (finset.sum_congr rfl _),
      intros g hg,
      rw [←finsupp.smul_single_one g, ←tensor_product.smul_tmul, finsupp.smul_single_one] },
    { intros z w hz hw,
      dsimp at hz hw ⊢,
      simp only [map_add, hz, hw] } },
  ..to_tensor G n }

@[simp] lemma equiv_tensor_apply (x : fin (n + 1) → G) (m : ℤ) :
  equiv_tensor G n (finsupp.single x m) = (finsupp.single (x 0) m) ⊗ₜ (finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1) :=
to_tensor_add_hom_single _ _ _ _

@[simp] lemma equiv_tensor_symm_apply (g : G) (m : ℤ) (x : (fin n → G) →₀ ℤ) :
  (equiv_tensor G n).symm ((finsupp.single g m) ⊗ₜ x) =
  m • finsupp.lift (group_ring (fin (n + 1) → G)) ℤ (fin n → G)
    (λ f, of _ (g • to_prod f)) x :=
of_tensor_add_hom_single G n _ _ _

end

open tensor_product

section
variables {R : Type*} {A : Type*} {M : Type*} {N : Type*} {P : Type*} [comm_semiring R]
  [semiring A] [algebra R A] [add_comm_monoid M] [module R M] [module A M]
  [is_scalar_tower R A M] [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]
  [module A P] [is_scalar_tower R A P] (n : ℕ)

@[simps] def lift_nc (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (tensor_product.lift (f.restrict_scalars R)).comp
  (algebra.lsmul R _ c) x = (algebra.lsmul R _ c).comp (tensor_product.lift (f.restrict_scalars R)) x,
    from linear_map.ext_iff.1 $ tensor_product.ext' $ λ x y,
    by simp only [linear_map.comp_apply, algebra.lsmul_coe, tensor_product.smul_tmul',
      tensor_product.lift.tmul, linear_map.coe_restrict_scalars_eq_coe,
      f.map_smul, linear_map.smul_apply],
  .. tensor_product.lift (f.restrict_scalars R) }

@[simp] lemma lift_nc_tmul (f : M →ₗ[A] (N →ₗ[R] P)) (x : M) (y : N) :
  lift_nc f (x ⊗ₜ y) = f x y :=
lift.tmul' x y

variables (R A M N P)

@[simps] def uncurry_nc : (M →ₗ[A] (N →ₗ[R] P)) →ₗ[R] ((M ⊗[R] N) →ₗ[A] P) :=
{ to_fun := lift_nc,
  map_add' := λ f g, by { ext x y, dsimp, simp only [lift.tmul], refl },
  map_smul' := λ c f, by { ext x y, dsimp, simp only [lift.tmul], refl }}

@[simps] def lcurry_nc : ((M ⊗[R] N) →ₗ[A] P) →ₗ[R] (M →ₗ[A] (N →ₗ[R] P)) :=
{ to_fun := algebra_tensor_module.curry,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

def lift_nc_equiv : (M →ₗ[A] N →ₗ[R] P) ≃ₗ[R] M ⊗[R] N →ₗ[A] P :=
linear_equiv.of_linear (uncurry_nc R A M N P) (lcurry_nc R A M N P)
(linear_map.ext $ λ f, algebra_tensor_module.ext $ λ x y, lift_nc_tmul _ x y)
  (linear_map.ext $ λ f, linear_map.ext $ λ x, linear_map.ext $ λ y, lift_nc_tmul f x y)

def dom_tensor_equiv (S : Type*) [semiring S] [algebra R S]
  [module S N] [is_scalar_tower R S N] :
  (S ⊗[R] M →ₗ[S] N) ≃ₗ[R] (M →ₗ[R] N) :=
(lift_nc_equiv R S S M N).symm.trans
  (linear_map.ring_lmap_equiv_self S R (M →ₗ[R] N))

def dom_tensor_int_equiv (R : Type*) [ring R] (M : Type*) (N : Type*)
  [add_comm_group M] [add_comm_group N] [module R N] :
  (R ⊗[ℤ] M →ₗ[R] N) ≃+ (M →+ N) :=
((dom_tensor_equiv ℤ M N R).trans (add_monoid_hom_lequiv_int ℤ).symm).to_add_equiv

variables {R A M N P}

@[simp] lemma dom_tensor_equiv_apply {S : Type*} [semiring S] [algebra R S]
  [module S N] [is_scalar_tower R S N] (f : S ⊗[R] M →ₗ[S] N) (x : M) :
  dom_tensor_equiv R M N S f x = f (1 ⊗ₜ x) := rfl

@[simp] lemma dom_tensor_equiv_symm_apply {S : Type*} [semiring S] [algebra R S]
  [module S N] [is_scalar_tower R S N] (f : M →ₗ[R] N) (x : S) (y : M) :
  (dom_tensor_equiv R M N S).symm f (x ⊗ₜ y) = x • f y :=
begin
  unfold dom_tensor_equiv,
  dsimp,
  rw linear_equiv.symm_symm,
  unfold lift_nc_equiv lcurry_nc,
  dsimp,
  simp only [linear_map.one_apply, linear_map.smul_apply, lift.tmul, linear_map.coe_smul_right,
    linear_map.coe_restrict_scalars_eq_coe],
end

@[simp] lemma dom_tensor_int_equiv_apply {R : Type*} [ring R] {M : Type*} {N : Type*}
  [add_comm_group M] [add_comm_group N] [module R N] (f : R ⊗[ℤ] M →ₗ[R] N) (x : M) :
  dom_tensor_int_equiv R M N f x = f (1 ⊗ₜ x) := rfl

@[simp] lemma dom_tensor_int_equiv_symm_apply {R : Type*} [ring R] {M : Type*} {N : Type*}
  [add_comm_group M] [add_comm_group N] [module R N] (f : M →+ N) (x : R) (y : M) :
  (dom_tensor_int_equiv R M N).symm f (x ⊗ₜ y) = x • f y :=
dom_tensor_equiv_symm_apply _ _ _

open linear_equiv function linear_map
--local attribute [priority 100000, instance] tensor_product.left_module
@[simps] def arrow_congr_add_equiv {R M₁ M₂ M₂₁ M₂₂ : Sort*} [semiring R]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₂₁] [add_comm_monoid M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) :
  (M₁ →ₗ[R] M₂₁) ≃+ (M₂ →ₗ[R] M₂₂) :=
{ to_fun := λ f : M₁ →ₗ[R] M₂₁, (e₂ : M₂₁ →ₗ[R] M₂₂).comp $ f.comp (e₁.symm : M₂ →ₗ[R] M₁),
  inv_fun := λ f, (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp $ f.comp (e₁ : M₁ →ₗ[R] M₂),
  left_inv := λ f, by { ext x, simp only [symm_apply_apply, comp_app, coe_comp, linear_equiv.coe_coe]},
  right_inv := λ f, by { ext x, simp only [comp_app, apply_symm_apply, coe_comp, linear_equiv.coe_coe]},
  map_add' := λ f g, by { ext x, simp only [map_add, add_apply, comp_app, coe_comp, linear_equiv.coe_coe]} }

end

variables (M : Type u) [add_comm_group M] [distrib_mul_action G M] (n : ℕ)

@[priority 1] instance huhj : module (group_ring G) M :=
monoid_algebra.total_to_module

def cochain_equiv :
  (group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) ≃+ ((fin n → G) → M) :=
(arrow_congr_add_equiv (equiv_tensor G n) (linear_equiv.refl _ M)).trans
  (((dom_tensor_int_equiv (group_ring G) ((fin n → G) →₀ ℤ) M).trans
  (add_monoid_hom_lequiv_int ℤ).to_add_equiv).trans (finsupp.lift M ℤ (fin n → G)).symm)

@[simp] lemma cochain_equiv_apply (f : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M)
  (x : fin n → G) :
  cochain_equiv G M n f x = f (of _ (to_prod x)) :=
show f _ = _, by erw [equiv_tensor_symm_apply, one_smul];
begin
  dsimp,
  simp only [one_smul],
  rw [finsupp.sum_single_index, one_smul],
  { rw zero_smul }
end

@[simp] lemma cochain_equiv_symm_apply (f : (fin n → G) → M) (x : fin (n + 1) → G) :
  (cochain_equiv G M n).symm f (of _ x) = of _ (x 0) • f (λ i, (x i)⁻¹ * x i.succ) :=
begin
  unfold cochain_equiv,
  dsimp,
  erw equiv_tensor_apply,
  rw [linear_map.id_apply, dom_tensor_int_equiv_symm_apply, add_equiv.symm_symm],
  dsimp,
  erw finsupp.lift_apply,
  rw [finsupp.sum_single_index, one_smul],
  { rw zero_smul },
end

open group_ring

variables {G M n} (f : fin n → G) (i : fin (n + 1))

lemma smul_eq_of_smul (g : G) (m : M) :
  of G g • m = g • m :=
begin
  show finsupp.total _ _ _ _ (finsupp.single _ _) = _,
  rw [finsupp.total_single, one_smul],
end

lemma to_prod_F (g : fin (n + 1) → G) (m : ℕ) (hm : m ∈ finset.range (n + 1))
  (j : fin (n + 1)) : to_prod g (fin.delta rfl (m + 1) j) = to_prod (F m g) j :=
begin
  cases j with j hj,
  revert hj,
  induction j with j hn,
  { intro h0,
    simp only [to_prod_zero, fin.mk_zero, fin.coe_zero, fin.delta,
      if_pos m.succ_pos] },
  { intro hj,
    specialize hn (lt_trans j.lt_succ_self hj),
    rw ←fin.succ_mk _ _ (nat.succ_lt_succ_iff.1 hj),
    rw to_prod_succ,
    unfold fin.delta at ⊢ hn,
    split_ifs,
    { dsimp at ⊢ h hn,
      rw [←fin.succ_mk _ _ (lt_trans j.lt_succ_self hj), to_prod_succ],
      simp only [if_pos (lt_trans j.lt_succ_self h)] at hn,
      erw [hn, F_lt_apply],
      { refl },
      { exact nat.succ_lt_succ_iff.1 h }},
    { dsimp at ⊢ h hn,
      rw [←fin.succ_mk _ _ hj, to_prod_succ, fin.cast_succ_mk, ← hn,
          ←fin.succ_mk _ _ (lt_trans j.lt_succ_self hj), to_prod_succ, fin.cast_succ_mk],
      by_cases hjm : j = m,
      { simp only [F_eq_apply m _ ⟨j, nat.succ_lt_succ_iff.1 hj⟩ hjm,
          if_pos (show j < m + 1, by rw hjm; exact m.lt_succ_self)],
        exact mul_assoc _ _ _ },
      { rw F_neg_apply _ _ ⟨j, nat.succ_lt_succ_iff.1 hj⟩ (λ hl, h $ nat.succ_lt_succ hl) hjm,
        simp only [if_neg (show ¬j < m + 1, from λ h', hjm $ nat.eq_of_le_of_lt_succ
          (nat.le_of_succ_le_succ $ not_lt.1 h) h')],
        conv_rhs {rw ← fin.succ_mk _ _ (lt_trans j.lt_succ_self hj)}, rw to_prod_succ,
        refl, }}}
end

lemma cochain_comm (x : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) :
  cochain.d G M _ (cochain_equiv G M _ x)
    = cochain_equiv G M _ (x.comp $ group_ring.d G rfl) :=
begin
  ext g,
  rw cochain_equiv_apply,
  unfold cochain.d,
  dsimp,
  unfold d_to_fun,
  rw [d_single, linear_map.map_sum],
  symmetry,
  rw [finset.range_add_one', finset.sum_insert, pow_zero, one_mul],
  congr' 1,
  { simp only [cochain_equiv_apply, fin.delta_zero_apply, id.def, fin.cast_refl,
      order_iso.coe_refl, of_apply],
    rw [←smul_eq_of_smul, ←linear_map.map_smul],
    erw of_smul_of,
    congr,
    ext k,
    rw to_prod_succ',
    simp only [to_prod_succ', smul_eq_mul, pi.smul_apply],
    congr,
    ext y,
    cases y,
    refl, },
  { rw finset.sum_map,
    refine finset.sum_congr rfl (λ m hm, _),
    rw [cochain_equiv_apply, ←linear_map.map_smul_of_tower, of_apply, finsupp.smul_single_one],
    congr' 2,
    { dsimp,
      ext j,
      rw to_prod_F _ _ hm, },
    { exact mul_one _ } },
  { simp }
end

lemma cochain_symm_comm (x : (fin n → G) → M) :
  (cochain_equiv G M (n + 1)).symm (cochain.d G M n x)
    = ((cochain_equiv G M n).symm x).comp (group_ring.d G rfl) :=
by rw [add_equiv.symm_apply_eq, ←cochain_comm, add_equiv.apply_symm_apply]

end group_ring
