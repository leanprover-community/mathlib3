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
variables (M : Type u) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)
variables {G n}

lemma helpful {f : fin n → G} {i : fin (n + 1)} :
  ↑i < (list.of_fn f).inits.length :=
by cases i with i1 i2; simp only [i2, list.length_of_fn, list.length_inits, fin.coe_mk]

def to_prod (f : fin n → G) : fin (n + 1) → G :=
λ i, ((list.of_fn f).inits.nth_le i helpful).prod

variables (G n)

def to_tensor_aux (x : fin (n + 1) → G) : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
tensor_product.tmul _ (group_ring.of G (x 0))
  (finsupp.single (λ i, (x i)⁻¹ * x i.succ) 1)

@[simps] def to_tensor_add_hom : group_ring (fin (n + 1) → G) →+ group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ to_fun := finsupp.lift_add_hom (λ x,
  { to_fun := zmultiples_hom _ (to_tensor_aux G n x),
    map_zero' := by simp only [zmultiples_hom_apply, zero_smul],
    map_add' := λ f g, by { dsimp, rw add_smul } }),
  map_zero' := by { simp only [finsupp.lift_add_hom_apply, finsupp.sum_zero_index], },
  map_add' := λ f g, by {simp only [finsupp.sum_add_index', finsupp.lift_add_hom_apply]} }

def to_tensor : group_ring (fin (n + 1) → G) →ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
group_ring.mk_linear (to_tensor_add_hom G n) $ λ g x,
begin
  refine x.induction_on _ _ _,
  { intro y,
    unfold to_tensor_add_hom to_tensor_aux,
    dsimp,
    simp only [zmultiples_hom_apply, zero_smul, one_zsmul, finsupp.sum_single_index,
      group_ring.single_smul_single, one_mul],
    dsimp, simp only [mul_inv_rev],
    congr' 1,
    { dsimp, rw monoid_algebra.single_mul_single, rw mul_one},
    { dsimp,
    congr' 1,
    ext, simp only [smul_eq_mul, pi.smul_apply, fin.tail_def],
    assoc_rw inv_mul_cancel_left} },
  { intros y z hy hz,
    simp only [smul_add, add_monoid_hom.map_add, hy, hz] },
  { intros r y hy,
    rw smul_comm,
    rw add_monoid_hom.map_zsmul,
    rw hy,
    rw add_monoid_hom.map_zsmul,
    rw smul_comm,
      }
end

def of_tensor_add_hom :
  group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ) →+ group_ring (fin (n + 1) → G) :=
(tensor_product.lift (finsupp.lift _ _ _ $ λ g, finsupp.lift _ _ _
  (λ f, group_ring.of (fin (n + 1) → G) (g • to_prod f)))).to_add_monoid_hom

def of_tensor : group_ring G ⊗[ℤ] ((fin n → G) →₀ ℤ)
  →ₗ[group_ring G] group_ring (fin (n + 1) → G) :=
group_ring.mk_linear (of_tensor_add_hom G n) $
λ g x,
begin
  unfold of_tensor_add_hom,
  refine tensor_product.induction_on x _ _ _,
  { simp only [smul_zero, map_zero], },
  { intros y z,
    refine y.induction_on _ _ _,
    { intro w,
      dsimp,
      rw tensor_product.smul_tmul',
      rw smul_eq_mul,
      rw monoid_algebra.single_mul_single,
      rw one_mul,
      rw tensor_product.lift.tmul,
      rw tensor_product.lift.tmul,
      dsimp,
      rw finsupp.sum_single_index,
      rw finsupp.sum_single_index,
      simp only [one_smul],
      dsimp,
      refine z.induction_linear _ _ _,
      { simp only [finsupp.sum_zero_index, smul_zero] },
      { intros v u hv hu,
        rw finsupp.sum_add_index,
        rw finsupp.sum_add_index,
        simp only [smul_add, hu, hv],
        { intros, simp only [zero_mul, finsupp.smul_single', finsupp.single_zero]},
        { intros, rw add_smul},
        { intros, simp only [zero_mul, finsupp.smul_single', finsupp.single_zero], },
        { intros, rw add_smul}
        },
      { intros,
        rw finsupp.sum_single_index,
        rw finsupp.sum_single_index,
        rw smul_comm,
        rw group_ring.single_smul_single,
        rw one_mul,
        congr,
        ext, simp only [smul_eq_mul, pi.smul_apply],
        sorry,
        sorry,
        sorry },
      sorry,
      sorry },
      sorry,
      sorry
      }, sorry,
end

example : 1+1= 2 := rfl

lemma equiv_tensor_left_inv_aux (f : fin (n + 1) → G) (i : fin (n + 1)) :
  f 0 • to_prod (λ i : fin n, (f i)⁻¹ * f i.succ) = f :=
begin
  ext,
  unfold to_prod,
  simp only [fin.coe_eq_cast_succ, list.nth_le_inits, smul_eq_mul, pi.smul_apply],

end

def equiv_tensor : group_ring (fin (n + 1) → G) ≃ₗ[group_ring G] group_ring G
  ⊗[ℤ] ((fin n → G) →₀ ℤ) :=
{ inv_fun := of_tensor G n,
  left_inv := λ x, by {
    refine x.induction_on _ _ _,
    { intro g,
      unfold to_tensor of_tensor of_tensor_add_hom to_tensor_add_hom to_prod,
      dsimp,
      rw finsupp.sum_single_index,
      rw zmultiples_hom_apply,
      rw one_smul,
      unfold to_tensor_aux,
      dsimp,
      rw tensor_product.lift.tmul,
      dsimp,
      rw finsupp.sum_single_index,
      rw one_smul,
      rw finsupp.lift_apply,
      rw finsupp.sum_single_index,
      rw one_smul,

     /- dsimp,
      rw finsupp.sum_single_index,
      rw zmultiples_hom_apply,
      rw one_smul,
      unfold to_tensor_aux,
      dsimp,
      rw tensor_product.lift.tmul,
      dsimp,
      rw finsupp.sum_single_index,
      rw one_smul,
      dsimp,
      rw finsupp.sum_single_index,
      sorry,-/
     all_goals {sorry} },
    sorry, sorry
  },
  right_inv := λ x, by
  { refine tensor_product.induction_on x _ _ _,
    sorry,
    { intros y z,
      unfold to_tensor of_tensor of_tensor_add_hom to_tensor_add_hom,
      dsimp,
      rw tensor_product.lift.tmul, sorry,
      }, sorry }, ..to_tensor G n }


@[simp] lemma equiv_tensor_apply (x : fin (n + 1) → G) :
  equiv_tensor G n (of _ x) = (of G (x 0)) ⊗ₜ (finsupp.single ((x 0)⁻¹ • fin.tail x) 1) :=
begin
  unfold equiv_tensor to_tensor,
  dsimp,
  rw finsupp.sum_single_index,
  { exact one_smul _ _ },
  { exact zero_smul _ _ },
end

@[simp] lemma equiv_tensor_symm_apply (x : G) (y : fin n → G) :
  (equiv_tensor G n).symm (of G x ⊗ₜ finsupp.single y 1)
    = of _ (fin.cons x (x • y : fin n → G) : fin (n + 1) → G) :=
begin
  erw linear_equiv.coe_symm_mk,
  unfold of_tensor of_tensor_add_hom,
  dsimp,
  rw tensor_product.lift.tmul,
  dsimp,
  rw finsupp.sum_single_index,
  rw one_smul,
  dsimp,
  rw finsupp.sum_single_index,
  rw one_smul,
  { rw zero_smul },
  { rw zero_smul },
end

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
  cochain_equiv G M n f x = f (of _ (@fin.cons n (λ i, G) 1 x)) :=
show f _ = _, by erw [equiv_tensor_symm_apply, one_smul]; refl

@[simp] lemma cochain_equiv_symm_apply (f : (fin n → G) → M) (x : fin (n + 1) → G) :
  (cochain_equiv G M n).symm f (of _ x) = of _ (x 0) • f ((x 0)⁻¹ • fin.tail x) :=
begin
  unfold cochain_equiv,
  dsimp,
  erw equiv_tensor_apply,
  rw linear_map.id_apply,
  rw dom_tensor_int_equiv_symm_apply,
  rw add_equiv.symm_symm,
  dsimp,
  erw finsupp.lift_apply,
  rw finsupp.sum_single_index,
  rw one_smul,
  rw zero_smul,
end

open group_ring

variables {G M n} (f : fin n → G) (i : fin (n + 1))

lemma cochain_comm_aux (x : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) :
  cochain.d G M _ (cochain_equiv G M _ x)
    = cochain_equiv G M _ (x.comp $ group_ring.d G rfl)  :=
begin
  ext g,
  rw cochain_equiv_apply,
  unfold cochain.d,
  dsimp,
  unfold d_to_fun,
  rw d_single,
  simp only [cochain_equiv_apply],
  rw linear_map.map_sum,
  symmetry,
  rw finset.range_succ,
  rw finset.sum_insert,

end

lemma cochain_succ_comm (x : cochain_succ G M (n + 1)) :
  cochain_succ_add_equiv _ _ _ (cochain_succ.d rfl x) = ((map_std_resn G M).d _ _).unop
    (hom_equiv_yoneda _ _ _ (cochain_succ_add_equiv G M _ x)) :=
begin
  rw [map_std_resn_d_apply, cochain_succ_comm_aux],
  refl,
end

lemma cochain_succ_symm_comm (x : group_ring (fin (n + 1) → G) →ₗ[group_ring G] M) :
  (cochain_succ_add_equiv G M _).symm (((map_std_resn G M).d _ _).unop (hom_equiv_yoneda _ _ _ x))
    = cochain_succ.d rfl ((cochain_succ_add_equiv G M _).symm x) :=
begin
  rw [add_equiv.symm_apply_eq, cochain_succ_comm, add_equiv.apply_symm_apply],
end

/-- The cochain map from our complex of homogeneous cochains to `Hom(-, M)` of our
  projective resolution of the trivial `ℤ[G]`-module `ℤ`. -/
def cochain_succ_to_map_std_resn :
  cochain_succ.complex G M ⟶ (map_std_resn G M).unop_obj :=
{ f := λ i, (cochain_succ_add_equiv G M (i + 1)).to_add_monoid_hom.to_int_linear_map,
  comm' := λ i j hij,
  begin
    cases hij,
    ext1,
    simp only [category_theory.comp_apply],
    erw [cochain_complex.of_d, cochain_succ_comm],
    refl,
  end }

/-- The cochain map from `Hom(-, M)` of our projective resolution of the trivial `ℤ[G]`-module `ℤ`
  to our complex of homogeneous cochains. -/
def map_std_resn_to_cochain_succ :
  (map_std_resn G M).unop_obj ⟶ cochain_succ.complex G M :=
{ f := λ i, ((cochain_succ_add_equiv G M (i + 1)).trans
    (hom_equiv_yoneda _ _ _)).symm.to_add_monoid_hom.to_int_linear_map,
  comm' := λ i j hij,
  begin
    cases hij,
    ext1,
    simp only [category_theory.comp_apply],
    erw [cochain_complex.of_d, cochain_succ_symm_comm],
    refl,
  end }

/-- Homotopy equivalence between complex of homogeneous cochains and `Hom(-, M)`
  of our projective resolution of trivial `ℤ[G]`-module `ℤ`. -/
def homotopy_equiv_cochain_succ :
  homotopy_equiv (cochain_succ.complex G M) (map_std_resn G M).unop_obj :=
{ hom := cochain_succ_to_map_std_resn G M,
  inv := map_std_resn_to_cochain_succ G M,
  homotopy_hom_inv_id := homotopy.of_eq $
  begin
    ext n x i,
    congr' 1,
    exact add_equiv.apply_symm_apply _ _,
  end,
  homotopy_inv_hom_id := homotopy.of_eq $
  begin
    ext n x i,
    congr' 1,
    exact add_equiv.apply_symm_apply _ _,
  end }
end group_ring
