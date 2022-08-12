import representation_theory.cohomology.std_resn
import linear_algebra.tensor_product
import ring_theory.tensor_product
import representation_theory.cohomology.shenyang
universes v u
noncomputable theory
open_locale tensor_product
open linear_equiv function linear_map Rep
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

variables {k : Type u} [comm_ring k] {G : Type u} [group G] {V : Type u}
  [add_comm_group V] [module k V] (ρ : representation k G V) (n : ℕ)

#exit
def cochain_equiv :
  (of_mul_action k G (fin (n + 1) → G) ⟶ Rep.of ρ) ≃ₗ[k] ((fin n → G) → V) :=
#exit
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
