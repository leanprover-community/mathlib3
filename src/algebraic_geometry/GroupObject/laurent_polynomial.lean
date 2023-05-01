import data.polynomial.laurent
import algebraic_geometry.GroupObject.coalgebra
universes v u

namespace algebra.tensor_product

lemma is_unit_tmul_iff {R A B : Type*} [comm_semiring R] [ring A] [ring B]
  [algebra R A] [algebra R B] (x : A) (y : B) :
  is_unit (x ⊗ₜ[R] y) ↔ is_unit x ∧ is_unit y :=
sorry

open_locale tensor_product

lemma tmul_zpow {R A B : Type*} [comm_semiring R] [ring A] [ring B]
  [algebra R A] [algebra R B] (x : Aˣ) (y : Bˣ) (n : ℤ) :
  (((is_unit.unit ((is_unit_tmul_iff (x : A) (y : B)).2 ⟨units.is_unit x, units.is_unit y⟩)) ^ n : (A ⊗[R] B)ˣ) : A ⊗[R] B)
  = ((x ^ n : Aˣ) : A) ⊗ₜ[R] ((y ^ n : Bˣ) : B) :=
begin
  refine int.induction_on n _ _ _,
  { simpa only [zpow_zero, units.coe_one] },
  { intros i hi,
    simpa only [←int.coe_nat_succ, zpow_coe_nat, units.coe_pow, ←algebra.tensor_product.tmul_pow]},
  { intros,
    rw ←neg_add',
    rw ←neg_one_mul,
    rw zpow_mul,
    rw zpow_mul,
    rw zpow_mul,
    simp only [←int.coe_nat_succ, zpow_coe_nat, units.coe_pow, ←algebra.tensor_product.tmul_pow],
    congr' 1,
    simp only [zpow_neg, zpow_one],
    rw units.inv_eq_of_mul_eq_one_left,
    show _ * (_ ⊗ₜ[R] _) = _,
    rw algebra.tensor_product.tmul_mul_tmul,
    simp only [units.inv_mul],
    refl,
    }
end

noncomputable def units_tmul {R A B : Type*} [comm_semiring R] [ring A] [ring B]
  [algebra R A] [algebra R B] {x : A} {y : B} (hx : is_unit x) (hy : is_unit y) :
  units (A ⊗[R] B) :=
{ val := x ⊗ₜ[R] y,
  inv := ((is_unit.unit hx)⁻¹ : Aˣ) ⊗ₜ[R] ((is_unit.unit hy)⁻¹ : Bˣ),
  val_inv := sorry,
  inv_val := sorry }

lemma units_tmul_zpow {R A B : Type*} [comm_semiring R] [ring A] [ring B]
  [algebra R A] [algebra R B] (x : A) (y : B) (hx : is_unit x) (hy : is_unit y) (m : ℤ) :
  (((units_tmul hx hy) ^ m : (A ⊗[R] B)ˣ) : (A ⊗[R] B)) =
  ((is_unit.unit hx ^ m : Aˣ) : A) ⊗ₜ[R] ((is_unit.unit hy ^ m : Bˣ) : B) :=
begin
  rw ←tmul_zpow,
  congr,
  ext,
  refl,
end

end algebra.tensor_product
variables (R : Type u) [comm_ring R]

namespace laurent_polynomial

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

noncomputable def map_ring_hom {R S : Type*} [comm_semiring R]
  [comm_semiring S] (f : R →+* S) :
  R[T;T⁻¹] →+* S[T;T⁻¹] :=
@is_localization.map _ _ _ _ _ _ _ _ laurent_polynomial.is_localization _ _ _ _
  laurent_polynomial.is_localization (polynomial.map_ring_hom f) $
by simp only [submonoid.closure_singleton_le_iff_mem, submonoid.mem_comap,
  polynomial.coe_map_ring_hom, polynomial.map_X, submonoid.mem_closure_singleton_self]

lemma map_ring_hom_id (R : Type*) [comm_semiring R] :
  map_ring_hom (ring_hom.id R) = ring_hom.id _ :=
begin
  ext,
  all_goals
  { dsimp [laurent_polynomial.map_ring_hom],
    simp only [polynomial.map_ring_hom_id, is_localization.map_id] },
end

lemma map_ring_hom_comp {R S T : Type*} [comm_semiring R]
  [comm_semiring S] [comm_semiring T] (f : R →+* S) (g : S →+* T) :
  map_ring_hom (g.comp f) = (map_ring_hom g).comp (map_ring_hom f) :=
sorry

/-
-- again I don't think we need `R` commutative but I want to use `is_localization.lift`.
noncomputable def eval₂_ring_hom {R S : Type*}
  [comm_semiring R] [comm_semiring S] (f : R →+* S) (x : units S) :
  R[T;T⁻¹] →+* S :=
@is_localization.lift (polynomial R) _ _ _ _ _ _ _ laurent_polynomial.is_localization
(polynomial.eval₂_ring_hom f x) $
begin
  suffices : submonoid.closure {@polynomial.X R _} ≤ (is_unit.submonoid S).comap
    (polynomial.eval₂_ring_hom f x).to_monoid_hom,
  { intro y, exact this y.2},
  rw submonoid.closure_le,
  simpa only [ring_hom.to_monoid_hom_eq_coe, submonoid.coe_comap, ring_hom.coe_monoid_hom,
    polynomial.coe_eval₂_ring_hom, set.singleton_subset_iff, set.mem_preimage,
    polynomial.eval₂_X] using units.is_unit x,
end-/

noncomputable def eval₂_alg_hom (R : Type*) {S : Type*} [comm_semiring R] [ring S]
  [algebra R S] (x : S) (hx : is_unit x) :
  R[T;T⁻¹] →ₐ[R] S :=
add_monoid_algebra.lift _ _ _ ((units.coe_hom S).comp (zpowers_hom Sˣ $ is_unit.unit hx))

@[simp] lemma eval₂_alg_hom_single {R S : Type*} [comm_semiring R] [ring S] [algebra R S]
  {x : S} {hx : is_unit x} (n : ℤ) (r : R) :
  eval₂_alg_hom R x hx (finsupp.single n r) = r • (is_unit.unit hx ^ n : Sˣ) :=
begin
  rw [eval₂_alg_hom, add_monoid_algebra.lift_apply, finsupp.sum_single_index],
  { refl },
  { rw zero_smul },
end

open_locale tensor_product

lemma is_unit_T_tmul_T (R : Type*) [comm_ring R] (m n : ℤ) :
  is_unit (@T R _ m ⊗ₜ[R] @T R _ n) :=
⟨{ val := T m ⊗ₜ[R] T n,
  inv := T (- m) ⊗ₜ[R] T (- n),
  val_inv :=
  begin
    simpa only [algebra.tensor_product.tmul_mul_tmul, ←T_sub, ←T_add, add_neg_self],
  end,
  inv_val :=
  begin
    simpa only [algebra.tensor_product.tmul_mul_tmul, ←T_sub, ←T_add, neg_add_self],
  end }, rfl⟩

noncomputable def comul : R[T;T⁻¹] →ₐ[R] (R[T;T⁻¹] ⊗[R] R[T;T⁻¹]) :=
eval₂_alg_hom R _ (is_unit_T_tmul_T R 1 1)

noncomputable instance T_tmul_T_neg_invertible (m n : ℤ) :
  invertible (@T R _ m ⊗ₜ[R] @T R _ n) :=
{ inv_of := T (-m) ⊗ₜ[R] T (-n),
  inv_of_mul_self := by { simpa only [algebra.tensor_product.tmul_mul_tmul, ← T_add, add_left_neg,
    add_right_neg, T_zero], },
  mul_inv_of_self := by { simpa only [algebra.tensor_product.tmul_mul_tmul, ← T_add, add_left_neg,
    add_right_neg, T_zero], }, }

noncomputable instance T_neg_Tmul_T_invertible (m n : ℤ) :
  invertible (@T R _ (-m) ⊗ₜ[R] @T R _ (-n)) :=
@invertible_inv_of _ _ _ (@T R _ m ⊗ₜ[R] @T R _ n) _

lemma T_tmul_T_inv (m n : ℤ) : ⅟(@T R _ m ⊗ₜ[R] @T R _ n) = T (-m) ⊗ₜ[R] T (-n) := rfl
lemma T__Tmul_T_inv' (m n : ℤ) : ⅟(@T R _ (-m) ⊗ₜ[R] @T R _ (-n) ) = T m ⊗ₜ[R] T n :=
begin
  rw inv_of_eq_right_inv,{ simpa only [algebra.tensor_product.tmul_mul_tmul, ← T_add, add_left_neg,
    add_right_neg, T_zero], }
end

lemma comul_T_nat (m : ℕ) :
  comul R (T m) = T m ⊗ₜ[R] T m :=
begin
  show comul R (finsupp.single m (1 : R)) = _,
  simp only [comul, one_smul, eval₂_alg_hom_single, zpow_coe_nat, units.coe_pow, is_unit.unit_spec,
    algebra.tensor_product.tmul_pow, T_pow, mul_one, mul_neg],
end

lemma comul_T (m : ℤ) :
  comul R (T m) = T m ⊗ₜ[R] T m :=
begin
  refine int.induction_on m _ _ _,
  { show comul R (finsupp.single 0 (1 : R)) = _,
    simpa only [comul, eval₂_alg_hom_single, one_smul, zpow_zero, units.coe_one, T_zero, neg_zero]
     },
  { intros i hi,
    exact comul_T_nat _ _ },
  { intros i hi,
    rw ←neg_add',
    rw ←int.coe_nat_succ,
      rw ←T_tmul_T_inv,
  rw eq_comm,
  rw inv_of_eq_right_inv,
  rw ←comul_T_nat,
  rw ←map_mul (comul R),
  show comul R (T _ * T _) = _,
  rw ←T_add,
  rw add_right_neg,
  rw T_zero,
  rw map_one,
     }
end

noncomputable def counit : R[T;T⁻¹] →ₐ[R] R := eval₂_alg_hom R _ is_unit_one

lemma T_def (m : ℤ) : T m = finsupp.single m 1 := rfl
lemma counit_T (m : ℤ) :
  counit R (T m) = 1 :=
begin
  rw counit,
  rw T,
  rw eval₂_alg_hom_single,
  rw one_smul,
  simp only [units.coe_eq_one],
  rw ←one_zpow m,
  congr,
  ext,
  refl,
end

noncomputable def coinv : R[T;T⁻¹] →ₐ[R] R[T;T⁻¹] :=
eval₂_alg_hom R _ (is_unit_T (-1))

lemma coinv_T (m : ℤ) :
  coinv R (T m) = T (-m) :=
begin
  rw coinv,
  delta T,
  rw eval₂_alg_hom_single,
  rw one_smul,
  simp only [single_eq_C_mul_T, map_one, one_mul],
    refine m.induction_on _ _ _,
  { simp only [zpow_zero, units.coe_one, neg_zero, T_zero], },
  { intros i hi,
    rw ←int.coe_nat_succ,
    rw zpow_coe_nat,
    rw units.coe_pow,
    rw is_unit.unit_spec,
    rw T_pow,
    rw mul_neg_one, },
  { intros i hi,
    rw ←neg_add',
    rw ←int.coe_nat_succ,
    rw zpow_neg,
    rw units.inv_eq_of_mul_eq_one_left,
     rw zpow_coe_nat,
    rw units.coe_pow,
    rw is_unit.unit_spec,
    rw T_pow,
    rw neg_neg,
    rw mul_neg_one,
    rw ←T_add,
    rw add_neg_self,
    rw T_zero,
    }

end

variables {k : Type*} [comm_ring k] (m : ℤ)

noncomputable instance bialgebra : bialgebra R (laurent_polynomial R) :=
bialgebra.mk'.{u u u} R (comul R)
(counit R)
begin
  ext,
  simp only [linear_map.comp_apply, finsupp.lsingle_apply, single_eq_C_mul_T, map_one, one_mul,
    alg_hom.to_linear_map_apply, linear_equiv.coe_to_linear_map, comul_T, tensor_product.map_tmul,
    linear_map.id_apply, tensor_product.assoc_tmul],
end
begin
  ext,
    simp only [linear_map.comp_apply, finsupp.lsingle_apply, single_eq_C_mul_T, map_one, one_mul,
    alg_hom.to_linear_map_apply, linear_equiv.coe_to_linear_map, comul_T, tensor_product.map_tmul,
    linear_map.id_apply, tensor_product.rid_tmul, counit_T, one_smul],
end
begin
  ext,
    simp only [linear_map.comp_apply, finsupp.lsingle_apply, single_eq_C_mul_T, map_one, one_mul,
    alg_hom.to_linear_map_apply, linear_equiv.coe_to_linear_map, comul_T, tensor_product.map_tmul,
    linear_map.id_apply, tensor_product.lid_tmul, counit_T, one_smul],
end

noncomputable instance : hopf_algebra R (laurent_polynomial R) :=
hopf_algebra.of_alg_hom (coinv R)


end laurent_polynomial
