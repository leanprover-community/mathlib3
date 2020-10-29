import m4r.tpow algebra.punit_instances

universe u
variables (R : Type u) [comm_semiring R] (M : Type u) [add_comm_monoid M] [semimodule R M]
open tpow

def pow_to_alg (n : ℕ) : (tpow R M n) →ₗ[R] (tensor_algebra R M) :=
tpow.lift R n (tensor_algebra R M) $ tensor_algebra.mk R M

@[simp] lemma tensor_algebra.mk_default :
  tensor_algebra.mk R M (default (fin 0 → M)) = 1 :=
list.prod_nil

local attribute [semireducible] tensor_algebra tensor_algebra.lift
  free_algebra ring_quot.mk_ring_hom ring_quot.mk_alg_hom ring_quot free_algebra.lift

lemma free_algebra_map_apply {x : R} :
  algebra_map R (free_algebra R M) x =
  quot.mk (free_algebra.rel R M) (free_algebra.pre.of_scalar x) :=
rfl

lemma tensor_algebra_map_apply {x : R} :
  algebra_map R (tensor_algebra R M) x
  = (quot.mk (ring_quot.rel $ tensor_algebra.rel R M)
      (algebra_map R (free_algebra R M) x) : tensor_algebra R M) :=
rfl

lemma talg_map_add (x y : free_algebra.pre R M) :
  quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M) (x.add y))
  = (quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M) x)
    + quot.mk (ring_quot.rel (tensor_algebra.rel R M))
      (quot.mk (free_algebra.rel R M) y) : tensor_algebra R M) :=
rfl

lemma falg_map_add (x y : free_algebra.pre R M) :
  quot.mk (free_algebra.rel R M) (x.add y)
  = (quot.mk (free_algebra.rel R M) x
    + quot.mk (free_algebra.rel R M) y : free_algebra R M) :=
rfl

lemma talg_map_mul (x y : free_algebra.pre R M) :
  quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M) (x.mul y))
  = (quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M) x)
  * quot.mk (ring_quot.rel (tensor_algebra.rel R M))
    (quot.mk (free_algebra.rel R M) y) : tensor_algebra R M) :=
rfl

lemma falg_map_mul (x y : free_algebra.pre R M) :
  quot.mk (free_algebra.rel R M) (x.mul y)
  = (quot.mk (free_algebra.rel R M) x
    * quot.mk (free_algebra.rel R M) y : free_algebra R M) :=
rfl

def trivial_talg : tensor_algebra R punit ≃ₐ[R] R :=
{ to_fun := tensor_algebra.lift R 0,
  inv_fun := λ x, quot.mk (ring_quot.rel $ tensor_algebra.rel R punit)
    (algebra_map R (free_algebra R punit) x),
  left_inv := λ x, by {refine quot.induction_on x _, intro y,
    refine quot.induction_on y _, intro z,
    refine free_algebra.pre.rec_on z _ _ _ _,
    intro z,
    erw free_algebra.quot_mk_eq_ι,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    erw free_algebra.lift_ι_apply,
    rw linear_map.zero_apply,
    simp only [ring_hom.map_zero],
    rw @punit.ext z 0,
    have := @tensor_algebra.rel.smul R _ punit _ _ (0 : R) (0 : punit),
    rw zero_smul at this,
    rw ring_hom.map_zero at this,
    rw zero_mul at this,
    rw quot.sound (ring_quot.rel.of this),
    intro z,
    congr,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply, refl,
    intros a b hb ha,
    dsimp only at hb ha ⊢,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    rw talg_map_add R punit a b,
    rw ←ha, rw ←hb,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    rw falg_map_add,
    rw alg_hom.map_add,
    rw ring_hom.map_add,
    refl,
    intros a b ha hb,
    dsimp only at hb ha ⊢,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    rw talg_map_mul R punit a b,
    rw ←ha, rw ←hb,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
    rw falg_map_mul,
    rw alg_hom.map_mul,
    rw ring_hom.map_mul,
    refl,
 },
  right_inv := λ x, by {erw ring_quot.lift_alg_hom_mk_alg_hom_apply, refl,},
  map_mul' :=
    begin
      intros x y,
      rw alg_hom.map_mul,
    end,
  map_add' :=
    begin
      intros x y,
      rw alg_hom.map_add,
    end,
  commutes' := λ r, by {erw ring_quot.lift_alg_hom_mk_alg_hom_apply, refl,}  }

def talg_to_ring : tensor_algebra R M →ₐ tpow R M 0 :=
(trivial_talg R).to_alg_hom.comp $
  tensor_algebra.lift R (0 : M →ₗ[R] tensor_algebra R punit)

lemma talg_inj_zero :
  linear_map.ker (pow_to_alg R M 0) = ⊥ :=
begin
  apply linear_map.ker_eq_bot_of_injective,
  refine @function.left_inverse.injective _ _ (talg_to_ring R M) _ _,
  intro x,
  unfold pow_to_alg, unfold tpow.lift,
  rw to_span_singleton_apply,
  rw alg_hom.map_smul,
  rw algebra.id.smul_eq_mul, convert mul_one x,
  rw tensor_algebra.mk_default,
  rw alg_hom.map_one,
end

variables {R M}

lemma tensor_algebra.induction_on {C : tensor_algebra R M → Prop}
  (H : ∀ (n : ℕ) (i : fin n → M), C $ tensor_algebra.mk R M i)
  (Hadd : ∀ x y, C x → C y → C (x + y)) (x) : C x :=
begin
  refine quot.induction_on x _,
  intro a,
  refine quot.induction_on a _,
  rintro (y | y | ⟨y, z⟩ | ⟨y, z⟩);
  sorry
end

lemma tpow.induction_on (n : ℕ) {C : tpow R M n → Prop}
  (H : ∀ (i : fin n → M), C $ tpow.mk R M n i)
  (H : ∀ x y, C x → C y → C (x + y)) (x) : C x :=
sorry

theorem inj_of_pow_to_alg (n : ℕ) : (pow_to_alg R M n).ker = ⊥ :=
begin
  induction n with n hn,
    exact talg_inj_zero R M,
  apply linear_map.ker_eq_bot'.2,
  intros x h,
  unfold pow_to_alg at h,
  unfold tpow.lift at h,
  revert h,
  refine tensor_product.induction_on x _ _ _,
  tauto,
  intros y z h,
  rw tensor_product.lift.tmul at h,
  revert h,
  refine tpow.induction_on n _ _ y,
  intros i h,
  erw tpow.lift_mk_apply at h,
  rw multilinear_map.curry_right_apply at h,
  sorry, sorry, sorry,
end

