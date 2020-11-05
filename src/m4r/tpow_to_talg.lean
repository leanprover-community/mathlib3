import m4r.tpow algebra.punit_instances m4r.direct_sum_semimodule

universe u
section
variables (R : Type u) [comm_semiring R] (M : Type u) [add_comm_monoid M] [semimodule R M]
  (N : Type u) [add_comm_monoid N] [semimodule R N]
open tpow
open_locale direct_sum

lemma map_sum_tmul {α : Type*} (s : multiset α) (m : α → M) (n : N) :
  ((multiset.map m s).sum ⊗ₜ[R] n) = (multiset.map (λ a, m a ⊗ₜ[R] n) s).sum :=
begin
  refine multiset.induction _ _ s,
  rw multiset.map_zero,
  rw multiset.map_zero,
  rw multiset.sum_zero,
  rw tensor_product.zero_tmul,
  rw multiset.sum_zero,
  intros a S h,
  rw multiset.map_cons,
  rw multiset.map_cons,
  rw multiset.sum_cons,
  rw multiset.sum_cons,
  rw tensor_product.add_tmul,
  rw h,
end

/-lemma tmul_map_sum (m : M) {α : Type*} (s : finset α) (n : α → N) :
  (m ⊗ₜ[R] (∑ a in s, n a)) = ∑ a in s, m ⊗ₜ[R] n a :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp, },
  { simp [finset.sum_insert has, tmul_add, ih], },
end-/

def pow_to_alg (n : ℕ) : (tpow R M n) →ₗ[R] (tensor_algebra R M) :=
tpow.lift R n (tensor_algebra R M) $ tensor_algebra.mk R M

@[simp] lemma tensor_algebra.mk_default :
  tensor_algebra.mk R M (default (fin 0 → M)) = 1 :=
list.prod_nil

local attribute [semireducible] tensor_algebra tensor_algebra.lift
  free_algebra ring_quot.mk_ring_hom ring_quot.mk_alg_hom ring_quot free_algebra.lift
  tensor_algebra.ι free_algebra.ι

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

end
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]
open tpow
open direct_sum2

local attribute [semireducible] tensor_algebra tensor_algebra.lift
  free_algebra ring_quot.mk_ring_hom ring_quot.mk_alg_hom ring_quot free_algebra.lift
  tensor_algebra.ι free_algebra.ι
/-
instance fd (S : Type u) [comm_semiring S] {P : Type*} {Q : Type*} [add_comm_group P]
  [add_comm_group Q] [semimodule R P] [semimodule R Q] :
  add_comm_group (tensor_product R P Q) :=
by apply_instance

instance tpow_acg : Π (n : ℕ), Σ (h : add_comm_group (tpow_aux R M n).1), @module R (tpow_aux R M n).1 _ h
| 0 := ⟨by unfold tpow_aux; apply_instance, by apply_instance⟩
| (n + 1) := ⟨by {unfold tpow_aux, squeeze_simp, exact @tensor_product.add_comm_group R _ (tpow_aux R M n).1 M (tpow_acg n).1 _ (tpow_acg n).2 _}, by apply_instance⟩

instance tpow_semimodule (R : Type u) [comm_semiring R] (M : Type u)
  [add_comm_monoid M] [semimodule R M] (n : ℕ) :
semimodule R (tpow_aux R M n).1 := (tpow_aux R M n).2.2

-/

lemma tpow.induction_on (n : ℕ) {C : Π (n : ℕ), tpow R M n → Prop}
  (H : ∀ n (f : fin n → M), C n (tpow.mk R M n f))
  (Ht : ∀ n (x : tpow R M n) (y : M), C n x → C n.succ (tensor_product.mk R _ _ x y))
  (Hadd : ∀ n (x y : tpow R M n), C n x → C n y → C n (x + y))
  (Hsmul : ∀ n x (c : R), C n x → C n (c • x)) (x : tpow R M n) : C n x :=
begin
  induction n with n hn,
  have h := Hsmul 0 _ x (H 0 (default _)),
  convert h,
  rw algebra.id.smul_eq_mul, exact (mul_one _).symm,
  apply tensor_product.induction_on x,
  convert Ht n 0 0 (hn 0),
  rw linear_map.map_zero,
  intros y z,
  exact Ht n y z (hn y),
  intros y z,
  exact Hadd n.succ y z,
end

lemma exists_sum_of_tpow {n : ℕ} (x : tpow R M n) :
  ∃ (s : multiset (fin n → M)), multiset.sum (s.map (tpow.mk R M n)) = x :=
begin
  refine tpow.induction_on _ _ _ _ _ _ _ x,
  intros n f,
  use {f},
  rw multiset.map_singleton,
  erw multiset.sum_singleton,
  rintros n y z ⟨s, h⟩,
  use multiset.map (λ f, fin.snoc f z) s,

  sorry, sorry, sorry
end

variables (m n : ℕ)

@[reducible] def talg : Type* := direct_sum ℕ (tpow R M)

def lof_add {m n : ℕ} (f : fin m → M) : multilinear_map R (λ x : fin n, M) (talg R M) :=
{ to_fun := λ g, direct_sum2.lof R ℕ (tpow R M) (m + n) (tpow.mk' R M (m + n) $ fin.append f g),
  map_add' := λ g i x y, sorry,
  map_smul' := sorry }

variables (f : fin m → M) (g : fin n → M)

def mul : talg R M →ₗ[R] talg R M →ₗ[R] talg R M :=
direct_sum2.to_semimodule R ℕ (talg R M →ₗ[R] talg R M) $
λ m, tpow.lift R m _ $
{ to_fun := λ x, direct_sum2.to_semimodule R ℕ _ $ λ n, tpow.lift R n _ $
    lof_add R M x,
  map_add' := sorry,
  map_smul' := sorry }

instance : has_mul (talg R M) :=
⟨λ x, mul R M x⟩

def talg_mk {n : ℕ} (f : fin n → M) : talg R M :=
direct_sum2.lof R ℕ (tpow R M) n (tpow.mk' _ _ n f)

instance : has_one (talg R M) :=
⟨direct_sum2.lof R _ _ 0 1⟩

lemma mul_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  talg_mk R M f * talg_mk R M g = talg_mk R M (fin.append f g) :=
begin
  unfold talg_mk,
  show mul R M _ _ = _,
  unfold mul,
  ext, rw to_semimodule_lof,
  rw tpow.lift_mk_apply,
  erw to_semimodule_lof,
  erw tpow.lift_mk_apply,
  refl,
end

lemma zero_eq_mk : talg_mk R M (λ i : fin 1, 0) = 0 :=
begin
  unfold talg_mk,
  unfold tpow.mk',
  show lof R ℕ (tpow R M) 1 (tpow.mk R M 1 (λ _, 0)) = 0,
  unfold tpow.mk,
  rw linear_map.map_zero,
  rw linear_map.map_zero,
end

lemma one_eq_mk : talg_mk R M (default (fin 0 → M)) = 1 :=
rfl

lemma of_tensor_eq_mul {n : ℕ} (x : tpow R M n) (y : M) :
  direct_sum2.of (tpow R M) n.succ (tensor_product.mk _ _ _ x y) =
    direct_sum2.of (tpow R M) n x * talg_mk _ _ (λ i : fin 1, y) :=
begin
  sorry -- hmmm .___.
end

lemma talg.mul_assoc (x y z : talg R M) : x * y * z = x * (y * z) :=
sorry

lemma talg.add_mul (x y z : talg R M) : (x + y) * z = x * z + y * z :=
begin
  sorry
end

lemma talg.mul_one (x : talg R M) : x * 1 = x :=
begin
  refine direct_sum2.induction_on x _ _ _,
  rw ←zero_eq_mk, rw ←one_eq_mk,
  rw mul_apply,
  rw fin.append_default,
  intros i y,
  refine tpow.induction_on R M _ _ _ _ _ y,
  intros n f,
  rw ←one_eq_mk,
  erw mul_apply _ _,
  rw fin.append_default,
  refl,
  intros n a b h,
  rw of_tensor_eq_mul _ _ a b,
  rw talg.mul_assoc,
  rw ←one_eq_mk,
  rw mul_apply,
  rw fin.append_default,
  intros n a b ha hb,
  show lof R _ (tpow R M) n (a + b) * 1 = lof R _ (tpow R M) n (a + b),
  rw linear_map.map_add,
  rw talg.add_mul,
  erw ha, erw hb, refl,
  intros n z c h,
  show lof R _ (tpow R M) n (c • z) * 1 = lof R _ (tpow R M) n (c • z),
  rw linear_map.map_smul,
  show c • of _ _ _ * 1 = c • of _ _ _,
  conv_rhs {rw ←h},
  sorry,
  intros a b ha hb,
  rw talg.add_mul, rw ha, rw hb,
end



variables {R M}

local attribute [instance] free_algebra.pre.has_mul

lemma tensor_algebra.induction_on {C : tensor_algebra R M → Prop}
  (H : ∀ (n : ℕ) (i : fin n → M), C $ tensor_algebra.mk R M i)
  (Hadd : ∀ x y, C x → C y → C (x + y))
  (Hsmul : ∀ x (c : R), C x → C (c • x))
  (Hmul : ∀ x y, C x → C y → C (x * y)) (x) : C x :=
begin
  refine quot.induction_on x _,
  intro a,
  refine quot.induction_on a _,
  intro z,
  refine free_algebra.pre.rec_on z _ _ _ _,
  intro y,
  have h := H 1 (λ _, y),
  suffices : tensor_algebra.mk R M (λ x : fin 1, y) =
    quot.mk (ring_quot.rel (tensor_algebra.rel R M))
      (quot.mk (free_algebra.rel R M) (free_algebra.pre.of y)),
  by rwa this at h,
  show list.prod _ = _,
  erw list.map_singleton,
  rw list.prod_singleton,
  refl,
  intro y,
  have h := Hsmul _ y (H 0 (default _)),
  suffices : y • tensor_algebra.mk R M (default (fin 0 → M)) =
    quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M)
      (free_algebra.pre.of_scalar y)),
  by rwa this at h,
  show y • list.prod _ = _,
  erw list.map_nil, rw list.prod_nil,
  rw ←algebra.algebra_map_eq_smul_one,
  refl,
  intros y z hy hz,
  rw falg_map_add,
  exact Hadd _ _ hy hz,
  intros y z hy hz,
  rw falg_map_mul,
  exact Hmul _ _ hy hz,
end

lemma mk_succ_eq {n : ℕ} (i : fin n → M) (x : M) :
  tpow.mk R M n.succ (fin.snoc i x) = tensor_product.mk R _ _ (tpow.mk R M n i) x :=
begin
  unfold tpow.mk, congr,
  ext y, unfold fin.snoc, split_ifs,
  simp only [fin.coe_eq_cast_succ, fin.cast_lt_cast_succ], refl,
  exfalso, apply h, simpa only [fin.coe_eq_cast_succ] using y.2,
  rw fin.snoc_mk_apply,
end

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
  refine tpow.induction_on _ _ n _ _ _ _ y,
  intros i f h,
  erw tpow.lift_mk_apply at h,
  rw multilinear_map.curry_right_apply at h,
  sorry, sorry, sorry, sorry, sorry,
end

