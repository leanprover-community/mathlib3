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
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_monoid M] [semimodule R M]
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
  ∃ (s : multiset (R × (fin n → M))), multiset.sum (s.map (λ i, i.1 • tpow.mk R M n i.2)) = x :=
begin
  refine tpow.induction_on _ _ _ _ _ _ _ x,
  intros n f,
  use {(1, f)},
  rw multiset.map_singleton,
  erw multiset.sum_singleton,
  rw one_smul,
  rintros n y z ⟨s, rfl⟩,
  use (multiset.map (λ t : R × (fin n → M), (t.1, fin.snoc t.2 z)) s),
  simp only [tensor_product.mk_apply, function.comp_app, multiset.map_map],
  rw map_sum_tmul,
  congr' 2,
  ext t,
  rw ←tensor_product.mk_apply,
  rw linear_map.map_smul₂,
  simp only [tensor_product.mk_apply, function.comp_app],
  rw mk_snoc, refl,
  rintros n y z ⟨s, rfl⟩ ⟨t, rfl⟩,
  use s + t,
  rw multiset.map_add,
  rw multiset.sum_add,
  rintros n y c ⟨s, rfl⟩,
  use (multiset.map (λ i : R × (fin n → M), (c • i.1, i.2)) s),
  rw multiset.map_map,
  rw multiset.smul_sum,
  rw multiset.map_map,
  congr' 2,
  ext z,
  rw function.comp_app,
  erw smul_eq_mul,
  rw mul_smul,
end

variables (m n : ℕ)

@[reducible] def talg : Type* := direct_sum ℕ (tpow R M)

def lof_add {m n : ℕ} (f : fin m → M) : multilinear_map R (λ x : fin n, M) (talg R M) :=
{ to_fun := λ g, direct_sum2.lof R ℕ (tpow R M) (m + n) (tpow.mk' R M (m + n) $ fin.append f g),
  map_add' := λ g i x y,
    begin
      rw ←linear_map.map_add,
      congr,
      simp only [fin.append_update],
      rw multilinear_map.map_add,
    end,
  map_smul' := λ g i r x,
    begin
      rw ←linear_map.map_smul,
      congr,
      simp only [fin.append_update],
      rw multilinear_map.map_smul,
    end
     }

lemma lof_add_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  lof_add R _ f g = direct_sum2.lof R _ _ _ (tpow.mk' R _ _ $ fin.append f g) := rfl

lemma lof_add_map {m n : ℕ} (f : fin m → M) (i : fin m) (x y : M) (z : fin n → M) :
  lof_add R M (function.update f i (x + y)) z = lof_add R M (function.update f i x) z
     + lof_add R M (function.update f i y) z :=
begin
  simp only [lof_add_apply],
  ext t,
  rcases classical.em (t = m + n) with ⟨rfl, ht⟩,
  rw dfinsupp.add_apply,
  erw [dfinsupp.single_eq_same, dfinsupp.single_eq_same, dfinsupp.single_eq_same],
  induction n with j hj,
  induction m with k hk,
  exact fin.elim0 i,
  show tpow.mk R M k.succ _ = tpow.mk R M k.succ _ + tpow.mk R M k.succ _,
  unfold tpow.mk,
  have := hk (fin.init f),
  sorry, sorry, sorry,
end

lemma lof_add_smul {m n : ℕ} (f : fin m → M) (i : fin m) (r : R) (x : M) (z : fin n → M) :
  lof_add R M (function.update f i (r • x)) z = r • lof_add R M (function.update f i x) z :=
begin
  sorry
end

variables (f : fin m → M) (g : fin n → M) {N : Type*} [add_comm_monoid N] [semimodule R N]


@[simp] lemma map_sum {N : Type*} [add_comm_monoid N] [semimodule R N]
  (f : M →ₗ[R] N) {ι : Type*} {t : multiset ι} {g : ι → M} :
  f (t.map g).sum = (t.map $ λ i, f (g i)).sum :=
begin
  erw f.to_add_monoid_hom.map_multiset_sum,
  rw multiset.map_map,
  refl,
end

lemma map_sum' {N : Type*} [add_comm_monoid N] [semimodule R N]
  (f : M →ₗ[R] N) {t : multiset M} :
  f t.sum = (t.map f).sum :=
begin
  erw f.to_add_monoid_hom.map_multiset_sum,
  refl,
end


lemma tpow.ext {n : ℕ} (f g : tpow R M n →ₗ[R] N) (H : ∀ x : fin n → M, f (tpow.mk' _ _ _ x) = g (tpow.mk' _ _ _ x)) :
  f = g :=
begin
  ext,
  rcases exists_sum_of_tpow _ _ x with ⟨s, rfl⟩,
  rw map_sum,
  rw map_sum,
  congr,
  ext,
  rw linear_map.map_smul,
  rw linear_map.map_smul,
  erw H,
  refl,
end

def mul : talg R M →ₗ[R] talg R M →ₗ[R] talg R M :=
direct_sum2.to_semimodule R ℕ (talg R M →ₗ[R] talg R M) $
λ m, tpow.lift R m _ $
  { to_fun := λ x, direct_sum2.to_semimodule R ℕ _ (λ n, tpow.lift R n _ (lof_add R M x)),
    map_add' := sorry,/-λ f i g j, by {
      ext x k,
      rw linear_map.add_apply,
      refine direct_sum2.induction_on x _ _ _,
      simp only [linear_map.map_zero, add_zero],
      intros t y,
      rw dfinsupp.add_apply,
      show direct_sum2.to_semimodule R ℕ (talg R M) _ (direct_sum2.lof R ℕ (tpow R M) _ y) k =
      direct_sum2.to_semimodule R ℕ (talg R M) _ (direct_sum2.lof R ℕ (tpow R M) _ y) k +
      direct_sum2.to_semimodule R ℕ (talg R M) _ (direct_sum2.lof R ℕ (tpow R M) _ y) k,
      simp only [direct_sum2.to_semimodule_lof],
      erw ←dfinsupp.add_apply,
      rw ←linear_map.add_apply,
      congr,
      refine tpow.ext _ _ _ _ _,
      intro z,
      rw linear_map.add_apply,
      simp only [lift_mk_apply],
      rw lof_add_map,
      intros y z hy hz,
      simp only [linear_map.map_add],
      simp only [dfinsupp.add_apply],
      rw hy, rw hz,
      simp only [dfinsupp.add_apply],
      abel, },-/
    map_smul' := λ f i r x, by
      {sorry/-ext y k,
      rw linear_map.smul_apply,
      refine direct_sum2.induction_on y _ _ _,
      simp only [linear_map.map_zero, smul_zero],
      intros t z,
      rw dfinsupp.smul_apply,
      show direct_sum2.to_semimodule R ℕ (talg R M) _ (direct_sum2.lof R ℕ (tpow R M) _ z) k =
          r • direct_sum2.to_semimodule R ℕ (talg R M) _ (direct_sum2.lof R ℕ (tpow R M) _ z) k,
      simp only [direct_sum2.to_semimodule_lof],
      erw ←dfinsupp.smul_apply,
      rw ←linear_map.smul_apply,
      congr,
      refine tpow.ext _ _ _ _ _,
      intro w,
      rw linear_map.smul_apply,
      simp only [lift_mk_apply],
      rw lof_add_smul,
      intros a b ha hb,
      simp only [linear_map.map_add],
      simp only [dfinsupp.add_apply],
      rw ha, rw hb,
      rw smul_add, simp only [dfinsupp.smul_apply, dfinsupp.add_apply],-/
      } }

instance talg.has_mul : has_mul (talg R M) :=
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

lemma talg.mul_zero (x : talg R M) : x * 0 = 0 :=
linear_map.map_zero _

lemma talg.zero_mul (x : talg R M) : 0 * x = 0 :=
linear_map.map_zero₂ _ _

lemma talg.mul_add (x y z : talg R M) : x * (y + z) = x * y + x * z :=
linear_map.map_add _ _ _

lemma talg.add_mul (x y z : talg R M) : (x + y) * z = x * z + y * z :=
linear_map.map_add₂ _ _ _ _

lemma talg.mul_sum (s : multiset (talg R M)) (x : talg R M) :
  x * s.sum = (s.map (mul _ _ x)).sum :=
map_sum' _ _ _

lemma linear_map.map_sum₂ {P : Type*} [add_comm_monoid P] [semimodule R P]
  (f : M →ₗ[R] N →ₗ[R] P) (s : multiset M) :
  f s.sum = (s.map f).sum :=
map_sum' _ _ _

lemma talg.sum_mul (s : multiset (talg R M)) (x : talg R M) :
  s.sum * x = (s.map (λ y, y * x)).sum :=
begin
  show mul _ _ s.sum x = (s.map (λ y, mul _ _ y x)).sum,
  rw linear_map.map_sum₂,
  sorry,
end


lemma talg.mul_assoc (x y z : talg R M) : x * y * z = x * (y * z) :=
begin
  show mul _ _ (mul _ _ x y) z = mul _ _ x (mul _ _ y z),
  sorry,
end

lemma talg.smul_assoc (r : R) (x y : talg R M) :
  (r • x) * y = r • (x * y) :=
linear_map.map_smul₂ _ _ _ _

lemma talg.mul_one (x : talg R M) : x * 1 = x :=
begin
  refine direct_sum2.induction_on x _ _ _,
  rw ←zero_eq_mk, rw ←one_eq_mk,
  rw mul_apply,
  rw fin.append_default,
  intros i y,
  show direct_sum2.lof R ℕ (tpow R M) _ _ * 1 = direct_sum2.lof R ℕ (tpow R M) _ _,
  rcases exists_sum_of_tpow _ _ y with ⟨s, rfl⟩,
  rw map_sum,
  rw talg.sum_mul,
  rw multiset.map_map,
  congr' 2, ext y j,
  simp only [function.comp_app, dfinsupp.smul_apply, map_smul_eq_smul_map],
  rw ←one_eq_mk,
  rw talg.smul_assoc,
  erw mul_apply,
  refl,
  intros x y hx hy,
  rw talg.add_mul,
  rw hx, rw hy,
end

lemma talg.one_mul (x : talg R M) : 1 * x = x :=
begin
  refine direct_sum2.induction_on x _ _ _,
  rw ←zero_eq_mk, rw ←one_eq_mk,
  rw mul_apply,
  refl,
  intros i y,
  show 1 * direct_sum2.lof R ℕ (tpow R M) _ _ = direct_sum2.lof R ℕ (tpow R M) _ _,
  rcases exists_sum_of_tpow _ _ y with ⟨s, rfl⟩,
  rw map_sum,
  rw talg.mul_sum,
  rw multiset.map_map,
  congr' 2, ext y j,
  simp only [function.comp_app, dfinsupp.smul_apply, map_smul_eq_smul_map],
  rw ←one_eq_mk,
  congr,
  show talg_mk R M _ * talg_mk R M y.2 = _,
  rw mul_apply,
  sorry, --annoying fin stuff
  intros x y hx hy,
  rw talg.mul_add,
  rw hx, rw hy,
end

instance talg.monoid : monoid (talg R M) :=
{ mul_assoc := talg.mul_assoc _ _,
  one := 1,
  one_mul := talg.one_mul _ _,
  mul_one := talg.mul_one _ _, ..talg.has_mul _ _ }

instance : semiring (talg R M) :=
{ zero_mul := talg.zero_mul _ _,
  mul_zero := talg.mul_zero _ _,
  left_distrib := talg.mul_add R M,
  right_distrib := talg.add_mul R M, ..direct_sum2.add_comm_monoid, ..talg.monoid _ _ }




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

