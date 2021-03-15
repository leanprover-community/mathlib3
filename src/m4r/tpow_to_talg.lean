import m4r.tpow algebra.punit_instances linear_algebra.direct_sum_module

universe u

section
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]
  (N : Type u) [add_comm_group N] [module R N]

open tpow
open_locale classical direct_sum

lemma map_sum_tmul {α : Type*} (s : multiset α) (m : α → M) (n : N) :
  ((multiset.map m s).sum ⊗ₜ[R] n) = (multiset.map (λ a, m a ⊗ₜ[R] n) s).sum :=
begin
  refine multiset.induction _ _ s,
  { rw [multiset.map_zero, multiset.map_zero, multiset.sum_zero,
      tensor_product.zero_tmul, multiset.sum_zero] },
  { intros a S h,
    rw [multiset.map_cons, multiset.map_cons, multiset.sum_cons,
        multiset.sum_cons, tensor_product.add_tmul, h] },
end

local attribute [semireducible] tensor_algebra

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
  left_inv := λ x,
    begin
      refine quot.induction_on x _,
      intro y,
      refine quot.induction_on y _,
      intro z,
      refine free_algebra.pre.rec_on z _ _ _ _,
      { intro z,
        erw [free_algebra.quot_mk_eq_ι, ring_quot.lift_alg_hom_mk_alg_hom_apply,
             free_algebra.lift_ι_apply],
        rw linear_map.zero_apply,
        simp only [ring_hom.map_zero],
        rw @punit.ext z 0,
        have := @tensor_algebra.rel.smul R _ punit _ _ (0 : R) (0 : punit),
        rw [zero_smul, ring_hom.map_zero, zero_mul] at this,
        rw quot.sound (ring_quot.rel.of this) },
      { intro z,
        congr,
        erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
        refl },
      { intros a b hb ha,
        dsimp only at hb ha ⊢,
        erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
        rw [talg_map_add R punit a b, ←ha, ←hb],
        erw [ring_quot.lift_alg_hom_mk_alg_hom_apply, ring_quot.lift_alg_hom_mk_alg_hom_apply],
        rw [falg_map_add, alg_hom.map_add, ring_hom.map_add],
        refl },
      { intros a b ha hb,
        dsimp only at hb ha ⊢,
        erw ring_quot.lift_alg_hom_mk_alg_hom_apply,
        rw [talg_map_mul R punit a b, ←ha, ←hb],
        erw [ring_quot.lift_alg_hom_mk_alg_hom_apply, ring_quot.lift_alg_hom_mk_alg_hom_apply],
        rw [falg_map_mul, alg_hom.map_mul, ring_hom.map_mul],
        refl },
    end,
  right_inv := λ x, by erw ring_quot.lift_alg_hom_mk_alg_hom_apply; refl,
  map_mul' := λ x y, by rw alg_hom.map_mul,
  map_add' := λ x y, by rw alg_hom.map_add,
  commutes' := λ r, by erw ring_quot.lift_alg_hom_mk_alg_hom_apply; refl  }

def talg_to_ring : tensor_algebra R M →ₐ tpow R M 0 :=
(trivial_talg R).to_alg_hom.comp $
  tensor_algebra.lift R (0 : M →ₗ[R] tensor_algebra R punit)

lemma talg_inj_zero :
  linear_map.ker (pow_to_alg R M 0) = ⊥ :=
begin
  apply linear_map.ker_eq_bot_of_injective,
  refine @function.left_inverse.injective _ _ (talg_to_ring R M) _ _,
  intro x,
  unfold pow_to_alg tpow.lift,
  rw [to_span_singleton_apply, alg_hom.map_smul, algebra.id.smul_eq_mul],
  convert mul_one x,
  rw [tensor_algebra.mk_default, alg_hom.map_one],
end

end

variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]
open tpow
open direct_sum

local attribute [semireducible] tensor_algebra tensor_algebra.lift
  free_algebra ring_quot.mk_ring_hom ring_quot.mk_alg_hom ring_quot free_algebra.lift
  tensor_algebra.ι free_algebra.ι

lemma tpow.induction_on (n : ℕ) {C : Π (n : ℕ), tpow R M n → Prop}
  (H : ∀ n (f : fin n → M), C n (tpow.mk R M n f))
  (Ht : ∀ n (x : tpow R M n) (y : M), C n x → C n.succ (tensor_product.mk R _ _ x y))
  (Hadd : ∀ n (x y : tpow R M n), C n x → C n y → C n (x + y))
  (Hsmul : ∀ n x (c : R), C n x → C n (c • x)) (x : tpow R M n) : C n x :=
begin
  induction n with n hn,
  have h := Hsmul 0 _ x (H 0 (default _)),
  convert h,
  rw algebra.id.smul_eq_mul,
  exact (mul_one _).symm,
  apply tensor_product.induction_on x,
  { convert Ht n 0 0 (hn 0),
    rw linear_map.map_zero },
  { intros y z,
    exact Ht n y z (hn y) },
  { intros y z,
    exact Hadd n.succ y z },
end

lemma exists_sum_of_tpow {n : ℕ} (x : tpow R M n) :
  ∃ (s : multiset (R × (fin n → M))),
    multiset.sum (s.map (λ i, i.1 • tpow.mk R M n i.2)) = x :=
begin
  refine tpow.induction_on _ _ _ _ _ _ _ x,
  { intros n f,
    use {(1, f)},
    rw multiset.map_singleton,
    erw multiset.sum_singleton,
    rw one_smul },
  { rintros n y z ⟨s, rfl⟩,
    use (multiset.map (λ t : R × (fin n → M), (t.1, fin.snoc t.2 z)) s),
    simp only [tensor_product.mk_apply, function.comp_app, multiset.map_map],
    rw map_sum_tmul,
    congr' 2,
    ext t,
    rw [←tensor_product.mk_apply, linear_map.map_smul₂],
    simp only [tensor_product.mk_apply, function.comp_app],
    rw mk_snoc,
    refl },
  { rintros n y z ⟨s, rfl⟩ ⟨t, rfl⟩,
    use s + t,
    rw [multiset.map_add, multiset.sum_add] },
  { rintros n y c ⟨s, rfl⟩,
    use (multiset.map (λ i : R × (fin n → M), (c • i.1, i.2)) s),
    rw [multiset.map_map, multiset.smul_sum, multiset.map_map],
    congr' 2,
    ext z,
    rw function.comp_app,
    erw smul_eq_mul,
    rw mul_smul },
end

variables (m n : ℕ)

@[reducible] def talg : Type u := direct_sum ℕ (tpow R M)

def lof_add {m n : ℕ} (f : fin m → M) :
  multilinear_map R (λ x : fin n, M) (talg R M) :=
{ to_fun := λ g, direct_sum.lof R ℕ (tpow R M) (m + n)
    (tpow.mk' R M (m + n) $ fin.append rfl f g),
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
    end}

lemma lof_add_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  lof_add R _ f g = direct_sum.lof R _ _ _ (tpow.mk' R _ _ $ fin.append rfl f g) := rfl

lemma lof_add_map {m n : ℕ} (f : fin m → M) (i : fin m) (x y : M) (z : fin n → M) :
  lof_add R M (function.update f i (x + y)) z = lof_add R M (function.update f i x) z
     + lof_add R M (function.update f i y) z :=
begin
  simp only [lof_add_apply],
  rw [←linear_map.map_add, fin.update_append, fin.update_append,
      fin.update_append, multilinear_map.map_add],
end

lemma lof_add_smul {m n : ℕ} (f : fin m → M) (i : fin m) (r : R) (x : M) (z : fin n → M) :
  lof_add R M (function.update f i (r • x)) z = r • lof_add R M (function.update f i x) z :=
begin
  simp only [lof_add_apply],
  rw [←linear_map.map_smul, fin.update_append,
      fin.update_append, multilinear_map.map_smul],
end

variables (f : fin m → M) (g : fin n → M) {N : Type u} [add_comm_group N] [module R N]

@[simp] lemma map_sum {N : Type u} [add_comm_group N] [module R N]
  (f : M →ₗ[R] N) {ι : Type u} (t : multiset ι) (g : ι → M) :
  f (t.map g).sum = (t.map $ λ i, f (g i)).sum :=
begin
  erw f.to_add_monoid_hom.map_multiset_sum,
  rw multiset.map_map,
  refl,
end

lemma map_sum' {N : Type u} [add_comm_group N] [module R N]
  (f : M →ₗ[R] N) {t : multiset M} :
  f t.sum = (t.map f).sum :=
begin
  erw f.to_add_monoid_hom.map_multiset_sum,
  refl,
end

lemma tpow.ext {n : ℕ} (f g : tpow R M n →ₗ[R] N)
  (H : ∀ x : fin n → M, f (tpow.mk' _ _ _ x) = g (tpow.mk' _ _ _ x)) :
  f = g :=
begin
  ext,
  rcases exists_sum_of_tpow _ _ x with ⟨s, rfl⟩,
  rw [map_sum, map_sum],
  congr,
  ext,
  rw [linear_map.map_smul, linear_map.map_smul],
  erw H,
  refl,
end

def mul : talg R M →ₗ[R] talg R M →ₗ[R] talg R M :=
direct_sum.to_module R ℕ (talg R M →ₗ[R] talg R M) $
λ m, tpow.lift R m _ $
  { to_fun := λ x, direct_sum.to_module R ℕ _ (λ n, tpow.lift R n _ (lof_add R M x)),
    map_add' := λ f i g j,
      begin
        refine linear_map.ext _,
        intro x,
        rw linear_map.add_apply,
        refine direct_sum.linduction_on R x _ _ _,
        { simp only [linear_map.map_zero, add_zero] },
        { intros t y,
         simp only [direct_sum.to_module_lof],
          rw ←linear_map.add_apply,
          congr,
          refine tpow.ext _ _ _ _ _,
          intro z,
          rw linear_map.add_apply,
          simp only [lift_mk_apply],
          rw lof_add_map },
        { intros y z hy hz,
          simp only [linear_map.map_add],
          rw [hy, hz],
          simp only [dfinsupp.add_apply],
          abel },
      end,
    map_smul' := λ f i r x,
      begin
        refine linear_map.ext _,
        intro y,
        rw linear_map.smul_apply,
        refine direct_sum.linduction_on R y _ _ _,
        { simp only [linear_map.map_zero, smul_zero] },
        { intros t z,
          simp only [to_module_lof],
          rw ←linear_map.smul_apply,
          congr,
          refine tpow.ext _ _ _ _ _,
          intro w,
          rw linear_map.smul_apply,
          simp only [lift_mk_apply],
          rw lof_add_smul },
        { intros a b ha hb,
          simp only [linear_map.map_add],
          rw [ha, hb, smul_add] },
      end }

instance talg.has_mul : has_mul (talg R M) :=
⟨λ x, mul R M x⟩

lemma mul_def {x y : talg R M} : mul R M x y = x * y := rfl

def talg_mk {n : ℕ} (f : fin n → M) : talg R M :=
direct_sum.lof R ℕ (tpow R M) n (tpow.mk' _ _ n f)

lemma talg_mk_def {n : ℕ} (f : fin n → M) :
  talg_mk R M f = direct_sum.lof R ℕ (tpow R M) n (tpow.mk' _ _ n f) := rfl

instance : has_one (talg R M) :=
⟨direct_sum.lof R _ _ 0 1⟩

lemma mul_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  talg_mk R M f * talg_mk R M g = talg_mk R M (fin.append rfl f g) :=
begin
  unfold talg_mk,
  show mul R M _ _ = _,
  unfold mul,
  ext,
  rw [to_module_lof, tpow.lift_mk_apply],
  erw [to_module_lof, tpow.lift_mk_apply],
  refl,
end

@[simp] lemma zero_eq_mk : talg_mk R M (λ i : fin 1, 0) = 0 :=
begin
  unfold talg_mk tpow.mk',
  show lof R ℕ (tpow R M) 1 (tpow.mk R M 1 (λ _, 0)) = 0,
  unfold tpow.mk,
  rw [linear_map.map_zero, linear_map.map_zero],
end

@[simp] lemma one_eq_mk : talg_mk R M (default (fin 0 → M)) = 1 :=
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

@[simp] lemma linear_map.map_sum₂ {P : Type u} [add_comm_group P] [module R P]
  (f : M →ₗ[R] N →ₗ[R] P) (s : multiset M) :
  f s.sum = (s.map f).sum :=
map_sum' _ _ _

variables {P : Type u} [add_comm_group P] [module R P]

lemma sum_apply' (s : multiset (M →ₗ[R] N)) (x : M) :
  s.sum x = (s.map (λ f : M →ₗ[R] N, f x)).sum :=
begin
   apply multiset.induction_on s,
   simp only [multiset.map_zero, linear_map.zero_apply, multiset.sum_zero],
   intros f t h,
   simp [h],
end

lemma sum_apply (s : multiset M) (f : M →ₗ[R] N →ₗ[R] P) (x : N) :
  (s.map f).sum x = (s.map (f.flip x)).sum :=
begin
  erw s.sum_hom f.to_add_monoid_hom,
  rw ←map_sum,
  simp only [multiset.map_id', linear_map.to_add_monoid_hom_coe, linear_map.flip_apply],
end

lemma talg.sum_mul (s : multiset (talg R M)) (x : talg R M) :
  s.sum * x = (s.map (λ y, y * x)).sum :=
begin
  show mul _ _ s.sum x = (s.map (λ y, mul _ _ y x)).sum,
  rw [linear_map.map_sum₂, sum_apply],
  congr,
end

lemma lof_apply' {ι : Type u} [decidable_eq ι] {M : ι → Type u} [Π i, add_comm_group (M i)] [Π i, module R (M i)]
  {i} {x} : direct_sum.lof R ι M i x = direct_sum.of M i x := rfl

lemma multiset.sum_mul {R : Type u} [ring R] {S : multiset R} {x : R} :
  S.sum * x = (S.map (λ y, y * x)).sum :=
(S.sum_hom ⟨(λ y, y * x), zero_mul _, λ _ _, add_mul _ _ x⟩).symm

lemma multiset.mul_sum {R : Type u} [ring R] {S : multiset R} {x : R} :
  x * S.sum = (S.map (λ y, x * y)).sum :=
(S.sum_hom ⟨(λ y, x * y), mul_zero _, mul_add _⟩).symm

lemma alg_hom.map_sum' {A : Type u} {B : Type u} [ring A] [ring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) (S : multiset A) :
  f S.sum = (S.map f).sum :=
(S.sum_hom f.to_ring_hom.to_add_monoid_hom).symm

lemma alg_hom.map_prod' {A : Type u} {B : Type u} [ring A] [ring B]
  [algebra R A] [algebra R B] (f : A →ₐ[R] B) (S : list A) :
  f S.prod = (S.map f).prod :=
(S.prod_hom f.to_ring_hom.to_monoid_hom).symm

lemma talg.smul_assoc (r : R) (x y : talg R M) :
  (r • x) * y = r • (x * y) :=
linear_map.map_smul₂ _ _ _ _

lemma aux (x : talg R M) (k : ℕ) (s : multiset (R × (fin k → M)))
(X : R × (fin k → M)) (j : ℕ) (t : multiset (R × (fin j → M)))
(Y : R × (fin j → M)) :
 x * (lof R ℕ (tpow R M) j (mk' R M j Y.snd)) *
      (lof R ℕ (tpow R M) k (mk R M k X.2)) =
    x * (talg_mk R M (fin.append rfl Y.2 X.2)) :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { simp only [talg.zero_mul] },
  { rintros n a,
    rcases exists_sum_of_tpow _ _ a with ⟨u, rfl⟩,
    simp only [←mul_def, map_sum, sum_apply', multiset.map_map],
    simp only [linear_map.smul_apply, function.comp_app, linear_map.map_smul],
    congr' 2,
    ext Z w,
    simp only [linear_map.smul_apply, function.comp_app],
    congr' 2,
    simp only [mul_def],
    erw [mul_apply, mul_apply, mul_apply],
    congr' 1,
  { rw add_assoc },
  { rw fin.heq_fun_iff (add_assoc _ _ _),
    intro I,
    exact fin.append_assoc _ _ _ rfl rfl rfl rfl _ }},
  { intros a b ha hb,
    simp only [talg.add_mul, ha, hb] },
end

lemma aux2 {x : talg R M}
  {k : ℕ} (s : multiset (R × (fin k → M))) (X : R × (fin k → M))
  {j : ℕ} (t : multiset (R × (fin j → M))) :
(λ (f : talg R M →ₗ[R] talg R M),
            f ((lof R ℕ (tpow R M) k) (mk R M k X.snd)))
∘ ((mul R M) ∘ (mul R M x)) ∘
  (λ (i : R × (fin j → M)),
     i.fst • (lof R ℕ (tpow R M) j) (mk R M j i.snd))
      =
  (mul R M x) ∘
         (λ (y : talg R M), y * (lof R ℕ (tpow R M) k) (mk R M k X.snd)) ∘
           λ (i : R × (fin j → M)),
             i.fst • (lof R ℕ (tpow R M) j) (mk R M j i.snd) :=
begin
  ext Y l,
  simp only [linear_map.smul_apply, function.comp_app, dfinsupp.smul_apply, linear_map.map_smul],
  rw [talg.smul_assoc, linear_map.map_smul, dfinsupp.smul_apply],
  congr' 2,
  erw mul_apply,
  simp only [mul_def],
  erw aux R M _ _ s _ j t _,
end

lemma talg.mul_assoc (x y z : talg R M) : x * y * z = x * (y * z) :=
begin
  refine direct_sum.linduction_on R z _ _ _,
  { simp only [talg.mul_zero] },
  { rintros k c,
   rcases exists_sum_of_tpow _ _ c with ⟨s, rfl⟩,
   rw map_sum,
    simp only [linear_map.map_smul],
    rw [talg.mul_sum, talg.mul_sum, multiset.map_map, multiset.map_map,
        talg.mul_sum],
    congr' 1,
    simp only [function.comp_app, multiset.map_map],
    congr' 1,
    ext X,
    simp only [function.comp_app, dfinsupp.smul_apply],
    refine direct_sum.linduction_on R y _ _ _,
    { simp only [talg.mul_zero, linear_map.map_zero,
      dfinsupp.zero_apply, linear_map.zero_apply, smul_zero] },
    { rintros j b,
      rcases exists_sum_of_tpow _ _ b with ⟨t, rfl⟩,
      rw map_sum R _ _ t (λ i : R × (fin j → M), i.1 • mk R M j i.2),
      simp only [linear_map.map_smul],
      rw [talg.mul_sum, linear_map.map_sum₂, multiset.map_map, multiset.map_map],
      congr' 2,
      rw [sum_apply', mul_def, mul_def, talg.sum_mul, talg.mul_sum],
      simp only [linear_map.smul_apply, function.comp_app, multiset.map_map, linear_map.map_smul],
      refine congr_arg _ _,
      erw aux2 R M s X t },
    { intros a b ha hb,
      rw [talg.mul_add, linear_map.map_add, linear_map.add_apply,
          linear_map.map_add, linear_map.add_apply, linear_map.map_add],
      simp only [add_apply],
      rw [ha, hb] }},
  { intros a b ha hb,
    rw [talg.mul_add, talg.mul_add, ha, hb, talg.mul_add] },
end

lemma talg.mul_one (x : talg R M) : x * 1 = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [←zero_eq_mk, ←one_eq_mk, mul_apply, fin.append_default'] },
  { intros i y,
    rcases exists_sum_of_tpow _ _ y with ⟨s, rfl⟩,
    rw [map_sum, talg.sum_mul, multiset.map_map],
    congr' 2, ext y j,
    simp only [function.comp_app, linear_map.map_smul],
    rw ←one_eq_mk,
    erw [talg.smul_assoc, mul_apply],
    congr,
    rw fin.append_default' },
  { intros x y hx hy,
    rw [talg.add_mul, hx, hy] },
end

lemma talg.one_mul (x : talg R M) : 1 * x = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [←zero_eq_mk, ←one_eq_mk, mul_apply],
    refl },
  { intros i y,
    rcases exists_sum_of_tpow _ _ y with ⟨s, rfl⟩,
    rw [map_sum, talg.mul_sum, multiset.map_map],
    congr' 2, ext y j,
    simp only [function.comp_app, linear_map.map_smul],
    rw ←one_eq_mk,
    congr,
    show talg_mk R M _ * talg_mk R M y.2 = _,
    rw mul_apply,
    congr,
    rw zero_add,
    rw fin.heq_fun_iff (zero_add _),
    intro k,
    rw fin.default_append,
    congr,
    rw zero_add },
  { intros x y hx hy,
    rw [talg.mul_add, hx, hy] },
end

instance talg.monoid : monoid (talg R M) :=
{ mul_assoc := talg.mul_assoc _ _,
  one := 1,
  one_mul := talg.one_mul _ _,
  mul_one := talg.mul_one _ _, ..talg.has_mul _ _ }

instance : ring (talg R M) :=
{ left_distrib := by exact talg.mul_add R M,
  right_distrib := by exact talg.add_mul R M,
  ..direct_sum.add_comm_group _, ..talg.monoid _ _ }

def talg.of_scalar : R →+* (talg R M) :=
{ to_fun := direct_sum.lof R ℕ (tpow R M) 0,
  map_one' := rfl,
  map_mul' := λ x y,
    begin
      rw ←mul_one (x * y),
      conv_rhs {rw ←mul_one x, rw ←mul_one y},
      erw [linear_map.map_smul, linear_map.map_smul, linear_map.map_smul],
      show _ = mul R M (x • talg_mk R M (default (fin 0 → M)))
        (y • talg_mk R M (default (fin 0 → M))),
      rw [linear_map.map_smul, linear_map.map_smul₂, mul_def,
          mul_apply, mul_comm, mul_smul],
      congr,
    end,
  map_zero' := linear_map.map_zero _,
  map_add' := linear_map.map_add _ }

lemma talg.of_scalar_apply {x : R} :
  talg.of_scalar R M x = direct_sum.lof R ℕ (tpow R M) 0 x := rfl

lemma talg.smul_one (r : R) : r • (1 : talg R M) = talg.of_scalar R M r :=
begin
  rw [talg.of_scalar_apply, ←one_eq_mk],
  unfold talg_mk,
  ext,
  cases i,
  convert mul_one r,
  rw [tpow.mk'_apply, ←linear_map.map_smul],
  simp only [dfinsupp.smul_apply],
  unfold tpow.mk,
  rw [algebra.id.smul_eq_mul, mul_one],
end

instance : algebra R (talg R M) :=
{ smul := (•),
  to_fun := talg.of_scalar R M,
  map_one' := ring_hom.map_one _,
  map_mul' := ring_hom.map_mul _,
  map_zero' := ring_hom.map_zero _,
  map_add' := ring_hom.map_add _,
  commutes' := λ r x,
    begin
      simp only,
      rw ←mul_one r,
      erw linear_map.map_smul,
      rw [←mul_def, ←mul_def, linear_map.map_smul,
          linear_map.map_smul, linear_map.smul_apply],
      show r • (talg.of_scalar R M 1 * x) = r • (x * talg.of_scalar R M 1),
      rw [ring_hom.map_one, mul_one, one_mul],
    end,
  smul_def' := λ r x,
    begin
      simp only,
      rw [←talg.smul_one R M r, ←mul_def, linear_map.map_smul₂, mul_def, one_mul],
    end }

variables {R M}

def alg_prod {A : Type u} [ring A] [algebra R A] (f : M →ₗ[R] A) (n : ℕ) :
  multilinear_map R (λ i : fin n, M) A :=
{ to_fun := λ g, (list.of_fn (f ∘ g)).prod,
  map_add' := λ g i x y,
    begin
      induction n with m hm,
      { exact fin.elim0 i },
      { rw [list.of_fn_succ, list.of_fn_succ, list.of_fn_succ,
            list.prod_cons, list.prod_cons, list.prod_cons],
        simp only [function.comp_app],
        rcases classical.em (i = 0) with ⟨rfl, hi⟩,
        { erw [function.update_same, function.update_same, function.update_same],
          rw [f.map_add, add_mul],
          congr,
          any_goals {ext l,
          rw [function.update_noteq, function.update_noteq],
          any_goals {intro hnot, apply nat.succ_ne_zero (l : ℕ),
          rw [fin.ext_iff, fin.coe_succ] at hnot,
          exact hnot }}},
        { rw [function.update_noteq (ne.symm h), function.update_noteq (ne.symm h),
              function.update_noteq (ne.symm h), ←mul_add],
          congr,
          have := hm (fin.tail g) (i.pred h),
          convert this,
          all_goals {ext z,
          simp only [function.comp_app],
          rw [←fin.tail_update_succ g (i.pred h), fin.succ_pred],
          congr }}},
    end,
  map_smul' := λ g i r x,
    begin
      induction n with m hm,
      { exact fin.elim0 i},
      { rw [list.of_fn_succ, list.of_fn_succ, list.prod_cons, list.prod_cons],
        simp only [function.comp_app],
        rcases classical.em (i = 0) with ⟨rfl, hi⟩,
        { erw [function.update_same, function.update_same],
          rw [f.map_smul, algebra.smul_mul_assoc],
          congr,
          any_goals
          {ext l, rw [function.update_noteq, function.update_noteq],
          any_goals {intro hnot, apply nat.succ_ne_zero (l : ℕ),
          rw [fin.ext_iff, fin.coe_succ] at hnot,
          exact hnot }}},
        { rw [function.update_noteq (ne.symm h), function.update_noteq (ne.symm h),
              ←algebra.mul_smul_comm],
          congr,
          have := hm (fin.tail g) (i.pred h),
          have hh := fin.tail_update_succ g (i.pred h),
          convert this,
          all_goals {ext z,
          simp only [function.comp_app],
          rw [←fin.tail_update_succ g (i.pred h), fin.succ_pred],
          congr }}},
    end }

lemma alg_prod_apply {A : Type u} [ring A] [algebra R A] (f : M →ₗ[R] A) (n : ℕ)
  (g : fin n → M) : alg_prod f n g = (list.of_fn (f ∘ g)).prod := rfl

variables (R M)
def talg.lift {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) : talg R M →ₐ[R] A :=
{ to_fun := direct_sum.to_module R ℕ A $ λ n, @tpow.lift R _ M _ _ n A _ _ (alg_prod f n),
  map_one' := by erw [←one_eq_mk, to_module_lof, tpow.lift_mk_apply]; convert list.prod_nil,
  map_mul' := λ x y,
    begin
      refine direct_sum.linduction_on R x _ _ _,
      { rw [zero_mul, linear_map.map_zero, zero_mul] },
      { intros i z,
        refine direct_sum.linduction_on R y _ _ _,
        { rw [mul_zero, linear_map.map_zero, mul_zero] },
        { intros j w,
          rw [to_module_lof, to_module_lof],
          rcases exists_sum_of_tpow R M z with ⟨s, rfl⟩,
          rw [map_sum, map_sum, talg.sum_mul, multiset.map_map, map_sum],
          rcases exists_sum_of_tpow R M w with ⟨t, rfl⟩,
          rw [map_sum, map_sum, multiset.sum_mul],
          congr' 1,
          rw multiset.map_map,
          congr' 1,
          ext z,
          simp only [function.comp_app, linear_map.map_smul, algebra.smul_mul_assoc],
          congr,
          erw [tpow.lift_mk_apply, multiset.mul_sum],
          rw [multiset.map_map, map_sum, multiset.mul_sum],
          congr' 1,
          rw multiset.map_map,
          congr' 1,
          ext w,
          simp only [algebra.mul_smul_comm, function.comp_app, linear_map.map_smul],
          congr,
          erw [tpow.lift_mk_apply, mul_apply, to_module_lof],
          rw tpow.lift_mk_apply,
          show list.prod _ = list.prod _ * list.prod _,
          rw [←list.prod_append, ←fin.append_comp, ←fin.of_fn_append] },
        { intros v w hv hw,
          simp only [to_module_lof, linear_map.map_add, mul_add] at * ,
          rw [hw, hv] }},
      { intros v w hv hw,
        simp only [to_module_lof, linear_map.map_add, add_mul] at *,
        rw [hw, hv] },
    end,
  map_zero' := linear_map.map_zero _,
  map_add' := linear_map.map_add _,
  commutes' := λ r,
    begin
      erw [to_module_lof, to_span_singleton_apply, alg_prod_apply, list.prod_nil],
      rw [algebra.smul_def'', mul_one],
    end }

def ι : M →ₗ[R] talg R M :=
(lof R ℕ (tpow R M) 1).comp (tensor_product.lid R M).symm.to_linear_map

variables {R M}

lemma ι_apply {x : M} : ι R M x = lof R ℕ (tpow R M) 1 (1 ⊗ₜ x) := rfl

lemma ι_eq_mk {x : M} : ι R M x = talg_mk R M (λ i : fin 1, x) :=
rfl

variables (R M)

lemma talg_mk_prod {i : fin n → M} :
  talg_mk R M i = alg_prod (ι R M) n i :=
begin
  induction n with n hn,
  { erw one_eq_mk,
    rw alg_prod_apply,
    simp only [list.of_fn_zero, list.prod_nil] },
  { rw [alg_prod_apply, fin.list.of_fn_succ', list.concat_eq_append, list.prod_append,
        list.prod_singleton],
    conv_rhs {rw ←fin.comp_init},
    rw [←alg_prod_apply, ←@hn (fin.init i), function.comp_app, ι_eq_mk, mul_apply],
    congr,
    rw fin.append_one,
    convert (fin.snoc_init_self i).symm,
    ext,
    simp only [fin.coe_last, fin.coe_nat_fin_succ] },
end

lemma talg.lift_ι_apply {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) {x : M} :
  talg.lift R M f (ι R M x) = f x :=
begin
  erw [to_module_lof, tpow.mk_one_lid_symm],
  rw [tpow.lift_mk_apply, alg_prod_apply],
  exact list.prod_singleton,
end

lemma hom_ext {A : Type u} [ring A] [algebra R A]
  (f g : talg R M →ₐ[R] A) (h : f.to_linear_map.comp (ι R M) = g.to_linear_map.comp (ι R M)) :
  f = g :=
begin
  ext,
  refine direct_sum.linduction_on R x _ _ _,
  { simp only [alg_hom.map_zero] },
  { intros i y,
    rcases exists_sum_of_tpow R M y with ⟨s, rfl⟩,
    simp only [map_sum, linear_map.map_smul, alg_hom.map_sum', multiset.map_map],
    congr' 2,
    ext X,
    simp only [alg_hom.map_smul, function.comp_app],
    congr' 1,
    show f (talg_mk R M _) = g (talg_mk R M _),
    erw talg_mk_prod,
    simp only [alg_prod_apply, alg_hom.map_prod', list.of_fn_eq_map, list.map_map],
    congr' 2,
    ext,
    rw linear_map.ext_iff at h,
    exact h _ },
  { intros X Y HX HY,
    simp only [alg_hom.map_add, HX, HY] },
end

def to_talg : tensor_algebra R M →ₐ[R] talg R M :=
tensor_algebra.lift R (ι R M)

lemma to_talg_mk {i : fin n → M} :
  to_talg R M (tensor_algebra.mk R M i) = talg_mk R M i :=
begin
  show to_talg R M (list.prod (list.map _ _)) = _,
  rw [alg_hom.map_prod', list.map_map],
  unfold to_talg,
  rw function.comp,
  have : (λ x : fin n, tensor_algebra.lift R (ι R M)
    (tensor_algebra.ι R (i x))) = ι R M ∘ i :=
  by funext; exact tensor_algebra.lift_ι_apply (ι R M) (i x),
  rw [this, talg_mk_prod],
  congr,
  exact list.of_fn_eq_map.symm,
end

theorem talg.right_inverse (x : talg R M) :
  to_talg R M (talg.lift R M (tensor_algebra.ι R) x) = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [alg_hom.map_zero, alg_hom.map_zero] },
  { intros i y,
    rcases exists_sum_of_tpow R M y with ⟨s, rfl⟩,
    rw map_sum,
    simp only [linear_map.map_smul],
    rw [alg_hom.map_sum', multiset.map_map, alg_hom.map_sum', multiset.map_map],
    congr,
    ext y j,
    simp only [alg_hom.map_smul, function.comp_app, dfinsupp.smul_apply],
    congr,
    erw [to_module_lof, tpow.lift_mk_apply],
    rw [alg_prod_apply, alg_hom.map_prod', list.map_of_fn],
    unfold to_talg,
    rcases y with ⟨y1, y2⟩,
    simp only [],
    clear s y1,
    induction i with i hi,
    { show _ = talg_mk R M (default (fin 0 → M)),
      simp only [list.of_fn_zero, list.prod_nil, one_eq_mk] },
    { rw list.of_fn_succ,
      have := hi (fin.tail y2),
      rw [fin.comp_tail, fin.comp_tail] at this,
      rw list.prod_cons,
      erw this,
      rw [function.comp_app, function.comp_app, tensor_algebra.lift_ι_apply, ι_eq_mk],
      erw mul_apply,
      congr,
      { rw add_comm },
      { rw fin.heq_fun_iff (add_comm _ _),
        intro j,
        rw [fin.one_append _ j, fin.cons_self_tail y2],
        refl }}},
  { intros y z hy hz,
    simp only [alg_hom.map_add, hy, hz] },
end

variables {R M}

local attribute [instance] free_algebra.pre.has_mul

@[elab_as_eliminator]
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
  { intro y,
    have h := H 1 (λ _, y),
    suffices : tensor_algebra.mk R M (λ x : fin 1, y) =
      quot.mk (ring_quot.rel (tensor_algebra.rel R M))
        (quot.mk (free_algebra.rel R M) (free_algebra.pre.of y)),
    by rwa this at h,
    show list.prod _ = _,
    erw list.map_singleton,
    rw list.prod_singleton,
    refl },
  { intro y,
    have h := Hsmul _ y (H 0 (default _)),
    suffices : y • tensor_algebra.mk R M (default (fin 0 → M)) =
      quot.mk (ring_quot.rel (tensor_algebra.rel R M)) (quot.mk (free_algebra.rel R M)
        (free_algebra.pre.of_scalar y)),
    by rwa this at h,
    show y • list.prod _ = _,
    erw list.map_nil,
    rw [list.prod_nil, ←algebra.algebra_map_eq_smul_one],
    refl },
  { intros y z hy hz,
    rw falg_map_add,
    exact Hadd _ _ hy hz },
  { intros y z hy hz,
    rw falg_map_mul,
    exact Hmul _ _ hy hz },
end

variables (R M)

theorem talg.left_inverse (x : tensor_algebra R M) :
  talg.lift R M (tensor_algebra.ι R) (to_talg R M x) = x :=
begin
  refine tensor_algebra.induction_on _ _ _ _ x,
  { intros n f,
    unfold to_talg,
    erw alg_hom.map_prod',
    rw list.map_map,
    erw alg_hom.map_prod',
    rw list.map_map,
    congr' 2,
    ext z,
    simp only [function.comp_app, tensor_algebra.lift_ι_apply],
    rw ι_eq_mk,
    erw to_module_lof,
    rw tpow.lift_mk_apply,
    show list.prod _ = _,
    simp only [list.repeat, mul_one, function.comp_const, list.prod_cons,
      list.prod_nil, list.of_fn_const] },
  { intros y z hy hz,
    simp only [alg_hom.map_add, hy, hz] },
  { intros x c hx, simp only [alg_hom.map_smul, hx] },
  { intros y z hy hz,
    simp only [alg_hom.map_mul, hy, hz] },
end

def talg_equiv : talg R M ≃ₐ[R] tensor_algebra R M :=
alg_equiv.of_alg_hom (talg.lift R M (tensor_algebra.ι R))
  (to_talg R M) (alg_hom.ext $ talg.left_inverse R M) (alg_hom.ext $ talg.right_inverse R M)
