import m4r.tensor_power algebra.punit_instances linear_algebra.direct_sum_module

universe u

section
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]
  (N : Type u) [add_comm_group N] [module R N]

open tensor_power
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

def pow_to_alg (n : ℕ) : (tensor_power R M n) →ₗ[R] (tensor_algebra R M) :=
tensor_power.lift R n (tensor_algebra R M) $ tensor_algebra.mk R M

end

variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]
open tensor_power
open direct_sum

lemma tensor_power.induction_on (n : ℕ) {C : Π (n : ℕ), tensor_power R M n → Prop}
  (H : ∀ n (f : fin n → M), C n (tensor_power.mk R M n f))
  (Ht : ∀ n (x : tensor_power R M n) (y : M), C n x → C n.succ (tensor_product.mk R _ _ x y))
  (Hadd : ∀ n (x y : tensor_power R M n), C n x → C n y → C n (x + y))
  (Hsmul : ∀ n x (c : R), C n x → C n (c • x)) (x : tensor_power R M n) : C n x :=
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

lemma exists_sum_of_tensor_power {n : ℕ} (x : tensor_power R M n) :
  ∃ (s : multiset (R × (fin n → M))),
    multiset.sum (s.map (λ i, i.1 • tensor_power.mk R M n i.2)) = x :=
begin
  refine tensor_power.induction_on _ _ _ _ _ _ _ x,
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

@[reducible] def tensor_algebra2 : Type u := direct_sum ℕ (tensor_power R M)

def mul_aux {m n : ℕ} (f : fin m → M) :
  multilinear_map R (λ x : fin n, M) (tensor_algebra2 R M) :=
{ to_fun := λ g, direct_sum.lof R ℕ (tensor_power R M) (m + n)
    (tensor_power.mk' R M (m + n) $ fin.append rfl f g),
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

lemma mul_aux_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  mul_aux R _ f g = direct_sum.lof R _ _ _ (tensor_power.mk' R _ _ $ fin.append rfl f g) := rfl

lemma mul_aux_add {m n : ℕ} (f : fin m → M) (i : fin m) (x y : M) (z : fin n → M) :
  mul_aux R M (function.update f i (x + y)) z = mul_aux R M (function.update f i x) z
     + mul_aux R M (function.update f i y) z :=
begin
  simp only [mul_aux_apply],
  rw [←linear_map.map_add, fin.update_append, fin.update_append,
      fin.update_append, multilinear_map.map_add],
end

lemma mul_aux_smul {m n : ℕ} (f : fin m → M) (i : fin m) (r : R) (x : M) (z : fin n → M) :
  mul_aux R M (function.update f i (r • x)) z = r • mul_aux R M (function.update f i x) z :=
begin
  simp only [mul_aux_apply],
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

lemma tensor_power.ext {n : ℕ} (f g : tensor_power R M n →ₗ[R] N)
  (H : ∀ x : fin n → M, f (tensor_power.mk' _ _ _ x) = g (tensor_power.mk' _ _ _ x)) :
  f = g :=
begin
  ext,
  rcases exists_sum_of_tensor_power _ _ x with ⟨s, rfl⟩,
  rw [map_sum, map_sum],
  congr,
  ext,
  rw [linear_map.map_smul, linear_map.map_smul],
  erw H,
  refl,
end

def mul : tensor_algebra2 R M →ₗ[R] tensor_algebra2 R M →ₗ[R] tensor_algebra2 R M :=
direct_sum.to_module R ℕ (tensor_algebra2 R M →ₗ[R] tensor_algebra2 R M) $
λ m, tensor_power.lift R m _ $
  { to_fun := λ x, direct_sum.to_module R ℕ _ (λ n, tensor_power.lift R n _ (mul_aux R M x)),
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
          refine tensor_power.ext _ _ _ _ _,
          intro z,
          rw linear_map.add_apply,
          simp only [lift_mk_apply],
          rw mul_aux_add },
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
          refine tensor_power.ext _ _ _ _ _,
          intro w,
          rw linear_map.smul_apply,
          simp only [lift_mk_apply],
          rw mul_aux_smul },
        { intros a b ha hb,
          simp only [linear_map.map_add],
          rw [ha, hb, smul_add] },
      end }

instance tensor_algebra2.has_mul : has_mul (tensor_algebra2 R M) :=
⟨λ x, mul R M x⟩

lemma mul_def {x y : tensor_algebra2 R M} : mul R M x y = x * y := rfl

def tensor_algebra2_mk {n : ℕ} (f : fin n → M) : tensor_algebra2 R M :=
direct_sum.lof R ℕ (tensor_power R M) n (tensor_power.mk' _ _ n f)

lemma tensor_algebra2_mk_def {n : ℕ} (f : fin n → M) :
  tensor_algebra2_mk R M f = direct_sum.lof R ℕ (tensor_power R M) n (tensor_power.mk' _ _ n f) := rfl

instance : has_one (tensor_algebra2 R M) :=
⟨direct_sum.lof R _ _ 0 1⟩

lemma mul_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  tensor_algebra2_mk R M f * tensor_algebra2_mk R M g = tensor_algebra2_mk R M (fin.append rfl f g) :=
begin
  unfold tensor_algebra2_mk,
  show mul R M _ _ = _,
  unfold mul,
  ext,
  rw [to_module_lof, tensor_power.lift_mk_apply],
  erw [to_module_lof, tensor_power.lift_mk_apply],
  refl,
end

@[simp] lemma zero_eq_mk : tensor_algebra2_mk R M (λ i : fin 1, 0) = 0 :=
begin
  unfold tensor_algebra2_mk tensor_power.mk',
  show lof R ℕ (tensor_power R M) 1 (tensor_power.mk R M 1 (λ _, 0)) = 0,
  unfold tensor_power.mk,
  rw [tensor_product.tmul_zero, linear_map.map_zero],
end

@[simp] lemma one_eq_mk : tensor_algebra2_mk R M (default (fin 0 → M)) = 1 :=
rfl

lemma tensor_algebra2.mul_zero (x : tensor_algebra2 R M) : x * 0 = 0 :=
linear_map.map_zero _

lemma tensor_algebra2.zero_mul (x : tensor_algebra2 R M) : 0 * x = 0 :=
linear_map.map_zero₂ _ _

lemma tensor_algebra2.mul_add (x y z : tensor_algebra2 R M) : x * (y + z) = x * y + x * z :=
linear_map.map_add _ _ _

lemma tensor_algebra2.add_mul (x y z : tensor_algebra2 R M) : (x + y) * z = x * z + y * z :=
linear_map.map_add₂ _ _ _ _

lemma tensor_algebra2.mul_sum (s : multiset (tensor_algebra2 R M)) (x : tensor_algebra2 R M) :
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

lemma tensor_algebra2.sum_mul (s : multiset (tensor_algebra2 R M)) (x : tensor_algebra2 R M) :
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

lemma tensor_algebra2.smul_assoc (r : R) (x y : tensor_algebra2 R M) :
  (r • x) * y = r • (x * y) :=
linear_map.map_smul₂ _ _ _ _

lemma mul_assoc_aux (x : tensor_algebra2 R M) (k : ℕ) (s : multiset (R × (fin k → M)))
(X : R × (fin k → M)) (j : ℕ) (t : multiset (R × (fin j → M)))
(Y : R × (fin j → M)) :
 x * (lof R ℕ (tensor_power R M) j (mk' R M j Y.snd)) *
      (lof R ℕ (tensor_power R M) k (mk R M k X.2)) =
    x * (tensor_algebra2_mk R M (fin.append rfl Y.2 X.2)) :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { simp only [tensor_algebra2.zero_mul]},
  { rintros n a,
    rcases exists_sum_of_tensor_power _ _ a with ⟨u, rfl⟩,
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
    simp only [tensor_algebra2.add_mul, ha, hb] },
end

lemma mul_assoc_aux2 {x : tensor_algebra2 R M}
  {k : ℕ} (s : multiset (R × (fin k → M))) (X : R × (fin k → M))
  {j : ℕ} (t : multiset (R × (fin j → M))) :
(λ (f : tensor_algebra2 R M →ₗ[R] tensor_algebra2 R M),
            f ((lof R ℕ (tensor_power R M) k) (mk R M k X.snd)))
∘ ((mul R M) ∘ (mul R M x)) ∘
  (λ (i : R × (fin j → M)),
     i.fst • (lof R ℕ (tensor_power R M) j) (mk R M j i.snd))
      =
  (mul R M x) ∘
         (λ (y : tensor_algebra2 R M), y * (lof R ℕ (tensor_power R M) k) (mk R M k X.snd)) ∘
           λ (i : R × (fin j → M)),
             i.fst • (lof R ℕ (tensor_power R M) j) (mk R M j i.snd) :=
begin
  ext Y l,
  simp only [linear_map.smul_apply, function.comp_app, dfinsupp.smul_apply, linear_map.map_smul],
  rw [tensor_algebra2.smul_assoc, linear_map.map_smul, dfinsupp.smul_apply],
  congr' 2,
  erw mul_apply,
  simp only [mul_def],
  erw mul_assoc_aux R M _ _ s _ j t _,
end

lemma tensor_algebra2.mul_assoc (x y z : tensor_algebra2 R M) : x * y * z = x * (y * z) :=
begin
  refine direct_sum.linduction_on R z _ _ _,
  -- apply the inductive principle for direct sums to `z`: it suffices to prove for 0, for elements
  -- contained in one component, and the `P w → P z → P (w + z)`
  { simp only [tensor_algebra2.mul_zero] }, -- easy for `z = 0`
  -- now we prove the case for some `c` in the `k`th summand
  { rintros k c,
    rcases exists_sum_of_tensor_power _ _ c with ⟨s, rfl⟩, -- decompose `c` as a linear combination of blahs
    rw map_sum,
    simp only [linear_map.map_smul],
    rw [tensor_algebra2.mul_sum, tensor_algebra2.mul_sum, multiset.map_map, multiset.map_map,
        tensor_algebra2.mul_sum], -- applying linearity properties
    congr' 1,
    simp only [function.comp_app, multiset.map_map],
    congr' 1,
    ext X,
    simp only [function.comp_app, dfinsupp.smul_apply],
    refine direct_sum.linduction_on R y _ _ _, -- inductive principle for direct sum with respect to `y`
    { simp only [tensor_algebra2.mul_zero, linear_map.map_zero, -- `y = 0` case
      dfinsupp.zero_apply, linear_map.zero_apply, smul_zero] },
    { rintros j b, -- case of some `b` in the `j`th summand
      rcases exists_sum_of_tensor_power _ _ b with ⟨t, rfl⟩, -- decompose as linear combination
      rw map_sum R _ _ t (λ i : R × (fin j → M), i.1 • mk R M j i.2),
      simp only [linear_map.map_smul],
      rw [tensor_algebra2.mul_sum, linear_map.map_sum₂, multiset.map_map, multiset.map_map],
      congr' 2,
      rw [sum_apply', mul_def, mul_def, tensor_algebra2.sum_mul, tensor_algebra2.mul_sum],
      simp only [linear_map.smul_apply, function.comp_app, multiset.map_map, linear_map.map_smul],
      -- linearity properties
      refine congr_arg _ _,
      erw mul_assoc_aux2 R M s X t }, -- we finish by inducting on `x` as well, but factor this out as the separate lemma `mul_assoc_aux2` for speed reasons
    { intros a b ha hb, -- an application of distributivity
      rw [tensor_algebra2.mul_add, linear_map.map_add, linear_map.add_apply,
          linear_map.map_add, linear_map.add_apply, linear_map.map_add],
      simp only [add_apply],
      rw [ha, hb] }},
  { intros a b ha hb, -- an application of distributivity
    rw [tensor_algebra2.mul_add, tensor_algebra2.mul_add, ha, hb, tensor_algebra2.mul_add] },
end

lemma tensor_algebra2.mul_one (x : tensor_algebra2 R M) : x * 1 = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [←zero_eq_mk, ←one_eq_mk, mul_apply, fin.append_default'] },
  { intros i y,
    rcases exists_sum_of_tensor_power _ _ y with ⟨s, rfl⟩,
    rw [map_sum, tensor_algebra2.sum_mul, multiset.map_map],
    congr' 2, ext y j,
    simp only [function.comp_app, linear_map.map_smul],
    rw ←one_eq_mk,
    erw [tensor_algebra2.smul_assoc, mul_apply],
    congr,
    rw fin.append_default' },
  { intros x y hx hy,
    rw [tensor_algebra2.add_mul, hx, hy] },
end

lemma tensor_algebra2.one_mul (x : tensor_algebra2 R M) : 1 * x = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [←zero_eq_mk, ←one_eq_mk, mul_apply],
    refl },
  { intros i y,
    rcases exists_sum_of_tensor_power _ _ y with ⟨s, rfl⟩,
    rw [map_sum, tensor_algebra2.mul_sum, multiset.map_map],
    congr' 2, ext y j,
    simp only [function.comp_app, linear_map.map_smul],
    rw ←one_eq_mk,
    congr,
    show tensor_algebra2_mk R M _ * tensor_algebra2_mk R M y.2 = _,
    rw mul_apply,
    congr,
    rw zero_add,
    rw fin.heq_fun_iff (zero_add _),
    intro k,
    rw fin.default_append,
    congr,
    rw zero_add },
  { intros x y hx hy,
    rw [tensor_algebra2.mul_add, hx, hy] },
end

instance tensor_algebra2.monoid : monoid (tensor_algebra2 R M) :=
{ mul_assoc := tensor_algebra2.mul_assoc _ _,
  one := 1,
  one_mul := tensor_algebra2.one_mul _ _,
  mul_one := tensor_algebra2.mul_one _ _, ..tensor_algebra2.has_mul _ _ }

instance : ring (tensor_algebra2 R M) :=
{ left_distrib := by exact tensor_algebra2.mul_add R M,
  right_distrib := by exact tensor_algebra2.add_mul R M,
  ..direct_sum.add_comm_group _, ..tensor_algebra2.monoid _ _ }

def tensor_algebra2.of_scalar : R →+* (tensor_algebra2 R M) :=
{ to_fun := direct_sum.lof R ℕ (tensor_power R M) 0,
  map_one' := rfl,
  map_mul' := λ x y,
    begin
      rw ←mul_one (x * y),
      conv_rhs {rw ←mul_one x, rw ←mul_one y},
      erw [linear_map.map_smul, linear_map.map_smul, linear_map.map_smul],
      show _ = mul R M (x • tensor_algebra2_mk R M (default (fin 0 → M)))
        (y • tensor_algebra2_mk R M (default (fin 0 → M))),
      rw [linear_map.map_smul, linear_map.map_smul₂, mul_def,
          mul_apply, mul_comm, mul_smul],
      congr,
    end,
  map_zero' := linear_map.map_zero _,
  map_add' := linear_map.map_add _ }

lemma tensor_algebra2.of_scalar_apply {x : R} :
  tensor_algebra2.of_scalar R M x = direct_sum.lof R ℕ (tensor_power R M) 0 x := rfl

lemma tensor_algebra2.smul_one (r : R) : r • (1 : tensor_algebra2 R M) = tensor_algebra2.of_scalar R M r :=
begin
  rw [tensor_algebra2.of_scalar_apply, ←one_eq_mk],
  unfold tensor_algebra2_mk,
  ext,
  cases i,
  convert mul_one r,
  rw [tensor_power.mk'_apply, ←linear_map.map_smul],
  simp only [dfinsupp.smul_apply],
  unfold tensor_power.mk,
  rw [algebra.id.smul_eq_mul, mul_one],
end

instance : algebra R (tensor_algebra2 R M) :=
{ smul := (•),
  to_fun := tensor_algebra2.of_scalar R M,
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
      show r • (tensor_algebra2.of_scalar R M 1 * x) = r • (x * tensor_algebra2.of_scalar R M 1),
      rw [ring_hom.map_one, mul_one, one_mul],
    end,
  smul_def' := λ r x,
    begin
      simp only,
      rw [←tensor_algebra2.smul_one R M r, ←mul_def, linear_map.map_smul₂, mul_def, one_mul],
    end }

variables {R M}

/-- An linear map `M → A` with `A` an `R`-algebra induces a multilinear map sending tuples `(x₁, ..., xₙ)` in `M` to `f(x₁) * ... * f(xₙ)`. -/
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
def tensor_algebra2.lift {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) : tensor_algebra2 R M →ₐ[R] A :=
{ to_fun := direct_sum.to_module -- constructs a map out of a direct sum, given a family of maps from each component
    R ℕ A $ λ n, @tensor_power.lift R _ M _ _ n A _ _ (alg_prod f n),
  map_one' := by erw [←one_eq_mk, to_module_lof, tensor_power.lift_mk_apply]; convert list.prod_nil,
  map_mul' := λ x y,
    begin
      refine direct_sum.linduction_on R x _ _ _,
      { rw [zero_mul, linear_map.map_zero, zero_mul] },
      { intros i z,
        refine direct_sum.linduction_on R y _ _ _,
        { rw [mul_zero, linear_map.map_zero, mul_zero] },
        { intros j w,
          rw [to_module_lof, to_module_lof],
          rcases exists_sum_of_tensor_power R M z with ⟨s, rfl⟩,
          rw [map_sum, map_sum, tensor_algebra2.sum_mul, multiset.map_map, map_sum],
          rcases exists_sum_of_tensor_power R M w with ⟨t, rfl⟩,
          rw [map_sum, map_sum, multiset.sum_mul],
          congr' 1,
          rw multiset.map_map,
          congr' 1,
          ext z,
          simp only [function.comp_app, linear_map.map_smul, algebra.smul_mul_assoc],
          congr,
          erw [tensor_power.lift_mk_apply, multiset.mul_sum],
          rw [multiset.map_map, map_sum, multiset.mul_sum],
          congr' 1,
          rw multiset.map_map,
          congr' 1,
          ext w,
          simp only [algebra.mul_smul_comm, function.comp_app, linear_map.map_smul],
          congr,
          erw [tensor_power.lift_mk_apply, mul_apply, to_module_lof],
          rw tensor_power.lift_mk_apply,
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

def ι : M →ₗ[R] tensor_algebra2 R M :=
(lof R ℕ (tensor_power R M) 1).comp (tensor_product.lid R M).symm.to_linear_map

variables {R M}

lemma ι_apply {x : M} : ι R M x = lof R ℕ (tensor_power R M) 1 (1 ⊗ₜ x) := rfl

lemma ι_eq_mk {x : M} : ι R M x = tensor_algebra2_mk R M (λ i : fin 1, x) :=
rfl

variables (R M)

lemma tensor_algebra2_mk_prod {i : fin n → M} :
  tensor_algebra2_mk R M i = alg_prod (ι R M) n i :=
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

lemma tensor_algebra2.lift_ι_apply {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) {x : M} :
  tensor_algebra2.lift R M f (ι R M x) = f x :=
begin
  erw [to_module_lof, tensor_power.mk_one_lid_symm],
  rw [tensor_power.lift_mk_apply, alg_prod_apply],
  exact list.prod_singleton,
end

lemma hom_ext {A : Type u} [ring A] [algebra R A]
  (f g : tensor_algebra2 R M →ₐ[R] A) (h : f.to_linear_map.comp (ι R M) = g.to_linear_map.comp (ι R M)) :
  f = g :=
begin
  ext,
  refine direct_sum.linduction_on R x _ _ _,
  { simp only [alg_hom.map_zero] },
  { intros i y,
    rcases exists_sum_of_tensor_power R M y with ⟨s, rfl⟩,
    simp only [map_sum, linear_map.map_smul, alg_hom.map_sum', multiset.map_map],
    congr' 2,
    ext X,
    simp only [alg_hom.map_smul, function.comp_app],
    congr' 1,
    show f (tensor_algebra2_mk R M _) = g (tensor_algebra2_mk R M _),
    erw tensor_algebra2_mk_prod,
    simp only [alg_prod_apply, alg_hom.map_prod', list.of_fn_eq_map, list.map_map],
    congr' 2,
    ext,
    rw linear_map.ext_iff at h,
    exact h _ },
  { intros X Y HX HY,
    simp only [alg_hom.map_add, HX, HY] },
end

def to_tensor_algebra2 : tensor_algebra R M →ₐ[R] tensor_algebra2 R M :=
tensor_algebra.lift R (ι R M)

lemma to_tensor_algebra2_mk {i : fin n → M} :
  to_tensor_algebra2 R M (tensor_algebra.mk R M i) = tensor_algebra2_mk R M i :=
begin
  show to_tensor_algebra2 R M (list.prod (list.map _ _)) = _,
  rw [alg_hom.map_prod', list.map_map],
  unfold to_tensor_algebra2,
  rw function.comp,
  have : (λ x : fin n, tensor_algebra.lift R (ι R M)
    (tensor_algebra.ι R (i x))) = ι R M ∘ i :=
  by funext; exact tensor_algebra.lift_ι_apply (ι R M) (i x),
  rw [this, tensor_algebra2_mk_prod],
  congr,
  exact list.of_fn_eq_map.symm,
end

theorem tensor_algebra2.right_inverse (x : tensor_algebra2 R M) :
  to_tensor_algebra2 R M (tensor_algebra2.lift R M (tensor_algebra.ι R) x) = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [alg_hom.map_zero, alg_hom.map_zero] },
  { intros i y,
    rcases exists_sum_of_tensor_power R M y with ⟨s, rfl⟩,
    rw map_sum,
    simp only [linear_map.map_smul],
    rw [alg_hom.map_sum', multiset.map_map, alg_hom.map_sum', multiset.map_map],
    congr,
    ext y j,
    simp only [alg_hom.map_smul, function.comp_app, dfinsupp.smul_apply],
    congr,
    erw [to_module_lof, tensor_power.lift_mk_apply],
    rw [alg_prod_apply, alg_hom.map_prod', list.map_of_fn],
    unfold to_tensor_algebra2,
    rcases y with ⟨y1, y2⟩,
    simp only [],
    clear s y1,
    induction i with i hi,
    { show _ = tensor_algebra2_mk R M (default (fin 0 → M)),
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

theorem tensor_algebra2.left_inverse (x : tensor_algebra R M) :
  tensor_algebra2.lift R M (tensor_algebra.ι R) (to_tensor_algebra2 R M x) = x :=
begin
  refine tensor_algebra.induction R _ _ _ _ _ x,
  { intro r,  -- the `r : R` case
    unfold to_tensor_algebra2,
    simp only [alg_hom.commutes] },
  { intro x, -- the `x : M` case
    unfold to_tensor_algebra2,
    rw [tensor_algebra.lift_ι_apply, ι_eq_mk],
    erw to_module_lof,
    rw [tensor_power.lift_mk_apply, alg_prod_apply],
    -- reduce to a statement about product of elements of a list
    simp only [list.repeat, mul_one, function.comp_const, list.prod_cons,
      list.prod_nil, list.of_fn_const] },
  { intros y z hy hz, -- `P x → P y → P(x * y)`
    simp only [alg_hom.map_mul, hy, hz] },
  { intros y z hy hz, -- `P x → P y → P(x + y)`
    simp only [alg_hom.map_add, hy, hz] },
end

def tensor_algebra2_equiv : tensor_algebra2 R M ≃ₐ[R] tensor_algebra R M :=
alg_equiv.of_alg_hom (tensor_algebra2.lift R M (tensor_algebra.ι R))
  (to_tensor_algebra2 R M) (alg_hom.ext $ tensor_algebra2.left_inverse R M) (alg_hom.ext $ tensor_algebra2.right_inverse R M)
