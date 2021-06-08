import m4r.exterior_power
import m4r.new_complexes
import algebra.category.Module.basic

universes u v

open_locale classical tensor_product

lemma differential_object.complex_like.range_le_ker {R : Type u}
  [ring R] {ι : Type} [has_succ ι] {cov : bool}
  (F : differential_object.complex_like ι (Module R) cov) {i j k : ι} :
  (F.d i j).range ≤ (F.d j k).ker :=
λ x ⟨y, hym, hy⟩, by rw ←hy; exact linear_map.ext_iff.1 (F.d_comp_d i j k) y

@[simp] lemma differential_object.complex_like.d_comp_d_apply {R : Type u} [ring R] {ι : Type}
  [has_succ ι] {cov : bool} (F : differential_object.complex_like ι (Module R) cov) (i j k : ι) (x) :
  F.d j k (F.d i j x) = 0 :=
linear_map.ext_iff.1 (F.d_comp_d _ _ _) _

lemma sum_of_eq_zero {ι : Type v} [add_comm_monoid ι] {s : multiset ι}
  (h : ∀ (x : ι), x ∈ s → x = 0) : s.sum = 0 :=
begin
  revert h,
  refine multiset.induction_on s _ _,
  { intro h,
    exact multiset.sum_zero },
  intros x t h hx,
  rw [multiset.sum_cons, h, hx x (multiset.mem_cons_self x _), zero_add],
  intros y ht,
  rw hx y (multiset.mem_cons_of_mem ht),
end

variables (R : Type u) [comm_ring R] {M : Type u} [add_comm_group M] [module R M] (x : M)

/-- The linear map `Λⁿ M → Λⁿ⁺¹ M` given by `x ∧ ⬝`. -/
def wedge_d (n : ℕ) : exterior_power R M n →ₗ[R] exterior_power R M n.succ :=
exterior_power_lift R $ -- will be induced by an alternating map `M × ... × M → Λⁿ⁺¹ M`
{ to_fun := λ f, exterior_power.mk R M n.succ $ fin.cons x f, -- append `x` to the beginning of an `n`-tuple and map the resulting `n + 1`-tuple into `Λⁿ⁺¹ M`.
  map_add' := λ x i y j, by simp only [fin.cons_update, alternating_map.map_add],
  map_smul' := λ x i r j, by simp only [fin.cons_update, alternating_map.map_smul],
  map_eq_zero_of_eq' := λ v i j h hij,
    alternating_map.map_eq_zero_of_eq _ (fin.cons x v)
    (show (fin.cons _ _ : fin n.succ → M) i.succ = (fin.cons _ _ : fin n.succ → M) j.succ,
      by rw [fin.cons_succ, fin.cons_succ, h]) (λ hnot, hij $ fin.succ_inj.1 hnot) }

def wedge_d_squared (n : ℕ) : (wedge_d R x n.succ).comp (wedge_d R x n) = 0 :=
begin
  ext y,
  refine quotient.induction_on' y _,
  intro X, -- let `X : tensor_power R M n`; we show `d²(π(X)) = 0` in the exterior power
  rw linear_map.zero_apply,
  rcases exists_sum_of_tensor_power R M X with ⟨s, rfl⟩, -- decompose `X` as a linear combination of ... monomials? homogeneous elements? not sure
  show (wedge_d R x n.succ).comp (wedge_d R x n) (submodule.mkq _ _) = 0,
  rw [map_sum' R _ (exterior_power_ker R M n).mkq, multiset.map_map, map_sum', multiset.map_map], -- apply linearity lemmas
  refine sum_of_eq_zero _, -- suffices to show each term in the sum is 0
  intros Y hY,
  rw multiset.mem_map at hY,
  rcases hY with ⟨f, hfs, rfl⟩,
  simp only [function.comp_app, submodule.mkq_apply, linear_map.map_smul, linear_map.comp_apply],
  erw [exterior_power_lift_mk, exterior_power_lift_mk],
  simp only [alternating_map.coe_mk],
  convert smul_zero _, -- we've got the goal into the form `x ∧ x ∧ ... = 0`.
  refine @alternating_map.map_eq_zero_of_eq _ _ _ _ _ _ _ _ _ _ (exterior_power.mk R M n.succ.succ)
    (fin.cons x (fin.cons x f.2)) 0 1 (by refl)
    (show (0 : fin n.succ.succ) ≠ 1, from λ h01, zero_ne_one ((fin.ext_iff _ _).1 h01)),
end

variables (M)

def Koszul : cochain_complex ℤ (Module R) :=
cochain_complex.mk' -- takes differentials defined `Cₙ → Cₙ₊₁` and defines differentials for every pair of indices (by setting the rest 0)
  (λ n, int.cases_on n (λ m, Module.of R (exterior_power R M m))
    (λ m, Module.of R punit)) -- the `n`th module is `Λⁿ M` for `n : ℕ`, the zero module otherwise
  (λ n, int.cases_on n (λ m, wedge_d R x m) (λ m, 0)) -- the `n`th differential is `wedge_d R x n` for `n : ℕ`, 0 otherwise
  (begin
    intro n,
    cases n,
    exact wedge_d_squared R x n,
    dec_trivial,
  end)

variables (F : cochain_complex ℤ (Module R)) (i : ℤ) {M}

@[reducible] def int_pair (n : ℤ) := { i : ℤ × ℤ // i.1 + i.2 = n }
def int_pair_mk (n i j : ℤ) (h : i + j = n) : int_pair n :=
⟨(i, j), h⟩

@[simp] lemma int_pair_fst_eq_sub {n : ℤ} (i : int_pair n) :
  n - i.1.2 = i.1.1 :=
by rw [sub_eq_iff_eq_add, i.2]

@[simp] lemma int_pair_snd_eq_sub {n : ℤ} (i : int_pair n) :
  n - i.1.1 = i.1.2 :=
by rw [sub_eq_iff_eq_add', i.2]

lemma int_pair_ext_iff_fst {n : ℤ} {i j : int_pair n} :
  i = j ↔ i.1.1 = j.1.1 :=
⟨λ h, by cc, λ h, subtype.ext $ prod.ext h $
  by erw [←int_pair_snd_eq_sub i, ←int_pair_snd_eq_sub j, h]⟩

lemma int_pair_ext_iff_snd {n : ℤ} {i j : int_pair n} :
  i = j ↔ i.1.2 = j.1.2 :=
⟨λ h, by cc, λ h, subtype.ext $ prod.ext
  (by erw [←int_pair_fst_eq_sub i, ←int_pair_fst_eq_sub j, h]) h⟩

instance aux_acg (n : ℤ) (F G : cochain_complex ℤ (Module R)) :
  add_comm_group (direct_sum (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))) :=
@direct_sum.add_comm_group (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _

instance aux_module (n : ℤ) (F G : cochain_complex ℤ (Module R)) :=
@direct_sum.semimodule R _ (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _ _

variables (G : cochain_complex ℤ (Module R)) {n : ℤ}

lemma int_pair_add_one (i : int_pair n) :
  i.1.1 + 1 + i.1.2 = n + 1 :=
by {rw [add_comm, ←add_assoc, add_left_inj, add_comm], exact i.2 }

def total_d_fst (i : int_pair n) :
  (F.X i.1.1) ⊗[R] (G.X (int_pair_mk (n + 1) (i.1.1 + 1) i.1.2 _).1.2)
    →ₗ[R] direct_sum _ (λ (j : int_pair (n + 1)), (F.X j.1.1) ⊗[R] (G.X j.1.2)) :=
(direct_sum.lof R (int_pair (n + 1))
  (λ j, (F.X j.1.1) ⊗[R] (G.X j.1.2))
    (int_pair_mk (n + 1) (i.1.1 + 1) i.1.2 (int_pair_add_one _))).comp $
    (tensor_product.map (F.d i.1.1 _ : F.X i.1.1 →ₗ[R] F.X $ i.1.1 + 1) linear_map.id)

def total_d_snd (i : int_pair n) :
  (F.X (int_pair_mk (n + 1) i.1.1 (i.1.2 + 1) _).1.1) ⊗[R] (G.X i.1.2)
    →ₗ[R] direct_sum _ (λ (j : int_pair (n + 1)), (F.X j.1.1) ⊗[R] (G.X j.1.2)) :=
(direct_sum.lof R (int_pair (n + 1))
  (λ j, tensor_product R (F.X j.1.1) (G.X j.1.2))
      (int_pair_mk (n + 1) i.1.1 (i.1.2 + 1) (by rw [←add_assoc, i.2]))).comp $
  (tensor_product.map ((-1 : R)^(int.nat_abs i.1.1) • linear_map.id)
  (G.d i.1.2 _ : G.X i.1.2 →ₗ[R] G.X $ i.1.2 + 1))

variables (n)

def total_d : direct_sum (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) →ₗ[R]
    direct_sum (int_pair (n + 1))
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) :=
direct_sum.to_module R (int_pair n) _ $
λ (i : int_pair n), total_d_fst R F G i + total_d_snd R F G i

def total_d_hom : Module.of R (direct_sum (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))) ⟶
    Module.of R (direct_sum (int_pair (n + 1))
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))) := total_d R F G n

variables {n}

def int_pair_add_one_fst (i : int_pair n) : int_pair (n + 1) :=
int_pair_mk (n + 1) (i.1.1 + 1) i.1.2 (int_pair_add_one i)

def int_pair_add_one_snd (i : int_pair n) : int_pair (n + 1) :=
int_pair_mk (n + 1) i.1.1 (i.1.2 + 1) (by rw [←add_assoc, i.2])

lemma total_d_fst_apply (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) :
  total_d_fst R F G i (tensor_product.mk R _ _ x y) (int_pair_add_one_fst i) =
  (tensor_product.mk R (F.X $ i.1.1 + 1) (G.X i.1.2) (F.d i.1.1 _ x) y) :=
direct_sum.lof_apply R _ _

lemma total_d_fst_of_ne (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_fst i ≠ j) :
  total_d_fst R F G i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma total_d_snd_apply (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) :
  total_d_snd R F G i (tensor_product.mk R _ _ x y) (int_pair_add_one_snd i) =
  (tensor_product.mk R (F.X i.1.1) (G.X $ i.1.2 + 1)
    ((-1 : R)^(int.nat_abs i.1.1) • x) (G.d i.1.2 _ y)) :=
direct_sum.lof_apply R _ _

lemma total_d_snd_of_ne (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_snd i ≠ j) :
  total_d_snd R F G i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma total_d_snd_of_eq (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_snd i = j) :
  total_d_snd R F G i (tensor_product.mk R (F.X i.1.1) (G.X i.1.2) x y) j =
  tensor_product.mk R (F.X j.1.1) (G.X j.1.2)
    (eq.rec ((-1 : R)^(int.nat_abs i.1.1) • x) $ show i.1.1 = j.1.1, by rw ←hj; refl)
    (eq.rec (G.d i.1.2 _ y) $ show i.1.2 + 1 = j.1.2, by rw ←hj; refl) :=
begin
  cases hj,
  convert total_d_snd_apply R F G i x y,
end

lemma int_pair_add_one_comm (i : int_pair n) :
  int_pair_add_one_fst (int_pair_add_one_snd i) = int_pair_add_one_snd (int_pair_add_one_fst i) :=
subtype.ext rfl

lemma neg_one_pow_nat_abs (i : ℤ) : (-1 : R) ^ (i + 1).nat_abs = -(-1 : R) ^ i.nat_abs :=
begin
  rw neg_eq_neg_one_mul ((-1 : R) ^ _),
  induction i,
  { rw ←pow_succ,
    congr },
  { rw [int.nat_abs, pow_succ, ←mul_assoc],
    simp only [neg_mul_neg, one_mul],
    congr,
    show int.nat_abs (-(i + 1 : ℤ) + 1) = _,
    simp only [int.nat_abs_of_nat, neg_add_cancel_comm, int.nat_abs_neg,
      neg_add_rev] },
end

lemma neg_one_pow_aux {N : Type v} [add_comm_group N] [module R N] (x : N) (i : ℤ) :
  (-1 : R) ^ (i + 1).nat_abs • x + (-1 : R) ^ i.nat_abs • x = 0 :=
begin
  cases @neg_one_pow_eq_or R _ i.nat_abs,
  any_goals {simp only [neg_one_pow_nat_abs, h, add_left_neg, neg_smul]},
end

variables (n)
lemma total_d_squared : (total_d R F G _).comp (total_d R F G n) = 0 :=
begin
  apply dfinsupp.lhom_ext, -- suffices to prove that `d^2(X) = 0` for some `X : F_i₁ ⊗ G_i₂`
  rintro i X,
  refine tensor_product.induction_on X _ _ _, -- suffices to show for 0, elements of the form `x ⊗ y`, and that `P x → P y → P (x + y)`
  { rw [dfinsupp.single_zero, linear_map.map_zero, linear_map.zero_apply] }, -- trivial for 0
  { intros x y, -- the `x ⊗ y` case
    rw [direct_sum.single_eq_lof R, linear_map.comp_apply],
    erw direct_sum.to_module_lof,
    rw [linear_map.add_apply, linear_map.map_add], -- applying linearity properties
    erw [direct_sum.to_module_lof, direct_sum.to_module_lof], -- triviality about maps out of a direct sum restricted to each component
    rw [tensor_product.map_tmul, tensor_product.map_tmul], -- def of tensor product of maps: `(f ⊗ g)(x ⊗ y) = f(x) ⊗ g(y)`
    unfold total_d_fst total_d_snd,
    simp only [linear_map.id_coe, id.def, linear_map.smul_apply, linear_map.zero_apply,
      linear_map.add_apply, subtype.val_eq_coe, linear_map.comp_apply, tensor_product.map_tmul,
      linear_map.map_add, linear_map.map_smul],
    -- we've got the goal into the form `d(F)^2(x) ⊗ y + ((-1)^|i₁ + 1| • d(F)(x)) ⊗ d(G)(y) + ((-1)^|i₁| • d(F)(x)) ⊗ d(G)(y) + x ⊗ d(G)^2(y) = 0`
    erw [F.d_comp_d_apply, G.d_comp_d_apply], -- apply `d(F)^2, d(G)^2 = 0`
    rw [tensor_product.zero_tmul, linear_map.map_zero, tensor_product.tmul_zero, linear_map.map_zero,
      add_zero, zero_add], -- trivialities
    erw neg_one_pow_nat_abs, -- apply `(-1) ^ |i₁ + 1| = -(-1) ^ |i₁|`, and we're essentially done.
    rw [neg_smul, tensor_product.neg_tmul, linear_map.map_neg, add_eq_zero_iff_eq_neg],
    congr },
  { intros x y hx hy, -- the `P x → P y → P (x + y)` statement, which follows from linearity of linear maps.
    rw [dfinsupp.single_add, linear_map.map_add, hx, hy, linear_map.zero_apply, zero_add],
    refl },
end

variables {M}

open_locale tensor_product
lemma total_d_hom_squared (n : ℤ) : total_d_hom R F G n ≫ total_d_hom R F G (succ n) = 0 :=
begin
  refine linear_map.ext _,
  intro x,
  dsimp,
  unfold total_d_hom,
  exact linear_map.ext_iff.1 (total_d_squared R F G n) x,
end

def cochain_complex.total (F G : cochain_complex.{u+1} ℤ (Module.{u} R)) :=
cochain_complex.mk' (λ n, Module.of R (direct_sum (int_pair n)
    (λ (i : int_pair n), tensor_product R (F.X i.1.1) (G.X i.1.2))))
  (λ n, total_d_hom R F G n) (total_d_hom_squared R F G)

variables {ι : Type} [has_succ ι] {cov : bool}
  (C : differential_object.complex_like.{u+1} ι (Module.{u} R) cov)
  (A : Module.{u} R)

def differential_object.complex_like.tensor_pure :
  differential_object.complex_like.{u+1} ι (Module.{u} R) cov :=
{ X := λ i, Module.of R (A ⊗[R] (C.X i)), -- the modules are `A ⊗ Cᵢ`
  d := λ i j, linear_map.ltensor A (C.d i j), -- the maps are `1 ⊗ d`
  d_comp_d := λ i j k,
  begin
    ext x,
    erw tensor_product.map_tmul,
    erw linear_map.ext_iff.1 (C.d_comp_d i j k),
    simp only [tensor_product.tmul_zero, linear_map.compr₂_apply, linear_map.zero_apply],
  end,
  d_eq_zero := λ i j h, by rw [C.d_eq_zero h, linear_map.ltensor_zero A] }

def differential_object.complex_like.ltensor
  {C D : differential_object.complex_like.{u+1} ι (Module.{u} R) cov}
  (A : Module.{u} R)
  (f : C ⟶ D) : C.tensor_pure R A ⟶ D.tensor_pure R A :=
{ f := λ i, (f.f i).ltensor A,
  comm := λ i j,
  begin
    ext,
    simp only [linear_map.compr₂_apply, Module.coe_comp],
    show (f.f j).ltensor A ((C.d i j).ltensor A _) = (D.d i j).ltensor A _,
    simp only [tensor_product.mk_apply, linear_map.ltensor_tmul],
    erw linear_map.ext_iff.1 (f.comm i j) _,
    refl,
  end }

def differential_object.complex_like.hom_snd :
  differential_object.complex_like.{u+1} ι (Module.{u} R) cov :=
{ X := λ i, Module.of R (A →ₗ[R] C.X i), -- the modules are `Hom(M, Cᵢ)`
  d := λ i j, linear_map.llcomp R A _ _ (C.d i j), --the maps are `d ∘ -`
  d_comp_d := λ i j k,
  begin
    ext y,
    simp only [linear_map.llcomp_apply, Module.coe_comp],
    exact linear_map.ext_iff.1 (C.d_comp_d i j k) _,
  end,
  d_eq_zero := λ i j h,
  begin
    ext,
    simp only [linear_map.llcomp_apply],
    exact linear_map.ext_iff.1 (C.d_eq_zero h) _,
  end }

def differential_object.complex_like.hom_fst :
  differential_object.complex_like.{u+1} ι (Module.{u} R) ¬cov :=
{ X := λ i, Module.of R (C.X i →ₗ[R] A), -- the modules are `Hom(Cᵢ, A)`
  d := λ i j, linear_map.lcomp R A (C.d j i), -- the maps are `- ∘ d`
  d_comp_d := λ i j k,
  begin
    ext y,
    simp only [linear_map.lcomp_apply, Module.coe_comp, linear_map.zero_apply],
    erw [linear_map.ext_iff.1 (C.d_comp_d _ _ _) _, y.map_zero],
  end,
  d_eq_zero := λ i j h,
  begin
    ext,
    simp only [linear_map.lcomp_apply, linear_map.zero_apply],
    erw [linear_map.ext_iff.1 (C.d_eq_zero _) _, x.map_zero],
    contrapose! h,
    cases cov,
    { exact h.symm },
    { exact h.symm },
  end }
