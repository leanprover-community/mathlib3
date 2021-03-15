import m4r.exterior_power
import algebra.homology.exact
import algebra.homology.chain_complex
import algebra.category.Module.basic

universes u v
variables (R : Type u) [comm_ring R] {M : Type u} [add_comm_group M] [module R M] (x : M)

open_locale classical

def wedge_d (n : ℕ) : epow R M n →ₗ[R] epow R M n.succ :=
epow_lift R $
{ to_fun := λ f, epow.mk R M n.succ $ fin.cons x f,
  map_add' := λ x i y j, by simp only [fin.cons_update, alternating_map.map_add],
  map_smul' := λ x i r j, by simp only [fin.cons_update, alternating_map.map_smul],
  map_eq_zero_of_eq' := λ v i j h hij,
    alternating_map.map_eq_zero_of_eq _ (fin.cons x v)
    (show (fin.cons _ _ : fin n.succ → M) i.succ = (fin.cons _ _ : fin n.succ → M) j.succ,
      by rw [fin.cons_succ, fin.cons_succ, h]) (λ hnot, hij $ fin.succ_inj.1 hnot) }

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

def wedge_d_squared (n : ℕ) : (wedge_d R x n.succ).comp (wedge_d R x n) = 0 :=
begin
  ext y,
  refine quotient.induction_on' y _,
  intro X,
  rw linear_map.zero_apply,
  rcases exists_sum_of_tpow R M X with ⟨s, rfl⟩,
  show (wedge_d R x n.succ).comp (wedge_d R x n) (submodule.mkq _ _) = 0,
  rw [map_sum' R _ (epow_ker R M n).mkq, multiset.map_map, map_sum', multiset.map_map],
  refine sum_of_eq_zero _,
  intros Y hY,
  rw multiset.mem_map at hY,
  rcases hY with ⟨f, hfs, rfl⟩,
  simp only [function.comp_app, submodule.mkq_apply, linear_map.map_smul, linear_map.comp_apply],
  erw [epow_lift_mk, epow_lift_mk],
  simp only [alternating_map.coe_mk],
  convert smul_zero _,
  refine @alternating_map.map_eq_zero_of_eq _ _ _ _ _ _ _ _ _ _ (epow.mk R M n.succ.succ)
    (fin.cons x (fin.cons x f.2)) 0 1 (by refl)
    (show (0 : fin n.succ.succ) ≠ 1, from λ h01, zero_ne_one ((fin.ext_iff _ _).1 h01)),
end

variables (M)

def Koszul : cochain_complex (Module R) :=
{ X := λ n, int.cases_on n (λ m, Module.of R (epow R M m)) (λ m, Module.of R punit),
  d := λ n, int.cases_on n (λ m, wedge_d R x m) (λ m, 0),
  d_squared' := begin
    ext1 n,
    cases n,
    exact wedge_d_squared R x n,
    dec_trivial,
  end}

variables {M}

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

instance aux_acg (n : ℤ) (F G : cochain_complex (Module R)) :
  add_comm_group (direct_sum (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))) :=
@direct_sum.add_comm_group (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _

instance aux_module (n : ℤ) (F G : cochain_complex (Module R)) :=
@direct_sum.semimodule R _ (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _ _

variables (F G : cochain_complex (Module R)) {n : ℤ}

lemma int_pair_add_one (i : int_pair n) :
  i.1.1 + 1 + i.1.2 = n + 1 :=
by {rw [add_comm, ←add_assoc, add_left_inj, add_comm], exact i.2 }

def tensor_d_fst (i : int_pair n) :=
(direct_sum.lof R (int_pair (n + 1))
  (λ j, tensor_product R (F.X j.1.1) (G.X j.1.2))
    (int_pair_mk (n + 1) (i.1.1 + 1) i.1.2 (int_pair_add_one _))).comp $
    (tensor_product.map (F.d i.1.1 : F.X i.1.1 →ₗ[R] F.X $ i.1.1 + 1) linear_map.id)

def tensor_d_snd (i : int_pair n) :=
(direct_sum.lof R (int_pair (n + 1))
  (λ j, tensor_product R (F.X j.1.1) (G.X j.1.2))
      (int_pair_mk (n + 1) i.1.1 (i.1.2 + 1) (by rw [←add_assoc, i.2]))).comp $
  (tensor_product.map ((-1 : R)^(int.nat_abs i.1.1) • linear_map.id)
  (G.d i.1.2 : G.X i.1.2 →ₗ[R] G.X $ i.1.2 + 1))

def tensor_d : direct_sum (int_pair n)
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) →ₗ[R]
    direct_sum (int_pair (n + 1))
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) :=
direct_sum.to_module R (int_pair n) _ $
λ (i : int_pair n), tensor_d_fst R F G i + tensor_d_snd R F G i

def int_pair_add_one_fst (i : int_pair n) : int_pair (n + 1) :=
int_pair_mk (n + 1) (i.1.1 + 1) i.1.2 (int_pair_add_one i)

def int_pair_add_one_snd (i : int_pair n) : int_pair (n + 1) :=
int_pair_mk (n + 1) i.1.1 (i.1.2 + 1) (by rw [←add_assoc, i.2])

lemma tensor_d_fst_apply (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) :
  tensor_d_fst R F G i (tensor_product.mk R _ _ x y) (int_pair_add_one_fst i) =
  (tensor_product.mk R (F.X $ i.1.1 + 1) (G.X i.1.2) (F.d i.1.1 x) y) :=
direct_sum.lof_apply R _ _

lemma tensor_d_fst_of_ne (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_fst i ≠ j) :
  tensor_d_fst R F G i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma tensor_d_fst_of_eq (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_fst i = j) :
  tensor_d_fst R F G i (tensor_product.mk R (F.X i.1.1) (G.X i.1.2) x y) j =
  tensor_product.mk R (F.X j.1.1) (G.X j.1.2)
    (eq.rec (F.d i.1.1 x) $ show i.1.1 + 1 = j.1.1, by rw ←hj; refl)
    (eq.rec y $ show i.1.2 = j.1.2, by rw ←hj; refl) :=
begin
  cases hj,
  convert tensor_d_fst_apply R F G i x y,
end

lemma tensor_d_snd_apply (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) :
  tensor_d_snd R F G i (tensor_product.mk R _ _ x y) (int_pair_add_one_snd i) =
  (tensor_product.mk R (F.X i.1.1) (G.X $ i.1.2 + 1)
    ((-1 : R)^(int.nat_abs i.1.1) • x) (G.d i.1.2 y)) :=
direct_sum.lof_apply R _ _

lemma tensor_d_snd_of_ne (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_snd i ≠ j) :
  tensor_d_snd R F G i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma tensor_d_snd_of_eq (i : int_pair n)
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : int_pair_add_one_snd i = j) :
  tensor_d_snd R F G i (tensor_product.mk R (F.X i.1.1) (G.X i.1.2) x y) j =
  tensor_product.mk R (F.X j.1.1) (G.X j.1.2)
    (eq.rec ((-1 : R)^(int.nat_abs i.1.1) • x) $ show i.1.1 = j.1.1, by rw ←hj; refl)
    (eq.rec (G.d i.1.2 y) $ show i.1.2 + 1 = j.1.2, by rw ←hj; refl) :=
begin
  cases hj,
  convert tensor_d_snd_apply R F G i x y,
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

lemma tensor_d_squared : (tensor_d R F G).comp (@tensor_d R _ F G n) = 0 :=
begin
  ext i x y j,
  simp only [tensor_product.mk_apply, linear_map.compr₂_apply, dfinsupp.lsingle_apply,
    linear_map.zero_apply, direct_sum.zero_apply, linear_map.comp_apply],
  erw [direct_sum.to_module_lof, linear_map.add_apply, linear_map.map_add,
    direct_sum.to_module_lof, direct_sum.to_module_lof],
  rw [linear_map.add_apply, linear_map.add_apply],
  repeat {rw tensor_product.map_tmul},
  repeat {rw dfinsupp.add_apply},
  cases classical.em (int_pair_add_one_fst (int_pair_add_one_fst i) = j),
  { have hj1 : int_pair_add_one_fst (int_pair_add_one_snd i) ≠ j :=
    λ hnot, succ_ne_self (i.1.1 + 1) $
      (prod.ext_iff.1 $ subtype.ext_iff.1 (h.trans hnot.symm)).1,
    have hj2 : int_pair_add_one_snd (int_pair_add_one_snd i) ≠ j := λ hnot, by {
      obtain ⟨h1, h2⟩ := prod.ext_iff.1 (subtype.ext_iff.1 $ h.trans hnot.symm),
      change i.1.1 + 1 + 1 = i.1.1 at h1,
      linarith },
    have hj3 : int_pair_add_one_snd (int_pair_add_one_fst i) ≠ j :=
    λ hnot, succ_ne_self (i.1.1 + 1) $
      (prod.ext_iff.1 $ subtype.ext_iff.1 (h.trans hnot.symm)).1,
    erw [dfinsupp.single_eq_of_ne hj1, dfinsupp.single_eq_of_ne hj2,
      dfinsupp.single_eq_of_ne hj3],
    rw [add_zero, add_zero, add_zero, ←h],
    erw tensor_d_fst_apply,
    convert linear_map.map_zero₂ _ _,
    rw ←linear_map.comp_apply,
    convert linear_map.zero_apply _,
    exact F.d_squared _ },
  { cases classical.em (int_pair_add_one_fst (int_pair_add_one_snd i) = j) with hj hj,
    { have hj1 : int_pair_add_one_snd (int_pair_add_one_snd i) ≠ j := λ hnot, succ_ne_self i.1.1 $
        (prod.ext_iff.1 $ subtype.ext_iff.1 (hj.trans hnot.symm)).1,
      erw [dfinsupp.single_eq_of_ne h, dfinsupp.single_eq_of_ne hj1],
      rw [zero_add, add_zero, ←hj],
      erw [tensor_d_fst_apply, tensor_d_snd_of_eq _ _ _ _ _ _
        (int_pair_add_one_fst (int_pair_add_one_snd i)) (int_pair_add_one_comm i).symm],
      show tensor_product.mk R (F.X $ i.1.1 + 1) (G.X $ i.1.2 + 1)
        ((-1 : R) ^ (i.1.1 + 1).nat_abs • F.d i.1.1 x) (G.d i.1.2 y) +
        tensor_product.mk R (F.X $ i.1.1 + 1) (G.X $ i.1.2 + 1)
          (F.d i.1.1 ((-1 : R) ^ (i.1.1.nat_abs) • x)) (G.d i.1.2 y) = 0,
      rw ←linear_map.add_apply,
      convert linear_map.zero_apply _,
      rw ←linear_map.map_add,
      convert linear_map.map_zero _,
      rw [linear_map.map_smul, neg_one_pow_aux] },
    { cases classical.em (int_pair_add_one_snd (int_pair_add_one_snd i) = j) with hj1 hj1,
      { erw [dfinsupp.single_eq_of_ne hj, dfinsupp.single_eq_of_ne h,
          dfinsupp.single_eq_of_ne (λ hnot, hj $ (int_pair_add_one_comm _).trans hnot)],
        simp only [zero_add],
        rw ←hj1,
        erw tensor_d_snd_apply,
        convert linear_map.map_zero _,
        rw ←linear_map.comp_apply,
        convert linear_map.zero_apply _,
        exact G.d_squared _ },
      { erw [dfinsupp.single_eq_of_ne hj, dfinsupp.single_eq_of_ne h,
          dfinsupp.single_eq_of_ne (λ hnot, hj $ (int_pair_add_one_comm _).trans hnot),
          dfinsupp.single_eq_of_ne hj1],
        simp only [zero_add, dfinsupp.zero_apply] }}},
end

variables {M}

def cochain_complex.tensor_product (F G : cochain_complex.{u u+1} (Module.{u u} R)) :
  cochain_complex (Module R) :=
{ X := λ n, Module.of R (direct_sum (int_pair n)
    (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))),
  d := λ n, tensor_d R F G,
  d_squared' := by { ext1 n, dsimp, exact @tensor_d_squared R _ F G n }}

def cochain_complex.tensor_single (F : cochain_complex.{u u+1} (Module.{u u} R))
  (M : Module R) : cochain_complex (Module R) :=
{ X := λ i, Module.of R (tensor_product R (F.X i) M),
  d := λ i, tensor_product.map (F.d i) linear_map.id,
  d_squared' :=
  begin
    ext i x,
    simp only [category_theory.graded_object.zero_apply, linear_map.zero_apply],
    erw tensor_product.map_tmul,
    simp only [linear_map.id_coe, id.def],
    convert tensor_product.zero_tmul _ _,
    exact linear_map.ext_iff.1 (F.d_squared i) _,
  end }
