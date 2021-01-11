import m4r.exterior_power
import algebra.homology.exact
import algebra.homology.chain_complex
import algebra.category.Module.basic

variables (R : Type) [comm_ring R] {M : Type} [add_comm_group M] [module R M] (x : M)


def wedge_d (n : ℕ) : epow R M n →ₗ[R] epow R M n.succ :=
epow_lift R $
{ to_fun := λ f, epow.mk R M n.succ $ fin.cons x f,
  map_add' := λ x i y j, by simp only [fin.cons_update, alternating_map.map_add],
  map_smul' := λ x i r j, by simp only [fin.cons_update, alternating_map.map_smul],
  map_eq_zero_of_eq' := λ v i j h hij,
    alternating_map.map_eq_zero_of_eq _ (fin.cons x v)
    (show (fin.cons _ _ : fin n.succ → M) i.succ = (fin.cons _ _ : fin n.succ → M) j.succ,
      by rw [fin.cons_succ, fin.cons_succ, h]) (λ hnot, hij $ fin.succ_inj.1 hnot) }

lemma sum_of_eq_zero {ι : Type} [add_comm_monoid ι] {s : multiset ι}
  (h : ∀ (x : ι), x ∈ s → x = 0) : s.sum = 0 :=
begin
  revert h,
  refine multiset.induction_on s _ _,
    intro h, exact multiset.sum_zero,
  intros x t h hx,
  rw multiset.sum_cons,
  rw h,
  rw hx x (multiset.mem_cons_self x _),
  rw zero_add,
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
  rw map_sum' R _ (epow_ker R M n).mkq,
  rw multiset.map_map,
  rw map_sum',
  rw multiset.map_map,
  refine sum_of_eq_zero _,
  intros Y hY,
  rw multiset.mem_map at hY,
  rcases hY with ⟨f, hfs, rfl⟩,
  simp only [function.comp_app, submodule.mkq_apply, linear_map.map_smul, linear_map.comp_apply],
  erw epow_lift_mk,
  erw epow_lift_mk,
  simp only [alternating_map.coe_mk],
  convert smul_zero _,
  refine @alternating_map.map_eq_zero_of_eq _ _ _ _ _ _ _ _ _ _ (epow.mk R M n.succ.succ)
    (fin.cons x (fin.cons x f.2)) 0 1 (by refl)
    (show (0 : fin n.succ.succ) ≠ 1, by
    {intro h01, exact zero_ne_one ((fin.ext_iff _ _).1 h01) }),
end

def Koszul : cochain_complex (Module R) :=
{ X := λ n, int.cases_on n (λ m, Module.of R (epow R M m)) (λ m, Module.of R punit),
  d := λ n, int.cases_on n (λ m, wedge_d R x m) (λ m, 0),
  d_squared' := begin
    ext1 n,
    cases n,
    exact wedge_d_squared R x n,
    dec_trivial,
  end}

instance aux_acg (n : ℤ) (F G : cochain_complex (Module R)) :
  add_comm_group (direct_sum ({i : ℤ × ℤ // i.1 + i.2 = n})
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))) :=
@direct_sum.add_comm_group ({i : ℤ × ℤ // i.1 + i.2 = n})
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _

instance aux_module (n : ℤ) (F G : cochain_complex (Module R)) :=
@direct_sum.semimodule R _ ({i : ℤ × ℤ // i.1 + i.2 = n})
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) _ _

variables (F G : cochain_complex (Module R)) (n : ℤ)

lemma aux_succ_eq (i : {i : ℤ × ℤ // i.1 + i.2 = n}) :
  i.1.1 + 1 + i.1.2 = n + 1 :=
by {rw [add_comm, ←add_assoc, add_left_inj, add_comm], exact i.2 }

def tensor_d_fst (i : {i : ℤ × ℤ // i.1 + i.2 = n}) :=
(direct_sum.lof R ({i : ℤ × ℤ // i.1 + i.2 = n.succ})
  (λ j, tensor_product R (F.X j.1.1) (G.X j.1.2))
    ⟨⟨i.1.1.succ, i.1.2⟩,
    show i.1.1 + 1 + i.1.2 = n + 1, by
      {rw [add_comm, ←add_assoc, add_left_inj, add_comm], exact i.2 }⟩).comp $
    (tensor_product.map (F.d i.1.1 : F.X i.1.1 →ₗ[R] F.X i.1.1.succ) linear_map.id)

def tensor_d_snd (i : {i : ℤ × ℤ // i.1 + i.2 = n}) :=
(direct_sum.lof R ({i : ℤ × ℤ // i.1 + i.2 = n.succ}) (λ j, tensor_product R (F.X j.1.1) (G.X j.1.2))
      ⟨⟨i.1.1, i.1.2.succ⟩,
       show i.1.1 + (i.1.2 + 1) = n + 1, by {rw [←add_assoc, add_left_inj], exact i.2}⟩).comp $
  (tensor_product.map ((-1 : ℤ)^(int.nat_abs i.1.1) • linear_map.id)
  (G.d i.1.2 : G.X i.1.2 →ₗ[R] G.X i.1.2.succ))

def tensor_d : direct_sum {i : ℤ × ℤ // i.fst + i.snd = n}
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) →ₗ[R] direct_sum {i : ℤ × ℤ // i.fst + i.snd = n.succ}
  (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2)) :=
direct_sum.to_module R ({i : ℤ × ℤ // i.1 + i.2 = n}) _ $
λ (i : {i : ℤ × ℤ // i.1 + i.2 = n}), @tensor_d_fst R _ F G n i + tensor_d_snd R F G n i

def succ_fst (i : {i : ℤ × ℤ // i.1 + i.2 = n}) : {i : ℤ × ℤ // i.1 + i.2 = n.succ} :=
 ⟨⟨i.1.1.succ, i.1.2⟩,
    show i.1.1 + 1 + i.1.2 = n + 1, by
    {rw [add_comm, ←add_assoc, add_left_inj, add_comm], exact i.2 }⟩

def succ_snd (i : {i : ℤ × ℤ // i.1 + i.2 = n}) : {i : ℤ × ℤ // i.1 + i.2 = n.succ} :=
 ⟨⟨i.1.1, i.1.2.succ⟩,
       show i.1.1 + (i.1.2 + 1) = n + 1, by {rw [←add_assoc, add_left_inj], exact i.2}⟩

lemma tensor_d_fst_apply (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) :
  tensor_d_fst R F G n i (tensor_product.mk R _ _ x y) (succ_fst n i) =
  (tensor_product.mk R (F.X i.1.1.succ) (G.X i.1.2) (F.d i.1.1 x) y) :=
direct_sum.lof_apply R _ _

lemma tensor_d_fst_of_ne (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : succ_fst n i ≠ j) :
  tensor_d_fst R F G n i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma tensor_d_fst_of_eq (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : succ_fst n i = j) :
  tensor_d_fst R F G n i (tensor_product.mk R (F.X i.1.1) (G.X i.1.2) x y) j =
  tensor_product.mk R (F.X j.1.1) (G.X j.1.2)
    (eq.rec (F.d i.1.1 x) $ show i.1.1.succ = j.1.1, by rw ←hj; refl)
    (eq.rec y $ show i.1.2 = j.1.2, by rw ←hj; refl) :=
begin
  cases hj,
  convert tensor_d_fst_apply R F G n i x y,
end

lemma tensor_d_snd_apply (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) :
  tensor_d_snd R F G n i (tensor_product.mk R _ _ x y) (succ_snd n i) =
  (tensor_product.mk R (F.X i.1.1) (G.X i.1.2.succ) ((-1 : ℤ)^(int.nat_abs i.1.1) • x) (G.d i.1.2 y)) :=
direct_sum.lof_apply R _ _

lemma tensor_d_snd_of_ne (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : succ_snd n i ≠ j) :
  tensor_d_snd R F G n i (tensor_product.mk R _ _ x y) j = 0 :=
dfinsupp.single_eq_of_ne hj

lemma tensor_d_snd_of_eq (i : {i : ℤ × ℤ // i.1 + i.2 = n})
  (x : F.X i.1.1) (y : G.X i.1.2) (j) (hj : succ_snd n i = j) :
  tensor_d_snd R F G n i (tensor_product.mk R (F.X i.1.1) (G.X i.1.2) x y) j =
  tensor_product.mk R (F.X j.1.1) (G.X j.1.2)
    (eq.rec ((-1 : ℤ)^(int.nat_abs i.1.1) • x) $ show i.1.1 = j.1.1, by rw ←hj; refl)
    (eq.rec (G.d i.1.2 y) $ show i.1.2.succ = j.1.2, by rw ←hj; refl) :=
begin
  cases hj,
  convert tensor_d_snd_apply R F G n i x y,
end

lemma succ_fst_succ_snd (i : {i : ℤ × ℤ // i.1 + i.2 = n}) :
  succ_fst n.succ (succ_snd n i) = succ_snd n.succ (succ_fst n i) :=
subtype.ext rfl

lemma tensor_d_squared : (tensor_d R F G n.succ).comp (tensor_d R F G n) = 0 :=
begin
  ext i x y j,
  rw [linear_map.zero_comp, linear_map.zero_apply, linear_map.comp_apply, linear_map.comp_apply],
  erw [direct_sum.to_module_lof, linear_map.add_apply, linear_map.map_add,
    direct_sum.to_module_lof, direct_sum.to_module_lof],
  rw [linear_map.add_apply, linear_map.add_apply],
  repeat {rw tensor_product.map_tmul},
  repeat {rw dfinsupp.add_apply},
  cases classical.em (succ_fst n.succ (succ_fst n i) = j),
  sorry,
  /-have hj1 : succ_fst n.succ (succ_snd n i) ≠ j:= sorry,
  have hj2 : succ_snd n.succ (succ_snd n i) ≠ j := sorry,
  have hj3 : succ_snd n.succ (succ_fst n i) ≠ j := sorry,
  erw dfinsupp.single_eq_of_ne hj1,
  erw dfinsupp.single_eq_of_ne hj2,
  erw dfinsupp.single_eq_of_ne hj3,
  rw add_zero, rw add_zero, rw add_zero, rw ←h, erw tensor_d_fst_apply,
  convert linear_map.map_zero₂ _ _,
  rw ←linear_map.comp_apply,
  convert linear_map.zero_apply _,
  exact F.d_squared _,-/
  cases classical.em (succ_fst n.succ (succ_snd n i) = j) with hj hj,
  have hj1 : succ_snd n.succ (succ_snd n i) ≠ j := sorry,
  erw dfinsupp.single_eq_of_ne h,
  erw dfinsupp.single_eq_of_ne hj1,
  rw zero_add, rw add_zero,
  rw ←hj,
  erw tensor_d_fst_apply,
  erw tensor_d_snd_of_eq _ _ _ _ _ _ _
    (succ_fst n.succ (succ_snd n i)) (succ_fst_succ_snd n i).symm,
  sorry, sorry,
 end

variables {M}

def cochain_complex.tensor_product (F G : cochain_complex (Module R)) :
  cochain_complex (Module R) :=
{ X := λ n, Module.of R (direct_sum ({i : ℤ × ℤ // i.1 + i.2 = n})
    (λ i, tensor_product R (F.X i.1.1) (G.X i.1.2))),
  d := λ n, _, --tensor_d R F G n, -- why does this time out :(
  d_squared' := _,--tensor_d_squared R F G

  }