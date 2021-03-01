import m4r.koszul_of_free

universes u v
variables (R : Type u) [comm_ring R] {M : Type u} [add_comm_group M] [module R M]
open_locale classical

noncomputable def alternating_map.comp_linear_map {M N : Type u} (P : Type u)
  (ι : Type v) [add_comm_group M]
  [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P]
  (f : M →ₗ[R] N) (F : alternating_map R N P ι) : alternating_map R M P ι :=
{ map_eq_zero_of_eq' := λ v i j hv hij,
    begin
      dsimp,
      rw F.map_eq_zero_of_eq (λ i, f (v i)) _ hij,
      dsimp,
      rw hv,
    end,
  .. F.to_multilinear_map.comp_linear_map (λ i, f) }

noncomputable def linear_map.comp_alternating_map {M N : Type u} (P : Type u)
  (ι : Type v) [add_comm_group M]
  [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P]
  (f : N →ₗ[R] P) (F : alternating_map R M N ι) : alternating_map R M P ι :=
{ map_eq_zero_of_eq' := λ v i j hv hij,
    begin
      dsimp,
      rw [F.map_eq_zero_of_eq _ hv hij, linear_map.map_zero]
    end,
  .. f.comp_multilinear_map F.to_multilinear_map }

variables {R}

@[simp] lemma alternating_map.comp_linear_map_apply {M N P : Type u} {ι : Type v} [add_comm_group M]
  [add_comm_group N] [add_comm_group P] [module R M] [module R N] [module R P]
  (f : M →ₗ[R] N) (F : alternating_map R N P ι) (x : ι → M) :
  F.comp_linear_map R _ _ f x = F (f ∘ x) :=
rfl

variables (R)

def Koszul.congr (x : M) (m n : ℤ) (h : m = n) : (Koszul R M x).X m ≃ₗ[R] (Koszul R M x).X n :=
{ to_fun := λ x, eq.rec x h,
  map_add' := λ x y, by cases h; refl,
  map_smul' := λ r x, by cases h; refl,
  inv_fun := λ x, eq.rec x h.symm,
  left_inv := λ x, by cases h; refl,
  right_inv := λ x, by cases h; refl }

def fin0_to_alternating (x : R) :
  alternating_map R M R (fin 0) :=
{ map_eq_zero_of_eq' := λ v i, fin.elim0 i,
  ..tpow.fin0_to_multilinear R M x }

variables (M)
def epow.zero_isom :
  epow R M 0 ≃ₗ[R] R :=
{ to_fun := epow_lift R $ fin0_to_alternating R 1,
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := submodule.mkq _,
  left_inv := λ x,
    begin
      refine quotient.induction_on' x _,
      intro y,
      erw submodule.liftq_apply,
      unfold tpow.lift,
      rw [tpow.to_span_singleton_apply, algebra.id.smul_eq_mul, submodule.mkq_apply],
      congr,
      exact mul_one _,
    end,
  right_inv := λ x,
    begin
      erw submodule.liftq_apply,
      unfold tpow.lift,
      rw [tpow.to_span_singleton_apply, algebra.id.smul_eq_mul],
      exact mul_one _
    end }

def multilinear_map.of_fin_one {N : Type u}
  [add_comm_group N] [module R N] (f : M →ₗ[R] N) : multilinear_map R (λ (i : fin 1), M) N :=
{ to_fun := λ x, f (x $ default (fin 1)),
  map_add' := λ m i x y, by rw subsingleton.elim i (default (fin 1)); simp only
    [function.update_same, f.map_add],
  map_smul' := λ m i r x, by rw subsingleton.elim i (default (fin 1)); simp only
    [function.update_same, f.map_smul], }

def alternating_map.of_fin_one {N : Type u}
  [add_comm_group N] [module R N] (f : M →ₗ[R] N) : alternating_map R M N (fin 1) :=
{ map_eq_zero_of_eq' := λ v i j hv hij, false.elim $ hij $ subsingleton.elim _ _,
  ..multilinear_map.of_fin_one R M f }

def epow.one_isom :
  epow R M 1 ≃ₗ[R] M :=
{ to_fun := epow_lift R $ alternating_map.of_fin_one R M linear_map.id,
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := (epow_ker R M 1).mkq.comp (tensor_product.lid R M).symm.to_linear_map,
  left_inv :=
    begin
      intro y,
      refine quotient.induction_on' y _,
      intro a,
      refine tensor_product.induction_on a _ _ _,
      { simp only [linear_map.map_zero, submodule.quotient.mk'_eq_mk,
          submodule.quotient.mk_zero], },
      { intros r x,
        simp only [submodule.quotient.mk'_eq_mk, to_linear_map_apply,
          submodule.mkq_apply, tensor_product.lid_symm_apply, linear_map.comp_apply],
        congr' 1,
        rw @tpow.mk_one_fin R _ M _ _ (r : R) x,
        erw epow_lift_mk,
        refl },
      { intros x y hx hy,
        show (epow_ker R M 1).mkq.comp _ ((epow_lift R
          (alternating_map.of_fin_one R M linear_map.id)) (submodule.mkq _ (x + y)))
            = submodule.mkq _ (x + y),
        simp only [linear_map.map_add, linear_map.add_apply],
        erw [hx, hy],
        refl }
    end,
  right_inv :=
    begin
      intro y,
      dsimp,
      rw tpow.mk_one_fin,
      erw epow_lift_mk,
      simp only [one_smul],
      refl,
    end }

lemma epow.ext {N : Type u} [add_comm_group N] [module R N] {n : ℕ}
  (f g : epow R M n →ₗ[R] N)
  (h : ∀ (x : fin n → M), f (epow.mk R M n x) = g (epow.mk R M n x)) :
  f = g :=
begin
  ext,
  refine quotient.induction_on' x _,
  intro y,
  have := tpow.ext R M (f.comp $ submodule.mkq _) (g.comp $ submodule.mkq _) h,
  rw linear_map.ext_iff at this,
  exact this _,
end

def epow.ring_isom_zero (n : ℕ) :
  epow R R n.succ.succ ≃ₗ[R] punit :=
{ to_fun := (0 : epow R R n.succ.succ →ₗ[R] punit),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := (0 : punit →ₗ[R] epow R R n.succ.succ),
  left_inv := λ x,
    begin
      refine quotient.induction_on' x _,
      intro y,
      rcases exists_sum_of_tpow R R y with ⟨s, rfl⟩,
      simp only [linear_map.zero_apply],
      show _ = submodule.mkq _ _,
      rw map_sum,
      simp only [linear_map.map_smul],
      refine (multiset.sum_eq_zero _ _).symm,
      intros y hy,
      rw multiset.mem_map at hy,
      rcases hy with ⟨z, hzm, hz⟩,
      rw ←hz,
      convert smul_zero _,
      show epow.mk _ _ _ _ = 0,
      have hz2 : z.2 = (λ i, z.2 i • 1),
      { ext j,
        rw [algebra.id.smul_eq_mul, mul_one] },
      rw [hz2],
      erw multilinear_map.map_smul_univ,
      convert smul_zero _,
      refine (epow.mk R R _).map_eq_zero_of_eq _ rfl fin.zero_ne_one,
    end,
  right_inv := λ x, subsingleton.elim _ _ }

def smul_cx_isom_aux (x : R) : Π (i : ℤ),
  (smul_cx R x).X i ≅ (Koszul R R x).X i
| 0 := (epow.zero_isom R R).symm.to_Module_iso
| 1 := (epow.one_isom R R).symm.to_Module_iso
| (int.of_nat (n + 2)) := (epow.ring_isom_zero R n).symm.to_Module_iso
| -[1+ n] := category_theory.iso.refl _

lemma tpow_zero_mk (y : R) :
  y = y • tpow.mk R M 0 (default (fin 0 → M)) :=
begin
  unfold tpow.mk,
  rw algebra.id.smul_eq_mul,
  rw mul_one,
end

def smul_cx_isom (x : R) :
  (smul_cx R x) ≅ (Koszul R R x) :=
{ hom :=
  { f := λ i, (smul_cx_isom_aux R x i).hom,
    comm' :=
      begin
        ext n y,
        induction n with n n,
        { induction n with n hn,
          { simp only [function.comp_app, category_theory.pi.comp_apply, Module.coe_comp],
            show (epow.one_isom R R).symm (x • (y : R)) = wedge_d R x 0 ((epow_ker R R 0).mkq y),

            erw linear_map.comp_apply,
            rw to_linear_map_apply,
            rw tensor_product.lid_symm_apply,
            rw tensor_product.tmul_smul,
            rw tensor_product.smul_tmul',
            rw algebra.id.smul_eq_mul,
            rw mul_one,
            --have hy : (epow_ker R R 0).mkq y = y • epow.mk R R 0 (default (fin 0 → R))

            sorry },
            { sorry }},
        { sorry },
      end },
  inv :=
  { f := λ i, (smul_cx_isom_aux R x i).inv,
    comm' :=
      begin
        ext n y,
        dsimp,
          sorry,
      end },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def tensor_Koszul_isom_prod (x : R) (y : M) (i : ℤ) :
  (cochain_complex.tensor_product R (Koszul R R x) (Koszul R M y)).X i ≅
  Module.of R ((Koszul R M y).X i × (Koszul R M y).X i.pred) :=
{ hom := direct_sum.to_module R _ _ $ λ j, subtype.rec_on j $ λ j, prod.rec_on j $ λ j k,
    by dsimp; exact
    int.rec_on j (λ j, nat.rec_on j (λ Hj, (linear_map.inl R _ ((Koszul R M y).X i.pred)).comp
    ((Koszul.congr R y k i (zero_add k ▸ Hj)).to_linear_map.comp
      ((tensor_product.lid R _).to_linear_map.comp (linear_map.rtensor ((Koszul R M y).X k)
        (epow.zero_isom R R).to_linear_map))))
    (λ j, nat.rec_on j (λ hj Hj, (linear_map.inr R ((Koszul R M y).X i)
      ((Koszul R M y).X i.pred)).comp ((Koszul.congr R y k i.pred (by
      simp only [int.pred, add_comm _ k, zero_add] at Hj;
      rw ←Hj; simp only [int.pred, int.coe_nat_zero, int.coe_nat_succ, int.of_nat_eq_coe,
          add_sub_cancel, zero_add])).to_linear_map.comp
      ((tensor_product.lid R _).to_linear_map.comp (linear_map.rtensor ((Koszul R M y).X k)
        (epow.one_isom R R).to_linear_map))))
    (λ l hl h h', 0))) (λ j hj, 0),
  inv := linear_map.coprod ((direct_sum.lof R _ _ (⟨(0, i), zero_add i⟩ :
    {j : ℤ × ℤ // j.1 + j.2 = i})).comp
   ((linear_map.rtensor ((Koszul R M y).X i) (epow.zero_isom R R).symm.to_linear_map).comp $
   (tensor_product.lid _ _).symm.to_linear_map)) $
   (direct_sum.lof R _ _ (⟨(1, i.pred), add_sub_cancel'_right 1 i⟩ :
     {j : ℤ × ℤ // j.1 + j.2 = i})).comp
     ((linear_map.rtensor ((Koszul R M y).X i.pred) (epow.one_isom R R).symm.to_linear_map).comp $
        (tensor_product.lid _ _).symm.to_linear_map),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def Koszul_isom_prod {n : ℕ} (x : fin n.succ → R) (i : ℤ) :
  (Koszul R (fin n.succ → R) x).X i ≅ Module.of R ((Koszul R (fin n → R) (fin.init x)).X i
    × (Koszul R (fin n → R) (fin.init x)).X i.pred) :=
{ hom := int.rec_on i (λ i, nat.rec_on n _ _) (λ i, 0),
  inv := _,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def Koszul_succ_isom_aux {n : ℕ} (x : fin n.succ → R) (i : ℤ) :
  (Koszul R (fin n.succ → R) x).X i ≅ (cochain_complex.tensor_product R
    (Koszul R R (x n)) (Koszul R (fin n → R) (fin.init x))).X i :=
{ hom := _,
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }
