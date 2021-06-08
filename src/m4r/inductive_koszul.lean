import m4r.total_complex data.matrix.basic

universes u v w

open_locale classical

variables (R : Type u) [comm_ring R]
{F : cochain_complex ℤ (Module.{u} R)}

def smul_complex_X : ℤ → Module.{u} R
| 0 := Module.of R R
| 1 := Module.of R R
| (int.of_nat n) := Module.of R punit
| -[1+ n] := Module.of R punit

variables {R}

def smul_complex_d (x : R) : Π i : ℤ, smul_complex_X R i ⟶ smul_complex_X R (i + 1)
| 0 := linear_map.lsmul R R x
| (int.of_nat n) := 0
| -[1+ n] := 0

theorem smul_complex_d_squared (x : R) (i : ℤ) :
  (smul_complex_d x (i + 1)).comp (smul_complex_d x i) = 0 :=
int.rec_on i (λ j, linear_map.zero_comp _) (λ j, linear_map.comp_zero _)

variables (R)

/-- The complex `0 → R →(•x) R → 0`. -/
def smul_complex (x : R) : cochain_complex ℤ (Module.{u} R) :=
cochain_complex.mk' (smul_complex_X R) (smul_complex_d x) (smul_complex_d_squared x)

def inductive_Koszul : Π (n : ℕ) (x : fin n.succ → R),
  cochain_complex ℤ (Module.{u} R)
| 0 x := smul_complex R (x 0)
| (n + 1) x := cochain_complex.total R
  (smul_complex R (x n.succ)) (inductive_Koszul n (fin.init x))

def punit_equiv_of_subsingleton (M : Type u) [add_comm_group M]
  [module R M] [subsingleton M] : M ≃ₗ[R] punit :=
{ inv_fun := (0 : punit →ₗ[R] M),
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _,
  ..(0 : M →ₗ[R] punit) }

def tensor_product.punit_left (M : Type u) [add_comm_group M]
  [module R M] : tensor_product R punit M ≃ₗ[R] punit :=
{ to_fun := tensor_product.lift 0,
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := (tensor_product.mk R punit M).flip 0,
  left_inv := λ x, tensor_product.induction_on x (by simp only [linear_map.map_zero])
    (by intros x y; rw [subsingleton.elim x 0, tensor_product.zero_tmul];
      simp only [linear_map.map_zero])
    (λ x y hx hy, by simp only [linear_map.map_add, hx, hy]),
  right_inv := λ x, subsingleton.elim _ _, ..tensor_product.lift 0 }

def tensor_product.punit_right (M : Type u) [add_comm_group M]
  [module R M] : tensor_product R M punit ≃ₗ[R] punit :=
(tensor_product.comm R M punit).trans $ tensor_product.punit_left R M

instance tensor_product.subsingleton_left {M : Type u} {N : Type u}
  [add_comm_group M] [add_comm_group N]
  [module R M] [module R N] [subsingleton M] : subsingleton (tensor_product R M N) :=
equiv.subsingleton ((tensor_product.congr (punit_equiv_of_subsingleton R _)
  (linear_equiv.refl R _)).trans (tensor_product.punit_left R _)).to_equiv

instance tensor_product.subsingleton_right {M : Type u} {N : Type u}
  [add_comm_group M] [add_comm_group N]
  [module R M] [module R N] [subsingleton N] : subsingleton (tensor_product R M N) :=
equiv.subsingleton ((tensor_product.congr (linear_equiv.refl R _)
  (punit_equiv_of_subsingleton R _)).trans (tensor_product.punit_right R _)).to_equiv

instance direct_sum.subsingleton {ι : Type v} (M : ι → Type u) [Π i, add_comm_monoid (M i)]
  [Π i, subsingleton (M i)] : subsingleton (direct_sum ι M) :=
begin
  constructor,
  intros,
  ext,
  exact subsingleton.elim _ _,
end

instance subsingleton_inductive_Koszul_neg (n j : ℕ) (x : fin n.succ → R) :
  subsingleton ((inductive_Koszul R n x).X (-[1+ j])) :=
begin
  revert j,
  induction n with n hn,
  { intro j,
    show subsingleton (Module.of R punit),
    apply_instance },
  { intro j,
    apply direct_sum.subsingleton _,
    rintros ⟨⟨i1, i2⟩, hi⟩,
    induction i1 with i1 i1,
    { convert tensor_product.subsingleton_right _,
      have : i2 = -[1+ (j + i1)] :=
      begin
        rw ←eq_sub_iff_add_eq' at hi,
        simp only [int.of_nat_eq_coe] at hi,
        rw [hi, int.neg_succ_of_nat_coe', int.neg_succ_of_nat_coe'],
        simp only [int.coe_nat_add, neg_add_rev],
        ring,
      end,
      simp only,
      rw this,
      exact hn _ _ },
    { convert tensor_product.subsingleton_left _,
      show subsingleton (Module.of R punit),
      apply_instance }},
end

lemma subsingleton_inductive_Koszul_neg' {n : ℕ} (j : ℤ) {x : fin n.succ → R} (hj : j < 0) :
  subsingleton ((inductive_Koszul R n x).X j) :=
@equiv.subsingleton _ _ (category_theory.eq_to_iso $ congr_arg _ $
show j = -[1+ (int.nat_abs (j + 1))],
begin
  induction j with j j,
  { exfalso,
    linarith [int.of_nat_nonneg j] },
  { induction j with j hj,
    { congr },
    { congr }},
end).to_linear_equiv.to_equiv
(subsingleton_inductive_Koszul_neg R _ _ _)

lemma subsingleton_smul_complex (j : ℤ) (x : R) (hj : ¬(j = 0 ∨ j = 1)) :
  subsingleton ((smul_complex R x).X j) :=
begin
  induction j with j j,
  { induction j with j hj,
    { contrapose! hj,
      exact or.inl rfl },
    { induction j with j hj',
      { contrapose! hj,
        exact or.inr rfl },
      { show subsingleton (Module.of R punit), by apply_instance }}},
  { exact subsingleton_inductive_Koszul_neg R 0 j (λ i, x) }
end

def of_fin_one_equiv : (fin 1 → R) ≃ₗ[R] R :=
{ to_fun := λ f, f 0,
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ r x, r,
  left_inv := λ x, funext $ λ i, subsingleton.elim i 0 ▸ rfl,
  right_inv := λ x, rfl }

variables (n : ℕ)

@[simp] lemma to_linear_map_apply {M N : Type u} [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] (f : M ≃ₗ[R] N) (x : M) :
  f.to_linear_map x = f x := rfl

lemma direct_sum.component.lof_ne {ι : Type v} [dec_ι : decidable_eq ι]
  {M : ι → Type w} [Π i, add_comm_monoid (M i)] [Π i, semimodule R (M i)]
  {i j : ι} (h : j ≠ i) (b : M j) :
  direct_sum.component R ι M i ((direct_sum.lof R ι M j) b) = 0 :=
dfinsupp.single_eq_of_ne h

open_locale classical

lemma comp_symm_hom (A B : Module R) (F : A ≅ B) :
  linear_map.comp F.symm.hom F.hom = linear_map.id :=
begin
  ext,
  simp only [category_theory.coe_hom_inv_id, linear_map.id_coe, id.def, category_theory.iso.symm_hom, linear_map.comp_apply],
end

lemma to_linear_map_comp {M : Type u} {N : Type u} {P : Type u}
  [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [module R M] [module R N] [module R P]
  (f : M ≃ₗ[R] N) (g : N ≃ₗ[R] P) :
  g.to_linear_map.comp f.to_linear_map = (f.trans g).to_linear_map :=
linear_map.ext $ λ x, rfl

lemma comp_symm_to_linear_map {M N : Type u} [add_comm_group M] [add_comm_group N]
  [module R M] [module R N] (f : M ≃ₗ[R] N) :
  f.symm.to_linear_map.comp f.to_linear_map = linear_map.id :=
by rw [to_linear_map_comp, f.trans_symm]; refl

variables (ι : Type v) [dec_ι : decidable_eq ι]

def inductive_Koszul_zero {n : ℕ} : Π (x : fin n.succ → R),
  (inductive_Koszul R n x).X 0 ≃ₗ[R] R :=
nat.rec_on n (λ x, linear_equiv.refl _ _) $ λ n fn x,
linear_equiv.of_linear
((fn (fin.init x)).to_linear_map.comp  (linear_map.comp (tensor_product.lid R
  ((inductive_Koszul R n (fin.init x)).X 0)).to_linear_map
  (direct_sum.component R (int_pair 0) _
   (int_pair_mk 0 0 0 $ zero_add _) : (inductive_Koszul R n.succ x).X 0
     →ₗ[R] tensor_product R (Module.of R R) ((inductive_Koszul R n (fin.init x)).X 0))))
((direct_sum.lof R _ _ (int_pair_mk 0 0 0 $ zero_add _)).comp $
    (tensor_product.lid R _).symm.to_linear_map.comp (fn _).symm.to_linear_map)
  (begin
      ext,
      dsimp,
      simp only [linear_map.comp_apply, ←tensor_product.lid_symm_apply],
      erw [direct_sum.component.lof_self, linear_equiv.apply_symm_apply,
        linear_equiv.apply_symm_apply],
      refl,
    end)
  (begin
    show linear_map.comp _ _ = _,
    rw [linear_map.comp_assoc, linear_map.comp_assoc],
    conv_lhs {congr, skip, congr, skip, rw [←linear_map.comp_assoc, comp_symm_to_linear_map, linear_map.id_comp]},
    conv_lhs {congr, skip, rw [←linear_map.comp_assoc, to_linear_map_comp]},
    erw linear_equiv.trans_symm,
    ext1 i,
    refine tensor_product.ext _,
    intros X Y,
    simp only [dfinsupp.lsingle_apply, Module.id_apply, linear_map.comp_apply],
    rcases classical.em (i = int_pair_mk 0 0 0 (zero_add _)) with ⟨rfl, h⟩,
    { erw [direct_sum.component.lof_self],
      refl },
    { erw direct_sum.component.lof_ne R h,
      erw linear_map.map_zero,
      suffices : X ⊗ₜ[R] Y = 0, by rw [this, dfinsupp.single_zero]; refl,
      refine decidable.lt_by_cases i.1.1 0 (λ H, _) (λ H, _) (λ H, _),
      { rw [@subsingleton.elim _ (@subsingleton_inductive_Koszul_neg' R _ 0 i.1.1 (λ k, x n.succ) H) X 0,
        tensor_product.zero_tmul] },
      { contrapose! h,
        rw [int_pair_ext_iff_fst, H],
        refl },
      { have : i.1.2 < 0 := by {rw ←int_pair_snd_eq_sub i, linarith},
        rw [@subsingleton.elim _ (@subsingleton_inductive_Koszul_neg' R _ n i.1.2 (fin.init x) this) Y 0,
        tensor_product.tmul_zero] }}
  end)

def equiv_punit_of_rk_eq_zero (i : ℕ) (hi : i = 0) :
  (fin i → R) ≃ₗ[R] punit :=
{ to_fun := (0 : (fin i → R) →ₗ[R] punit),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := (0 : punit →ₗ[R] (fin i → R)),
  left_inv := λ x, funext $ λ j, by have := (fin.cast hi j); exact fin.elim0 this,
  right_inv := λ x, subsingleton.elim _ _ }

def equiv_ring_of_rk_eq_one (i : ℕ) (hi : i = 1) :
  (fin i → R) ≃ₗ[R] R :=
{ to_fun := λ f, f (fin.cast hi.symm 0),
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ r j, r,
  left_inv := λ x, begin
      dsimp,
      ext j,
      cases hi,
      congr,
    end,
  right_inv := λ x, rfl }

def equiv_of_eq_rk (i j : ℕ) (h : i = j) :
  (fin i → R) ≃ₗ[R] (fin j → R) :=
{ to_fun := λ f, f ∘ fin.cast h.symm,
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ f, f ∘ fin.cast h,
  left_inv := λ x, funext $ λ j,
    begin
      dsimp,
      congr,
      ext,
      refl,
    end,
  right_inv := λ x, funext $ λ j,
    begin
      dsimp,
      congr,
      ext,
      refl,
    end, }

def smul_complex_prod (F : cochain_complex ℤ (Module R)) (x : R) (i : ℤ) :
  (cochain_complex.total R (smul_complex R x) F).X i ≃ₗ[R] F.X i × (F⟦-1⟧).X i :=
{ to_fun := @linear_map.prod R ((cochain_complex.total R (smul_complex R x) F).X i)
      (F.X i) ((F⟦-1⟧).X i) _ _ _ _ _ _ _ ((tensor_product.lid R _).to_linear_map.comp
    (direct_sum.component R (int_pair i) _ (int_pair_mk i 0 i $ zero_add _) :
      (cochain_complex.total R (smul_complex R x) F).X i →ₗ[R] tensor_product R
        (Module.of R R) (F.X i)))
    ((tensor_product.lid R _).to_linear_map.comp (direct_sum.component R _ _ (int_pair_mk i 1 (i-1)
      $ add_sub_cancel'_right _ _))),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := @linear_map.coprod R (F.X i) ((F⟦-1⟧).X i)
      ((cochain_complex.total R (smul_complex R x) F).X i) _ _ _ _ _ _ _
    ((direct_sum.lof R (int_pair i) _ (int_pair_mk i 0 i $ zero_add _)).comp
      (tensor_product.lid R (F.X i)).symm.to_linear_map)
    ((direct_sum.lof R (int_pair i) _ (int_pair_mk i 1 (i-1) $ add_sub_cancel'_right _ _)).comp
      (tensor_product.lid R ((F⟦-1⟧).X i)).symm.to_linear_map),
  left_inv := λ y,
    begin
      refine direct_sum.linduction_on R y _ _ _,
      { simp only [linear_map.map_zero] },
      { sorry /-intros j z,
        dsimp,
        rcases classical.em (j = int_pair_mk i 0 i (zero_add _)) with ⟨rfl, _⟩,
        { convert add_zero _,
          { convert linear_map.map_zero _,
            convert tensor_product.tmul_zero _ _ },
          { rw [linear_equiv.symm_apply_apply],
            sorry -- lean is being a dickhead
            }},
        { rcases classical.em (j = int_pair_mk i 1 (i-1) (add_sub_cancel'_right _ _)) with ⟨rfl, _⟩,
          { convert zero_add _,
            { convert linear_map.map_zero _,
              convert tensor_product.tmul_zero _ _, },
            { rw [linear_equiv.symm_apply_apply],
              erw direct_sum.component.lof_self, }
              },
          { rw @subsingleton.elim _ (@tensor_product.subsingleton_left R _ _ _ _ _ _ _ $
              subsingleton_smul_complex R j.1.1 _ (λ hnot,
              begin
                cases hnot with h0 h1,
                { contrapose! h,
                  exact int_pair_ext_iff_fst.2 h0 },
                { contrapose! h_1,
                  exact int_pair_ext_iff_fst.2 h1 }
              end)) z 0,
              simp only [linear_map.map_zero, tensor_product.tmul_zero,
                linear_equiv.map_zero, zero_add]
                }}
               -/ },
      { intros w z hw hz,
        simp only [to_linear_map_apply, linear_map.coprod_apply, linear_equiv.map_add,
          tensor_product.lid_symm_apply, zero_add, linear_map.prod_apply, linear_map.map_add,
          linear_map.comp_apply] at hw hz ⊢,
        rw [hw, hz], },
    end,
  right_inv := λ y,
  begin
    erw linear_map.coprod_apply,
    rw linear_map.map_add,
    ext,
    { simp only [add_right_eq_self, prod.mk_add_mk, linear_equiv.map_eq_zero_iff,
        to_linear_map_apply, one_smul, tensor_product.lid_tmul, direct_sum.component.lof_self,
        tensor_product.lid_symm_apply, linear_map.prod_apply, linear_map.comp_apply],
      erw direct_sum.component.lof_ne,
      exact (λ H, one_ne_zero (int_pair_ext_iff_fst.1 H)) },
    { simp only [add_left_eq_self, prod.mk_add_mk, linear_equiv.map_eq_zero_iff,
        to_linear_map_apply, one_smul, tensor_product.lid_tmul, direct_sum.component.lof_self,
        tensor_product.lid_symm_apply, linear_map.prod_apply, linear_map.comp_apply],
      erw direct_sum.component.lof_ne,
      exact (λ H, zero_ne_one (int_pair_ext_iff_fst.1 H)) }
  end}

def inductive_Koszul_prod {n : ℕ} (i : ℕ) (x : fin n.succ.succ → R) :
  (inductive_Koszul R n.succ x).X i.succ ≃ₗ[R]
  ((inductive_Koszul R n (fin.init x)).X i.succ × (inductive_Koszul R n (fin.init x)).X i) :=
(smul_complex_prod R (inductive_Koszul R n (fin.init x)) (x n.succ) i.succ).trans
$ linear_equiv.prod (linear_equiv.refl _ _)
  (category_theory.eq_to_iso $ congr_arg (inductive_Koszul R n (fin.init x)).X $
    show (i.succ : ℤ) - 1 = i, by norm_num).to_linear_equiv

def rk_free_prod_eq_add (i j : ℕ) :
  ((fin i → R) × (fin j → R)) ≃ₗ[R] (fin (i + j) → R) :=
{ to_fun := λ f, fin.append rfl f.1 f.2,
  map_add' := λ f g, fin.append_add rfl f.1 g.1 f.2 g.2,
  map_smul' := λ r f, by simp only [fin.append_smul rfl, prod.smul_snd, prod.smul_fst],
  inv_fun := λ f, (f ∘ fin.cast_add j, f ∘ @fin.nat_add i j),
  left_inv := λ x,
    begin
      ext k,
      { convert fin.append_apply_fst' x.1 x.2 rfl k },
      { ext k,
        convert fin.append_apply_snd' x.1 x.2 rfl _ },
    end,
  right_inv := λ x,
    begin
      ext k,
      dsimp,
      cases classical.em ((k : ℕ) < i),
      { rw [fin.append_apply_fst _ _ _ _ h, function.comp_app],
        congr,
        ext,
        refl, },
      { rw [fin.append_apply_snd _ _ _ _ h, function.comp_app],
        congr,
        ext,
        simp only [fin.coe_nat_add, fin.coe_mk],
        rw nat.add_sub_cancel' (not_lt.1 h), }
    end }

def inductive_Koszul_isom_choose {n : ℕ} : Π (i : ℕ) (x : fin n.succ → R),
  (inductive_Koszul R n x).X i ≅ Module.of R (fin (n.succ.choose i) → R) :=
nat.rec_on n
(λ i x, nat.rec_on i (of_fin_one_equiv R).symm.to_Module_iso
    (λ j fj, nat.rec_on j (of_fin_one_equiv R).symm.to_Module_iso (λ k fk,
    (equiv_punit_of_rk_eq_zero R (nat.choose 1 k.succ.succ)
      (nat.choose_eq_zero_of_lt (by omega))).symm.to_Module_iso)))
  (λ m fm i, nat.rec_on i (λ x, ((inductive_Koszul_zero R x).trans
    (of_fin_one_equiv R).symm).to_Module_iso)
  ((λ k hk x,
    ((inductive_Koszul_prod R k x).trans
     (linear_equiv.trans
  (linear_equiv.prod (fm k.succ (fin.init x)).to_linear_equiv
    (fm k (fin.init x)).to_linear_equiv)
  (((rk_free_prod_eq_add R _ _).trans (equiv_of_eq_rk R _ _ (add_comm _ _)))))).to_Module_iso)))
