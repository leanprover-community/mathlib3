import m4r.cx

universes u v
variables {R : Type u} [comm_ring R]
(F : cochain_complex.{u u+1} (Module.{u u} R))
/-
def cx_cast (j k : ℤ) (h : j = k) : F.X j ⟶ F.X k :=
{ to_fun := λ x, eq.rec x h,
  map_add' := λ x y, by cases h; refl,
  map_smul' := λ x r, by cases h; refl }

lemma cast_d_cast_eq_d (j k : ℤ) (h : j = k) (x : F.X j) :
  (cx_cast F _ _ h ≫ F.d k ≫ cx_cast F _ _ ((add_left_inj _).2 h.symm)) x = F.d j x :=
begin
  cases h,
  refl,
end

lemma cast_d_eq_d_cast (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h) ≫ F.d k) x = (F.d j ≫ cx_cast F _ _ ((add_left_inj _).2 h)) x :=
begin
  cases h,
  refl,
end

lemma d_squared_cast (j k : ℤ) (h : j + 1 = k) (x : F.X j) :
    (F.d j ≫ cx_cast F (j + 1) k (h ▸ rfl) ≫ F.d k) x = 0 :=
begin
  have := (cast_d_eq_d_cast F (j + 1) k h (F.d j x)).symm,
  simp only [function.comp_app, Module.coe_comp] at *,
  erw ←this,
  erw linear_map.ext_iff.1 (F.d_squared j),
  rw linear_map.zero_apply, rw linear_map.map_zero,
end

lemma shift_d_squared (j k : ℤ) (x : F.X (j - k)) :
  (F.d (j - k) ≫ cx_cast F (j - k + 1) (j + 1 - k) (sub_add_eq_add_sub _ _ _)
    ≫ F.d (j + 1 - k) ≫
  cx_cast F (j + 1 - k + 1) (j + 1 + 1 - k)
    (by conv_rhs {rw ←sub_add_eq_add_sub}; refl)) x = 0 :=
begin
  have := d_squared_cast F (j - k) (j + 1 - k) (sub_add_eq_add_sub _ _ _) x,
  simp only [function.comp_app, Module.coe_comp] at *,
  erw this,
  rw linear_map.map_zero,
end

def shift (F : cochain_complex.{u u+1} (Module.{u u} R)) (i : ℤ) :
  cochain_complex (Module R) :=
{ X := λ m, F.X (m - i),
  d := λ m, F.d (m - i) ≫ cx_cast F (m - i + 1) (m + 1 - i) (sub_add_eq_add_sub _ _ _),
  d_squared' := by {ext m y,  exact shift_d_squared _ _ _ _ } }
-/
variables (R)

def smul_cx_X : ℤ → Module.{u u} R
| 0 := Module.of R R
| 1 := Module.of R R
| (int.of_nat n) := Module.of R punit
| -[1+ n] := Module.of R punit

variables {R}

def smul_cx_d (x : R) : Π i : ℤ, smul_cx_X R i ⟶ smul_cx_X R (i + 1)
| 0 := linear_map.lsmul R R x
| (int.of_nat n) := 0
| -[1+ n] := 0

theorem smul_cx_d_squared (x : R) (i : ℤ) :
  smul_cx_d x i ≫ smul_cx_d x (i + 1) = 0 :=
int.rec_on i (λ j, linear_map.zero_comp _) (λ j, linear_map.comp_zero _)

variables (R)

def smul_cx (x : R) : cochain_complex.{u u+1} (Module.{u u} R) :=
{ X := smul_cx_X R,
  d := smul_cx_d x,
  d_squared' := by ext1 i; exact smul_cx_d_squared x i }

def free_Koszul : Π (n : ℕ) (x : fin n.succ → R),
  cochain_complex.{u u+1} (Module.{u u} R)
| 0 x := smul_cx R (x 0)
| (n + 1) x := cochain_complex.tensor_product R
  (smul_cx R (x 0)) (free_Koszul n (fin.init x))

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

instance subsingleton_free_Koszul_neg (n j : ℕ) (x : fin n.succ → R) :
  subsingleton ((free_Koszul R n x).X (-[1+ j])) :=
begin
  revert j,
  induction n with n hn,
  { unfold free_Koszul smul_cx,
    dsimp,
    unfold smul_cx_X,
    apply_instance },
  { unfold free_Koszul cochain_complex.tensor_product,
    simp only [Module.coe_of],
    intro j,
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
      simp only,
      unfold smul_cx,
      simp only,
      unfold smul_cx_X,
      apply_instance }},
end

def Koszul_isom_20 (x : fin 2 → R) :
  (free_Koszul R 1 x).X 0 ≅ Module.of R R :=
{ hom := direct_sum.to_module R _ (Module.of R R) $ λ i,
    subtype.cases_on i $ λ i, prod.cases_on i $ λ i j hij,
    int.cases_on i (λ a, nat.rec_on a (int.cases_on j
      (λ b, nat.rec_on b ((tensor_product.rid R R).to_linear_map)
      (λ c, 0)) (λ b, 0)) (λ b, 0)) (λ a, 0),
  inv := (direct_sum.lof R ({ i : ℤ × ℤ // i.1 + i.2 = 0}) _ (⟨(0, 0), zero_add _⟩)).comp
    (tensor_product.rid R R).symm.to_linear_map,
  hom_inv_id' := by {ext1 i, cases i with i1 i2, cases i1 with i j, induction i with i i,
    induction i with i hi, induction j with j j, induction j with j hj, ext1 x,
      ext,
      rcases classical.em (i = ⟨(0, 0), zero_add _⟩) with ⟨rfl, hi⟩,
      { simp only, dsimp [dfinsupp.lsingle],
      simp only [dfinsupp.single_eq_same],
      erw direct_sum.to_module_lof,
      erw tensor_product.rid_symm_apply,
      erw dfinsupp.single_eq_same,
      erw tensor_product.rid_tmul,
      rw tensor_product.smul_tmul,
      rw algebra.id.smul_eq_mul, rw mul_one },
      simp only, dsimp [dfinsupp.lsingle],
      erw dfinsupp.single_eq_of_ne (ne.symm h),
      erw dfinsupp.single_eq_of_ne (ne.symm h),
      exfalso,
      refine nat.succ_ne_zero j _,
      rw ←zero_add j.succ,
      refine int.of_nat.inj _, exact i2,
      exfalso,
      refine nat.succ_ne_zero j (int.of_nat.inj (neg_eq_zero.1 _)),
      rw ←zero_add (-(int.of_nat j.succ)),
      exact i2,
      refine sub_eq_zero.1 _,
      convert linear_map.unique_of_left.uniq _,
      have : j = -[1+ i] := (add_eq_zero_iff_neg_eq.1 i2).symm,
      simp only,dsimp, rw this,
      apply tensor_product.subsingleton_right _,
      exact subsingleton_free_Koszul_neg R 0 i _,
      refine sub_eq_zero.1 _,
      convert linear_map.unique_of_left.uniq _,
      apply tensor_product.subsingleton_left _,
      unfold smul_cx,
      simp only,
      unfold smul_cx_X,
      apply_instance},
  inv_hom_id' := by {
     ext,
     simp only,
     dsimp,
     rw direct_sum.to_module_lof,
     erw tensor_product.rid_symm_apply,
     erw tensor_product.rid_tmul,
     rw one_smul }  }

def Koszul_isom_21 (x : fin 2 → R) :
  (free_Koszul R 1 x).X 1 ≅ (Module.of R (R × R)) :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def Koszul_isom_22 (x : fin 2 → R) :
  (free_Koszul R 1 x).X 2 ≅ Module.of R R :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def free_Koszul_isom_choose {n : ℕ} (x : fin n.succ → R) (i : ℕ) :
  (free_Koszul R n x).X (int.of_nat i) ≅ Module.of R (fin (n.succ.choose i) → R) :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

variables (n : ℕ)

def free_Koszul_isom_Koszul {n : ℕ} (x : fin n.succ → R) :
  free_Koszul R n x ≅ Koszul R (fin n.succ → R) x :=
{ hom := sorry,
  inv := sorry,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def free_exterior_power (n i : ℕ) :
  epow R (fin n.succ → R) i ≃ₗ[R] (fin (n.succ.choose i) → R) :=
{ to_fun := sorry,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }
