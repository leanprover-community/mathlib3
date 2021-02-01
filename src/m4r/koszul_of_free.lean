import m4r.cx

universes u v
variables {R : Type u} [comm_ring R]
(F : cochain_complex.{u u+1} (Module.{u u} R))

def cx_cast (j k : ℤ) (h : j = k) : F.X j ≅ F.X k :=
{ hom := { to_fun := λ x, eq.rec x h,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  inv := { to_fun := λ x, eq.rec x h.symm,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

@[simp] lemma cast_d_cast_eq_d (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h).hom ≫ F.d k ≫ (cx_cast F _ _ ((add_left_inj _).2 h.symm)).hom) x = F.d j x :=
begin
  cases h,
  refl,
end

@[simp] lemma cast_d_eq_d_cast (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h).hom ≫ F.d k) x = (F.d j ≫ (cx_cast F _ _ ((add_left_inj _).2 h)).hom) x :=
begin
  cases h,
  refl,
end

@[simp] lemma d_squared_cast (j k : ℤ) (h : j + 1 = k) (x : F.X j) :
    (F.d j ≫ (cx_cast F (j + 1) k (h ▸ rfl)).hom ≫ F.d k) x = 0 :=
begin
  have := (cast_d_eq_d_cast F (j + 1) k h (F.d j x)).symm,
  simp only [function.comp_app, Module.coe_comp] at *,
  erw [←this, linear_map.ext_iff.1 (F.d_squared j)],
  rw [linear_map.zero_apply, linear_map.map_zero],
end

@[simp] lemma shift_d_squared (j k : ℤ) (x : F.X (j - k)) :
  (F.d (j - k) ≫ (cx_cast F (j - k + 1) (j + 1 - k) (sub_add_eq_add_sub _ _ _)).hom
    ≫ F.d (j + 1 - k) ≫
  (cx_cast F (j + 1 - k + 1) (j + 1 + 1 - k)
    (by conv_rhs {rw ←sub_add_eq_add_sub}; refl)).hom) x = 0 :=
begin
  have := d_squared_cast F (j - k) (j + 1 - k) (sub_add_eq_add_sub _ _ _) x,
  simp only [function.comp_app, Module.coe_comp] at *,
  erw this,
  rw linear_map.map_zero,
end

def shift (F : cochain_complex.{u u+1} (Module.{u u} R)) (i : ℤ) :
  cochain_complex (Module R) :=
{ X := λ m, F.X (m - i),
  d := λ m, F.d (m - i) ≫ (cx_cast F (m - i + 1) (m + 1 - i) (sub_add_eq_add_sub _ _ _)).hom,
  d_squared' := by ext m y;  exact shift_d_squared _ _ _ _ }

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
  (smul_cx R (x n.succ)) (free_Koszul n (fin.init x))

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

def hom_aux (x : fin 2 → R) :=
@direct_sum.to_module R _ ({ i : ℤ × ℤ // i.1 + i.2 = 0}) _
  (λ i, tensor_product R ((smul_cx R (x 1)).X i.1.1) ((smul_cx R (x 0)).X i.1.2)) _ _
     (Module.of R R) _ _ $ λ i,
    subtype.cases_on i $ λ i', prod.cases_on i' $ λ i j,
    int.cases_on i (λ a, nat.rec_on a (int.cases_on j
      (λ b, nat.rec_on b (λ hij, (tensor_product.rid R R).to_linear_map)
      (λ c hij' hij, 0)) (λ b hij', 0)) (λ b hij' hij, 0)) (λ a hij, 0)

def Koszul_isom_20 (x : fin 2 → R) :
  (free_Koszul R 1 x).X 0 ≅ Module.of R R :=
{ hom := @direct_sum.to_module R _ ({ i : ℤ × ℤ // i.1 + i.2 = 0}) _
  (λ i, tensor_product R ((smul_cx R (x 1)).X i.1.1) ((smul_cx R (x 0)).X i.1.2)) _ _
     (Module.of R R) _ _ $ λ i, subtype.cases_on i $ λ i', prod.cases_on i' $ λ i j,
    int.cases_on i (λ a, nat.rec_on a (int.cases_on j
      (λ b, nat.rec_on b (λ hij, (tensor_product.rid R R).to_linear_map)
      (λ c hij' hij, 0)) (λ b hij', 0)) (λ b hij' hij, 0)) (λ a hij, 0),
  inv := (direct_sum.lof R ({ i : ℤ × ℤ // i.1 + i.2 = 0}) _ (⟨(0, 0), zero_add _⟩)).comp
    (tensor_product.rid R R).symm.to_linear_map,
  hom_inv_id' :=
    begin
      ext1 i,
      cases i with i1 i2,
      cases i1 with i j,
      induction i with i i,
      { induction i with i hi,
        { induction j with j j,
          { induction j with j hj,
            { ext1 x,
              ext,
              rcases classical.em (i = ⟨(0, 0), zero_add _⟩) with ⟨rfl, hi⟩,
              { simp only,
                dsimp [dfinsupp.lsingle],
                simp only [dfinsupp.single_eq_same],
                erw [direct_sum.to_module_lof, tensor_product.rid_symm_apply,
                    dfinsupp.single_eq_same, tensor_product.rid_tmul],
                rw [tensor_product.smul_tmul, algebra.id.smul_eq_mul, mul_one] },
              { simp only,
                dsimp [dfinsupp.lsingle],
                erw [dfinsupp.single_eq_of_ne (ne.symm h),
                     dfinsupp.single_eq_of_ne (ne.symm h)] }},
            { exfalso,
              refine nat.succ_ne_zero j _,
              rw ←zero_add j.succ,
              exact int.of_nat.inj i2 }},
          { exfalso,
            refine nat.succ_ne_zero j (int.of_nat.inj (neg_eq_zero.1 _)),
            rw ←zero_add (-(int.of_nat j.succ)),
            exact i2 }},
        { refine sub_eq_zero.1 _,
          convert linear_map.unique_of_left.uniq _,
          have : j = -[1+ i] := (add_eq_zero_iff_neg_eq.1 i2).symm,
          simp only,
          dsimp,
          rw this,
          apply tensor_product.subsingleton_right _,
          exact subsingleton_free_Koszul_neg R 0 i _ }},
      { refine sub_eq_zero.1 _,
        convert linear_map.unique_of_left.uniq _,
        apply tensor_product.subsingleton_left _,
        unfold smul_cx,
        simp only,
        unfold smul_cx_X,
        apply_instance },
    end,
  inv_hom_id' :=
    begin
      dsimp,
      ext1,
      erw direct_sum.to_module_lof,
      erw [tensor_product.rid_symm_apply, tensor_product.rid_tmul],
      rw one_smul,
      refl,
    end  }

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

def of_fin_one_equiv : (fin 1 → R) ≃ₗ[R] R :=
{ to_fun := λ f, f 0,
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ r x, r,
  left_inv := λ x, funext $ λ i, subsingleton.elim i 0 ▸ rfl,
  right_inv := λ x, rfl }

instance cochain_complex.acg_hom (F G : cochain_complex.{u u+1} (Module.{u u} R)) :
  add_comm_group (F ⟶ G) :=
{ add := λ f g,
  { f := f.1 + g.1,
    comm' :=
    begin
      ext i x,
      have hf := congr_fun f.comm i,
      have hg := congr_fun g.comm i,
      rw linear_map.ext_iff at hf,
      rw linear_map.ext_iff at hg,
      simp only [pi.add_apply, function.comp_app, category_theory.pi.comp_apply, Module.coe_comp,
        linear_map.add_apply, category_theory.preadditive.add_comp] at *,
      rw [←hf, ←hg],
      refl,
    end },
  add_assoc := λ f g h,
    begin
      ext i x,
      exact add_assoc _ _ _,
    end,
  zero :=
    { f := 0,
      comm' :=
      begin
        ext i x,
        simp only [category_theory.limits.comp_zero, category_theory.limits.zero_comp,
          category_theory.shift_zero_eq_zero],
      end },
  zero_add := λ f,
    begin
      ext i x,
      exact zero_add _,
    end,
  add_zero := λ f,
    begin
      ext i x,
      exact add_zero _,
    end,
  neg := λ f,
    { f := -f.1,
      comm' :=
      begin
        ext i x,
        have := congr_fun f.comm i,
        rw linear_map.ext_iff at this,
        simp only [pi.neg_apply, function.comp_app, category_theory.pi.comp_apply,
          linear_map.neg_apply, Module.coe_comp, category_theory.preadditive.neg_comp] at *,
        rw ←this,
        refl,
      end },
  add_left_neg := λ f,
    begin
      ext i x,
      exact add_left_neg _,
    end,
  add_comm := λ f g,
    begin
      ext i x,
      exact add_comm _ _,
    end, }

instance cochain_complex.module_hom (F G : cochain_complex.{u u+1} (Module.{u u} R)) :
   module R (F ⟶ G) :=
 { smul := λ r f,
     { f := λ i, r • f.1 i,
       comm' :=
       begin
        ext i x,
         have := congr_fun f.comm i,
         rw linear_map.ext_iff at this,
         simp only [linear_map.smul_apply, function.comp_app, category_theory.pi.comp_apply,
           Module.coe_comp, linear_map.map_smul] at *,
         rw ←this,
         refl,
       end },
   one_smul := λ f,
     begin
       ext i x,
       simp only [one_smul],
     end,
   mul_smul := λ r s f,
     begin
       ext i x,
       exact mul_smul _ _ _,
     end,
   smul_add := λ r f g,
     begin
       ext i x,
       exact smul_add _ _ _,
     end,
   smul_zero := λ f,
     begin
       ext i x,
       exact smul_zero _,
     end,
   add_smul := λ r s f,
     begin
       ext i x,
       exact add_smul _ _ _,
     end,
   zero_smul := λ f,
     begin
       ext i x,
      simp only [zero_smul, category_theory.differential_object.zero_f,
         category_theory.graded_object.zero_apply],
     end, }

--lemma extjhjghjf (F G : cochain_complex.{u u+1} (Module.{u u} R))
--  (h : ∀ (i : ℤ), F.X i = G.X i) (hd : ∀ (i : ℤ) (x : F.X i), (eq.rec (F.d i x) (h i.succ) : G.X i.succ) = G.d i (eq.rec x (h i))) :
--  F = G :=

example : 1 = 1 := rfl

attribute [ext] category_theory.differential_object

def linear_equiv.congr {M N : Module R} (h : M = N) : M ≃ₗ[R] N :=
{ to_fun := λ m, eq.rec m h,
  map_add' := λ x y, by cases h; refl,
  map_smul' := λ r x, by cases h; refl,
  inv_fun := λ m, eq.rec m h.symm,
  left_inv := λ x, by cases h; refl,
  right_inv := λ x, by cases h; refl }
/-
def cochain_complex.congr (F G : cochain_complex.{u u+1} (Module.{u u} R))
  (h : ∀ i : ℤ, F.X i = G.X i) : F ≅ G :=
{ hom := { f := λ i, (linear_equiv.congr R (h i)).to_linear_map,
    comm' := by ext j x; {simp only [function.comp_app, category_theory.pi.comp_apply, Module.coe_comp],
    dsimp, unfold linear_equiv.congr, dsimp, have := (h j).rec, } },
  inv := _,
  hom_inv_id' := _,
  inv_hom_id' := _ }
-/
/-
lemma cochain_complex.hext (F G : cochain_complex.{u u+1} (Module.{u u} R))
  (h : ∀ i : ℤ, F.X i = G.X i) (hd : ∀ i : ℤ, F.d i ≫ linear_map.congr R (h i.succ)
  = linear_map.congr R (h i) ≫ G.d i) :
  F = G :=
begin
  tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { ext1, solve_by_elim },
  tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { refl },
  intros a a' ᾰ,
  dsimp at *,
  simp only [heq_iff_eq] at *,
  induction ᾰ,

end-/
/-lemma cochain_complex.hext (F G : cochain_complex.{u u+1} (Module.{u u} R))
  (h : ∀ i : ℤ, F.X i = G.X i) (hd : ∀ i : ℤ, F.d i == G.d i) :
  F = G :=
begin
  tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { ext1, solve_by_elim },
  tactic.ext1 [] {new_goals := tactic.new_goals.all},
  work_on_goal 0 { refl },
  intros a a' ᾰ,
  dsimp at *,
  simp only [heq_iff_eq] at *,
  induction ᾰ,
  solve_by_elim,
end-/

/-
def cochain_complex.hom (F G : cochain_complex.{u u+1} (Module.{u u} R)) :
  cochain_complex (Module R) :=
{ X := λ i,
 ({ X := λ j, Module.of R (shift F (i : ℤ) ⟶ shift G ((i - j) : ℤ)),
    d := λ j,
    { to_fun := λ f,
     { f := λ k, f.hom k ≫ (shift G _).d _,
       comm' := _ },
      map_add' := _,
      map_smul' := _ },
    d_squared' := _ } : cochain_complex (Module R)),
  d := _,
  d_squared' := _ }-/

variables (n : ℕ) (fn : Π (x : fin n.succ → R), (free_Koszul R n x).X 0 ≅ Module.of R R)
(x : fin n.succ.succ → R) (j : ℤ) (h0 : (int.of_nat 0, j).fst + (int.of_nat 0, j).snd = 0) (m : ℕ)

def add_eq (n i j : ℤ) (h : i + j = n) : {i : ℤ × ℤ // i.1 + i.2 = n} := ⟨(i, j), h⟩

def stupid_aux (y : R) (M : Module R) : tensor_product R ((smul_cx R y).X (add_eq 0 (int.of_nat 0) j h0).1.1) M →ₗ[R] M :=
(tensor_product.lid R M).to_linear_map


def huh : tensor_product R ((smul_cx R (x n.succ)).X (add_eq 0 (int.of_nat 0) j h0).1.1)
      ((free_Koszul R n (fin.init x)).X 0) →ₗ[R]
    (Module.of R R) :=
linear_map.comp (fn (fin.init x)).hom (stupid_aux R j h0 (x n.succ) ((free_Koszul R n (fin.init x)).X 0))

example (y : R) : (smul_cx R y).X (add_eq 0 (int.of_nat 0) j h0).1.1 = Module.of R R := rfl

def free_Koszul_zero {n : ℕ} : Π (x : fin n.succ → R),
  (free_Koszul R n x).X 0 ≅ Module.of R R :=
nat.rec_on n (λ x, category_theory.iso.refl _) $ λ n fn x,
{ hom := direct_sum.to_module R _ _
    (λ i, subtype.cases_on i $ λ i, prod.cases_on i $ λ i j, int.cases_on i (
    by dsimp; exact
    (λ i, nat.rec_on i
    (λ i, int.rec_on j (λ j, nat.rec_on j ((fn (fin.init x)).hom.comp
      (tensor_product.lid R _).to_linear_map)
    (λ j, 0)) (λ j, 0))
    (λ l fl hl, 0))) (λ l hl, 0)),
  inv := (direct_sum.lof R _ _ (⟨(0, 0), zero_add _⟩ : {i : ℤ × ℤ // i.1 + i.2 = 0})).comp $
    (tensor_product.lid R _).symm.to_linear_map.comp (fn _).symm.hom,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

def equiv_punit_of_rk_eq_zero (i : ℕ) (hi : i = 0) :
  (fin i → R) ≃ₗ[R] punit :=
{ to_fun := (0 : (fin i → R) →ₗ[R] punit),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := (0 : punit →ₗ[R] (fin i → R)),
  left_inv := sorry,
  right_inv := sorry }

def equiv_ring_of_rk_eq_one (i : ℕ) (hi : i = 1) :
  (fin i → R) ≃ₗ[R] R :=
{ to_fun := λ f, f (fin.cast hi.symm 0),
  map_add' := λ x y, rfl,
  map_smul' := λ r x, rfl,
  inv_fun := λ r j, r,
  left_inv := sorry,
  right_inv := sorry }

def equiv_of_eq_rk (i j : ℕ) (h : i = j) :
  (fin i → R) ≃ₗ[R] (fin j → R) :=
{ to_fun := λ f, f ∘ fin.cast h.symm,
  map_add' := sorry,
  map_smul' := sorry,
  inv_fun := λ f, f ∘ fin.cast h,
  left_inv := sorry,
  right_inv := sorry }

def free_Koszul_prod {n i : ℕ} (x : fin n.succ.succ → R) :
  (free_Koszul R n.succ x).X (int.of_nat i.succ) ≃ₗ[R]
  ((free_Koszul R n (fin.init x)).X (int.of_nat i.succ) ×
  (free_Koszul R n (fin.init x)).X (int.of_nat i)) :=
{ to_fun :=
    direct_sum.to_module R _ (((free_Koszul R n (fin.init x)).X
     (int.of_nat i.succ)) ×
  (free_Koszul R n (fin.init x)).X (int.of_nat i))
    (λ (j : {j : ℤ × ℤ // j.1 + j.2 = int.of_nat i.succ}),
  (subtype.cases_on j (λ j, prod.cases_on j $ λ j k,
  int.rec_on j (λ j, nat.rec_on j (λ hj, (linear_map.inl R _ _).comp
    ((cx_cast _ _ _ (by dsimp at hj; rwa zero_add at hj)).hom.comp
    (tensor_product.lid R _).to_linear_map))
    (λ k, nat.rec_on k (λ hj hk, (linear_map.inr R _ _).comp $
      (cx_cast _ _ _ (by dsimp at *; omega)).hom.comp
    (tensor_product.lid R _).to_linear_map) (λ _ _ _ _, 0)))
  (λ _ _, 0)) :
    tensor_product R ((smul_cx R (x n.succ)).X j.1.1)
      ((free_Koszul R n (fin.init x)).X j.1.2) →ₗ[R]
      ((free_Koszul R n (fin.init x)).X (int.of_nat i.succ)
        × (free_Koszul R n (fin.init x)).X (int.of_nat i)))),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := @linear_map.coprod R ((free_Koszul R n (fin.init x)).X (int.of_nat i.succ))
    ((free_Koszul R n (fin.init x)).X (int.of_nat i))
      ((free_Koszul R n.succ x).X (int.of_nat i.succ)) _ _ _ _ _ _ _
   ((direct_sum.lof R {j : ℤ × ℤ // j.1 + j.2 = int.of_nat i.succ} _
     ⟨(0, int.of_nat i.succ), zero_add _⟩).comp
   (tensor_product.lid R ((free_Koszul R n (fin.init x)).X (int.of_nat i.succ))).symm.to_linear_map)
   ((direct_sum.lof R {j : ℤ × ℤ // j.1 + j.2 = int.of_nat i.succ} _
     ⟨(1, int.of_nat i), by dsimp; rw add_comm⟩).comp
   (tensor_product.lid R ((free_Koszul R n (fin.init x)).X (int.of_nat i))).symm.to_linear_map),
  left_inv := sorry,
  right_inv := sorry }

def rk_free_prod_eq_add (i j : ℕ) :
  ((fin i → R) × (fin j → R)) ≃ₗ[R] (fin (i + j) → R) :=
{ to_fun := λ f, fin.append rfl f.1 f.2,
  map_add' := λ f g, fin.append_add rfl f.1 g.1 f.2 g.2,
  map_smul' := λ r f, by simp only [fin.append_smul rfl, prod.smul_snd, prod.smul_fst],
  inv_fun := λ f, (f ∘ fin.cast_add j, f ∘ fin.cast (add_comm j i) ∘ fin.cast_add i),
  left_inv := sorry,
  right_inv := sorry }

def free_Koszul_isom_choose {n : ℕ} (i : ℕ) : Π (x : fin n.succ → R),
  (free_Koszul R n x).X (int.of_nat i) ≅ Module.of R (fin (n.succ.choose i) → R) :=
nat.rec_on n (λ x, nat.rec_on i (of_fin_one_equiv R).symm.to_Module_iso
    (λ j fj, nat.rec_on j (of_fin_one_equiv R).symm.to_Module_iso (λ k fk,
    (equiv_punit_of_rk_eq_zero R (nat.choose 1 k.succ.succ)
      (nat.choose_eq_zero_of_lt (by omega))).symm.to_Module_iso))) $
  λ m, nat.rec_on i (λ fm x, (free_Koszul_zero R x).trans
    (of_fin_one_equiv R).symm.to_Module_iso) $
  λ k fm fm' y, linear_equiv.to_Module_iso $
     (free_Koszul_prod R _).trans $ linear_equiv.trans
  (linear_equiv.prod (fm' (fin.init y)).to_linear_equiv _)
  ((rk_free_prod_eq_add R _ _).trans (equiv_of_eq_rk R _ _ $ add_comm _ _))


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
