import m4r.cx data.matrix.basic

universes u v w
variables {R : Type u} [comm_ring R]
(F : cochain_complex.{u u+1} (Module.{u u} R))
open_locale classical

def cx_cast (j k : ℤ) (h : j = k) : F.X j ≅ F.X k :=
{ hom := { to_fun := λ x, eq.rec x h,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  inv := { to_fun := λ x, eq.rec x h.symm,
    map_add' := λ x y, by cases h; refl,
    map_smul' := λ r x, by cases h; refl },
  hom_inv_id' := by ext; cases h; refl,
  inv_hom_id' := by ext; cases h; refl }

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

lemma subsingleton_free_Koszul_neg' {n : ℕ} (j : ℤ) {x : fin n.succ → R} (hj : j < 0) :
  subsingleton ((free_Koszul R n x).X j) :=
@equiv.subsingleton _ _ (cx_cast _ j -[1+ (int.nat_abs (j + 1))]
begin
  induction j with j j,
  { exfalso,
    linarith [int.of_nat_nonneg j] },
  { induction j with j hj,
    { congr },
    { congr }},
end).to_linear_equiv.to_equiv
(subsingleton_free_Koszul_neg R _ _ _)

lemma subsingleton_smul_cx (j : ℤ) (x : R) (hj : ¬(j = 0 ∨ j = 1)) :
  subsingleton ((smul_cx R x).X j) :=
begin
  induction j with j j,
  { induction j with j hj,
    { contrapose! hj,
      exact or.inl rfl },
    { induction j with j hj',
      { contrapose! hj,
        exact or.inr rfl },
      { show subsingleton (Module.of R punit), by apply_instance }}},
  { exact subsingleton_free_Koszul_neg R 0 j (λ i, x) }
end

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

def free_Koszul_zero {n : ℕ} : Π (x : fin n.succ → R),
  (free_Koszul R n x).X 0 ≅ Module.of R R :=
nat.rec_on n (λ x, category_theory.iso.refl _) $ λ n fn x,
{ hom := (fn (fin.init x)).hom.comp  (linear_map.comp (tensor_product.lid R
  ((free_Koszul R n (fin.init x)).X 0)).to_linear_map
  (direct_sum.component R (int_pair 0) _
   (int_pair_mk 0 0 0 $ zero_add _) : (free_Koszul R n.succ x).X 0
     →ₗ[R] tensor_product R (Module.of R R) ((free_Koszul R n (fin.init x)).X 0))),
  inv := (direct_sum.lof R _ _ (int_pair_mk 0 0 0 $ zero_add _)).comp $
    (tensor_product.lid R _).symm.to_linear_map.comp (fn _).symm.hom,
  hom_inv_id' :=
  begin
    show linear_map.comp _ _ = _,
    rw [linear_map.comp_assoc, linear_map.comp_assoc],
    conv_lhs {congr, skip, congr, skip, rw [←linear_map.comp_assoc, comp_symm_hom, linear_map.id_comp]},
    conv_lhs {congr, skip, rw [←linear_map.comp_assoc, to_linear_map_comp]},
    erw linear_equiv.trans_symm,
    show (direct_sum.lof R (int_pair 0) _ _).comp (direct_sum.component R (int_pair 0) _ _) = _,
    ext1 i,
    refine tensor_product.ext _,
    intros X Y,
    simp only [dfinsupp.lsingle_apply, Module.id_apply, linear_map.comp_apply],
    rcases classical.em (i = int_pair_mk 0 0 0 (zero_add _)) with ⟨rfl, h⟩,
    { erw [direct_sum.component.lof_self],
      refl },
    { erw direct_sum.component.lof_ne R h,
      rw [←direct_sum.single_eq_lof, dfinsupp.single_zero],
      convert dfinsupp.single_zero.symm,
      refine decidable.lt_by_cases i.1.1 0 (λ H, _) (λ H, _) (λ H, _),
      { rw [@subsingleton.elim _ (@subsingleton_free_Koszul_neg' R _ 0 i.1.1 (λ k, x n.succ) H) X 0,
        tensor_product.zero_tmul] },
      { contrapose! h,
        rw [int_pair_ext_iff_fst, H],
        refl },
      { have : i.1.2 < 0 := by {rw ←int_pair_snd_eq_sub i, linarith},
        rw [@subsingleton.elim _ (@subsingleton_free_Koszul_neg' R _ n i.1.2 (fin.init x) this) Y 0,
        tensor_product.tmul_zero] },
      { apply_instance }}
  end,
  inv_hom_id' :=
    begin
      ext,
      dsimp,
      simp only [linear_map.comp_apply, ←tensor_product.lid_symm_apply],
      erw [direct_sum.component.lof_self, linear_equiv.apply_symm_apply,
        linear_map.ext_iff.1 (fn _).inv_hom_id],
      refl,
    end }

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

def smul_cx_prod (F : cochain_complex (Module R)) (x : R) (i : ℤ) :
  (cochain_complex.tensor_product R (smul_cx R x) F).X i ≃ₗ[R] F.X i × (shift F 1).X i :=
{ to_fun := @linear_map.prod R ((cochain_complex.tensor_product R (smul_cx R x) F).X i)
      (F.X i) ((shift F 1).X i) _ _ _ _ _ _ _ ((tensor_product.lid R _).to_linear_map.comp
    (direct_sum.component R (int_pair i) _ (int_pair_mk i 0 i $ zero_add _) :
      (cochain_complex.tensor_product R (smul_cx R x) F).X i →ₗ[R] tensor_product R
        (Module.of R R) (F.X i)))
    ((tensor_product.lid R _).to_linear_map.comp (direct_sum.component R _ _ (int_pair_mk i 1 (i-1)
      $ add_sub_cancel'_right _ _))),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := @linear_map.coprod R (F.X i) ((shift F 1).X i)
      ((cochain_complex.tensor_product R (smul_cx R x) F).X i) _ _ _ _ _ _ _
    ((direct_sum.lof R (int_pair i) _ (int_pair_mk i 0 i $ zero_add _)).comp
      (tensor_product.lid R (F.X i)).symm.to_linear_map)
    ((direct_sum.lof R (int_pair i) _ (int_pair_mk i 1 (i-1) $ add_sub_cancel'_right _ _)).comp
      (tensor_product.lid R ((shift F 1).X i)).symm.to_linear_map),
  left_inv := λ y,
    begin
      refine direct_sum.linduction_on R y _ _ _,
      { simp only [linear_map.map_zero] },
      { intros j z,
        dsimp,
        rcases classical.em (j = int_pair_mk i 0 i (zero_add _)) with ⟨rfl, _⟩,
        { convert add_zero _,
          { convert linear_map.map_zero _,
            convert tensor_product.tmul_zero _ _ },
          { rw [linear_equiv.symm_apply_apply],
            erw direct_sum.component.lof_self }},
        { rcases classical.em (j = int_pair_mk i 1 (i-1) (add_sub_cancel'_right _ _)) with ⟨rfl, _⟩,
          { convert zero_add _,
            { convert linear_map.map_zero _,
              convert tensor_product.tmul_zero _ _, },
            { rw [linear_equiv.symm_apply_apply],
              erw direct_sum.component.lof_self, }},
          { rw @subsingleton.elim _ (@tensor_product.subsingleton_left R _ _ _ _ _ _ _ $
              subsingleton_smul_cx R j.1.1 _ (λ hnot,
              begin
                cases hnot with h0 h1,
                { contrapose! h,
                  exact int_pair_ext_iff_fst.2 h0 },
                { contrapose! h_1,
                  exact int_pair_ext_iff_fst.2 h1 }
              end)) z 0,
              simp only [linear_map.map_zero, tensor_product.tmul_zero,
                linear_equiv.map_zero, zero_add] }}},
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
  end }

def free_Koszul_prod {n : ℕ} (i : ℕ) (x : fin n.succ.succ → R) :
  (free_Koszul R n.succ x).X i.succ ≃ₗ[R]
  ((free_Koszul R n (fin.init x)).X i.succ × (free_Koszul R n (fin.init x)).X i) :=
(smul_cx_prod R (free_Koszul R n (fin.init x)) (x n.succ) i.succ).trans
$ linear_equiv.prod (linear_equiv.refl _ _) (cx_cast _ (i.succ - 1) i $ by norm_num).to_linear_equiv

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

def free_Koszul_isom_choose {n : ℕ} : Π (i : ℕ) (x : fin n.succ → R),
  (free_Koszul R n x).X i ≅ Module.of R (fin (n.succ.choose i) → R) :=
nat.rec_on n (λ i x, nat.rec_on i (of_fin_one_equiv R).symm.to_Module_iso
    (λ j fj, nat.rec_on j (of_fin_one_equiv R).symm.to_Module_iso (λ k fk,
    (equiv_punit_of_rk_eq_zero R (nat.choose 1 k.succ.succ)
      (nat.choose_eq_zero_of_lt (by omega))).symm.to_Module_iso))) $
  λ m fm i, nat.rec_on i (λ x, (free_Koszul_zero R x).trans
    (of_fin_one_equiv R).symm.to_Module_iso) $
  λ k hk x,
    ((free_Koszul_prod R k x).trans $ linear_equiv.trans
  (linear_equiv.prod (fm k.succ (fin.init x)).to_linear_equiv
    (fm k (fin.init x)).to_linear_equiv) $
  ((rk_free_prod_eq_add R _ _).trans (equiv_of_eq_rk R _ _ $ add_comm _ _))).to_Module_iso

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

#exit
def free_exterior_power_aux (n i : ℕ) :
  alternating_map R (fin n.succ → R) (fin (n.succ.choose i) → R) (fin i) :=
{ to_fun := λ f i, ,
  map_add' := _,
  map_smul' := _,
  map_eq_zero_of_eq' := _ }

def hm : alternating_map R (fin 2 → R) (fin 1 → R) (fin 2) :=
{ to_fun := λ f i, f 0 0 * f 1 1 - f 1 0 * f 0 1,
  map_add' := λ x y w z,
    begin
      ext i,
      fin_cases y,
      { simp only [function.update_same, fin.one_eq_zero_iff, pi.add_apply,
          function.update_noteq, ne.def, not_false_iff, one_ne_zero],
        ring },
      { simp only [function.update_same, pi.add_apply, fin.zero_eq_one_iff,
          function.update_noteq, ne.def, not_false_iff, one_ne_zero],
        ring },
    end,
  map_smul' := λ x i r y,
    begin
      ext j,
      fin_cases i,
      { simp only [algebra.id.smul_eq_mul, function.update_same, fin.one_eq_zero_iff,
          function.update_noteq, ne.def, not_false_iff,  one_ne_zero, pi.smul_apply],
        ring },
      { simp only [algebra.id.smul_eq_mul, function.update_same, fin.zero_eq_one_iff,
         function.update_noteq, ne.def, not_false_iff,
         one_ne_zero, pi.smul_apply],
        ring, }
    end,
  map_eq_zero_of_eq' := λ v i j hv hij,
    begin
      ext k,
      fin_cases i,
      { fin_cases j,
        { exact false.elim (hij rfl) },
        { simp only [hv, pi.zero_apply, sub_self] }},
      { fin_cases j,
        { simp only [hv, pi.zero_apply, sub_self] },
        { exact false.elim (hij rfl) }}
    end }

def basis (n : ℕ) : fin n → (fin n → R) :=
λ i, function.update 0 i 1

lemma multiset.sum_const {α : Type*} {γ : Type*} {M : Type u} [add_comm_monoid M]
  (f : α → M) (s : multiset α) (x : γ) :
  (s.map (λ (y : α) (x : γ), f y)).sum x = (s.map f).sum :=
begin
  refine multiset.induction_on s _ _,
  { simp only [pi.zero_apply, multiset.map_zero, multiset.sum_zero] },
  { intros t s h,
    simp only [multiset.map_cons, pi.add_apply, multiset.sum_cons],
    rw h,},
end

lemma epow.mk_def {M : Type u} [add_comm_group M] [module R M] {n : ℕ}
  (f : fin n → M) :
  epow.mk R M n f = submodule.quotient.mk (tpow.mk R M n f) :=
rfl

lemma diag_eq_sum_std_basis {n : Type*} [fintype n] [decidable_eq n] (x : n → R) :
  matrix.diagonal x = finset.univ.sum (λ i, matrix.std_basis_matrix i i (x i)) :=
begin
  rw matrix.matrix_eq_sum_std_basis (matrix.diagonal x),
  congr,
  ext i j k,
  simp only [fintype.sum_apply],
  unfold matrix.std_basis_matrix,
  split_ifs,
  { simp only [ite_and, if_pos h.1],
    rw [finset.sum_ite_eq, if_pos (finset.mem_univ _), h.2],
    exact if_pos rfl },
  { cases classical.em (j = i),
    { simp only [ite_and, if_pos h_1],
      rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)],
      exact if_neg (ne.symm $ not_and.1 h h_1) },
    { simp only [ite_and, if_neg h_1, finset.sum_const_zero] }},
end

lemma sum_fin_two {α : Type*} [add_comm_monoid α] (f : fin 2 → α) :
  finset.univ.sum f = f 0 + f 1 :=
begin
  convert finset.sum_insert (show (0 : fin 2) ∉ ({1} : finset (fin 2)), from _),
  { simp only [finset.sum_singleton] },
  { simp only [fin.zero_eq_one_iff, not_false_iff, one_ne_zero, finset.mem_singleton] },
end

#exit

lemma are_you_serious {α : Type*} [add_comm_monoid α] (f : finset (fin 2) → α) :
  finset.univ.sum f = f {0} + f {1} + f {0, 1} + f ∅ :=
begin
  sorry,
end
--#check finset.piecewise_
def hmmm :
  epow R (fin 2 → R) 2 ≃ₗ[R] (fin 1 → R) :=
{ to_fun := epow_lift R (hm R),
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _,
  inv_fun := λ f, f 0 • epow.mk R (fin 2 → R) _ (matrix.diagonal (λ i : fin 2, (1 : R))),
  left_inv := λ x,
    begin
      refine quot.induction_on x _,
      intro y,
      simp only [submodule.quotient.quot_mk_eq_mk],
      rcases exists_sum_of_tpow R _ y with ⟨s, rfl⟩,
      rw ←submodule.mkq_apply,
      rw map_sum,
      rw map_sum,
      simp only [submodule.quotient.mk_smul, submodule.mkq_apply, linear_map.map_smul],
      simp only [←epow.mk_def, epow_lift_mk],
      unfold hm,
      simp only [alternating_map.coe_mk],
      erw @multiset.sum_const (R × (fin 2 → fin 2 → R)) (fin 1) R _
        (λ (i : R × (fin 2 → fin 2 → R)), i.1 • (i.2 0 0 * i.2 1 1 - i.2 1 0 * i.2 0 1)) s 0,
      rw multiset.sum_smul,
      congr' 1,
      simp only [algebra.id.smul_eq_mul, function.comp_app, multiset.map_map],
      congr,
      ext y,
      simp only [function.comp_app],
      rw mul_smul,
      congr,
      rw diag_eq_sum_std_basis,
      rw sum_fin_two,
      erw multilinear_map.map_add_univ,
      conv_rhs {rw matrix.matrix_eq_sum_std_basis y.2},
      rw sum_fin_two,
      rw sum_fin_two,
      erw multilinear_map.map_add_univ,
      rw are_you_serious,
      rw are_you_serious,
      show _ • (epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _) = epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _,
      simp only [finset.piecewise_singleton, finset.piecewise_insert, finset.piecewise_empty],
      rw sum_fin_two,
      erw multilinear_map.map_add_univ,
      rw are_you_serious,
      simp only [finset.piecewise_singleton, finset.piecewise_insert, finset.piecewise_empty],
      show _ = _ + (epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _ + epow.mk R (fin 2 → R) _ _),
      simp only [alternating_map.map_add, pi.add_apply],

      have := alternating_map.map_smul (epow.mk R (fin 2 → R) 2) 0 _ (y.2 0 0 * y.2 1 1 - y.2 1 0 * y.2 0 1),


    end,
  right_inv := _ }
