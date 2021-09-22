import linear_algebra.special_linear_group
import .mod_group

local notation `SL2Z` := matrix.special_linear_group (fin 2) ℤ

def red_map (N : ℕ) : ℤ →+* (zmod N) := int.cast_ring_hom _

def mat_mod_map (N : ℕ) : matrix (fin 2) (fin 2) ℤ →+* matrix (fin 2) (fin 2) (zmod N) :=
ring_hom.map_matrix (red_map N)


def SL_mod_map' (N : ℕ) : matrix.special_linear_group (fin 2) ℤ → matrix.special_linear_group (fin 2) (zmod N):=
λ M, ⟨mat_mod_map (N : ℕ) M.1 , by {rw mat_mod_map, rw ring_hom.map_matrix, rw red_map, simp,
    have:= matrix.special_linear_group.det_coe M, rw modular_group.det_of_22 at *,
    simp at *, norm_cast, rw this, simp,} ⟩

def SL_mod_map (N : ℕ) : matrix.special_linear_group (fin 2) ℤ →* matrix.special_linear_group (fin 2) (zmod N):={
 to_fun :=  SL_mod_map' (N : ℕ),
 map_one' := by {rw SL_mod_map', simp, refl,},
 map_mul' := by {intros A B, rw SL_mod_map',
 have := (mat_mod_map N).map_mul' A B,  simp_rw mat_mod_map at *, simp_rw red_map at *, simp at *,simp_rw [this], refl,} ,
}

@[simp]
lemma sl_map_val (N : ℕ) (γ : SL2Z) : ∀ i j, (SL_mod_map N γ) i j = ((γ i j) : zmod N) :=
begin
intros i j,
refl,
end

def Gamma_N (N : ℕ) : subgroup SL2Z := (SL_mod_map N).ker

lemma Gamma_N_mem' (N : ℕ) (γ : SL2Z) :γ ∈ (Gamma_N N) ↔ (SL_mod_map N γ)=1:=iff.rfl

@[simp]
lemma Gamma_N_mem (N : ℕ) (γ : SL2Z) : γ ∈ (Gamma_N N) ↔ ((γ 0 0) : zmod N) = 1 ∧ ((γ 0 1) : zmod N) = 0 ∧
  ((γ 1 0) : zmod N) = 0 ∧ ((γ 1 1) : zmod N) = 1 :=
 begin
split,
intro hg,
simp [Gamma_N_mem', SL_mod_map,  SL_mod_map', mat_mod_map,red_map ] at *,
have h1 : ∀ i j, (SL_mod_map N γ) i j = (1 : matrix.special_linear_group (fin 2) (zmod N)) i j, by {
  simp, have ht:=  matrix.special_linear_group.ext_iff (SL_mod_map N γ) 1,
  simp [Gamma_N_mem', SL_mod_map,  SL_mod_map', mat_mod_map,red_map ] at *, apply ht.1 hg,},
simp [Gamma_N_mem', SL_mod_map,  SL_mod_map', mat_mod_map,red_map ] at *,
simp_rw [h1], split, refl, split, refl, split, refl,refl,

intro H,
simp [Gamma_N_mem', SL_mod_map,  SL_mod_map', mat_mod_map,red_map ] at *,
ext,
simp,
fin_cases i; fin_cases j,
simp_rw H.1, refl,
simp_rw H.2.1, refl,
simp_rw H.2.2.1, refl,
simp_rw H.2.2.2, refl,
 end


def is_congruence_subgroup (Γ : subgroup SL2Z) : Prop :=
∃ (N : ℕ), (Gamma_N N) ≤ Γ

lemma is_congruence_subgroup_trans (H K : subgroup SL2Z) (h: H ≤ K) (h2 : is_congruence_subgroup H) :
is_congruence_subgroup K :=
begin
  simp_rw is_congruence_subgroup at *,
  let N:= classical.some_spec h2,
  have := le_trans N h,
  use classical.some h2,
  exact this,
end

lemma Gamma_N_is_cong_sub (N : ℕ) : is_congruence_subgroup (Gamma_N N):=
begin
rw is_congruence_subgroup,
use N,
simp only [le_refl],
end

def Gamma0_N (N : ℕ) : subgroup SL2Z :={
carrier := { g : SL2Z | (g 1 0 : zmod N) = 0},
one_mem' := by {simp, },
mul_mem':= by {intros a b ha hb, simp only [integral_matrices_with_determinant.mat_m_vals,
  matrix.special_linear_group.coe_mul, set.mem_set_of_eq,
  subtype.val_eq_coe] at *,
  have := (modular_group.mat_mul_expl a b).2.2.1,
  simp only [ integral_matrices_with_determinant.mat_m_vals, matrix.special_linear_group.coe_fn_eq_coe ] at this,
  dsimp at *, simp at *, rw this, simp, rw [ha, hb], simp,},
inv_mem':= by {intros a ha, simp only [ set.mem_set_of_eq, subtype.val_eq_coe],
have := modular_group.explicit_inv_is_inv a,
simp [modular_group.SL2Z_inv_explicit] at this, rw this, simp at *, exact ha,},
}

@[simp]
lemma Gamma0_N_mem (N : ℕ) (A: SL2Z) : A ∈ (Gamma0_N N) ↔ (A 1 0 : zmod N)=0 :=iff.rfl

lemma Gamma0_det (N : ℕ) (A : Gamma0_N N) : (A.1.1.det : zmod N) = 1 :=
begin
have ha:= A.1.property,
rw ha,
simp,
end

def Gamma0_map' (N : ℕ) : (Gamma0_N N) → (zmod N) :=
λ g, (g 1 1 : zmod N)

def Gamma_0_map (N : ℕ): (Gamma0_N N) →* (zmod N)   :={
 to_fun :=  λ g, (g 1 1 : zmod N),
 map_one' := by {simp only [integral_matrices_with_determinant.mat_m_vals,
  matrix.special_linear_group.coe_one, int.cast_one, matrix.one_apply_eq,
  coe_fn_coe_base, subgroup.coe_one, subtype.val_eq_coe], },
 map_mul' := by {intros A B,
   have := (modular_group.mat_mul_expl A B).2.2.2,
    dsimp at *,
    rw this,
    have ha:= A.property,
    simp at *,
    rw ha,
    simp,} ,
}

def Gamma1_N' (N : ℕ) : subgroup (Gamma0_N N) := (Gamma_0_map N).ker

@[simp]
lemma Gamma1_N_mem' (N : ℕ) (γ :(Gamma0_N N)) :γ ∈ (Gamma1_N' N) ↔ ((Gamma_0_map N) γ)=1:=iff.rfl

lemma Gamma1_to_Gamma0_mem (N : ℕ) (A : Gamma0_N N) : A ∈ (Gamma1_N' N) ↔
  (A 0 0 : zmod N) =1 ∧ (A 1 1 : zmod N) =1  ∧ (A 1 0 : zmod N) = 0 :=
begin
  split,
  intro ha,
  have hA:= A.property,
  simp only [Gamma0_N_mem, integral_matrices_with_determinant.mat_m_vals, subtype.val_eq_coe] at hA,
  simp only [Gamma1_N_mem', integral_matrices_with_determinant.mat_m_vals,
    coe_fn_coe_base, subtype.val_eq_coe] at *,
  simp_rw Gamma_0_map at ha, dsimp at *,
  simp only [ha, hA, and_true, eq_self_iff_true],
  have adet:= Gamma0_det N A,
  rw modular_group.det_of_22 at adet,
  simp only [int.cast_mul, int.cast_sub, subtype.val_eq_coe] at adet,
  rw [hA, ha] at adet,
  simp at adet,
  exact adet,
  intro ha,
  simp only [Gamma1_N_mem'],
  simp_rw Gamma_0_map,
  simp only [integral_matrices_with_determinant.mat_m_vals, coe_fn_coe_base,
    monoid_hom.coe_mk, subtype.val_eq_coe],
  exact ha.2.1,
end

def Gamma1_map (N : ℕ) : (Gamma1_N' N) →* SL2Z := ((Gamma0_N N).subtype).comp (Gamma1_N' N).subtype

def Gamma1_N (N : ℕ) : subgroup SL2Z :=subgroup.map (Gamma1_map N) ⊤

@[simp]
lemma Gamma1_N_mem (N : ℕ) (A : SL2Z) : A ∈ (Gamma1_N N) ↔
  (A 0 0 : zmod N) = 1 ∧ (A 1 1 : zmod N)=1 ∧ (A 1 0 : zmod N) = 0 :=
begin
  split,
  intro ha,
  simp only [integral_matrices_with_determinant.mat_m_vals, subtype.val_eq_coe] at *,
  dsimp at *,
  simp_rw Gamma1_N at ha,
  rw subgroup.mem_map at ha,
  rw Gamma1_map at  ha,
  simp at ha,
  let x:= classical.some ha,
  have hx:= x.property,
  simp only [Gamma1_to_Gamma0_mem]at hx,
  have hxx:= classical.some_spec ha,
  simp_rw x at hx,
  rw ← hxx,
  simp only [integral_matrices_with_determinant.mat_m_vals, coe_fn_coe_base, subtype.val_eq_coe] at *,
  simp only [hx, eq_self_iff_true, and_self],
  intro ha,
  simp only [integral_matrices_with_determinant.mat_m_vals, subtype.val_eq_coe] at *,
  simp_rw Gamma1_N,
  rw subgroup.mem_map,
  have hA: A ∈ (Gamma0_N N), by {simp only [ha.right.right, Gamma0_N_mem,
    integral_matrices_with_determinant.mat_m_vals, subtype.val_eq_coe],},
  have HA : (⟨A , hA⟩ : Gamma0_N N) ∈ Gamma1_N' N,
    by {simp only [Gamma1_to_Gamma0_mem, integral_matrices_with_determinant.mat_m_vals,
    coe_fn_coe_base, subtype.val_eq_coe,subgroup.coe_mk], exact ha,},
  use ⟨ (⟨A , hA⟩ : Gamma0_N N), HA ⟩,
  simp only [true_and, subgroup.mem_top],
  rw Gamma1_map,
  simp only [subgroup.coe_subtype, function.comp_app, monoid_hom.coe_comp, subgroup.coe_mk],
end

lemma Gamma1_in_Gamma0 (N : ℕ) : (Gamma1_N N) ≤ (Gamma0_N N) :=
begin
  intros x HA,
  simp only [Gamma0_N_mem, Gamma1_N_mem, integral_matrices_with_determinant.mat_m_vals,
    subtype.val_eq_coe] at *,
  exact HA.2.2,
end

lemma Gamma1_N_is_congruence (N : ℕ) : is_congruence_subgroup (Gamma1_N N) :=
begin
  simp_rw is_congruence_subgroup,
  use N,
  intros A hA,
  simp only [Gamma1_N_mem, integral_matrices_with_determinant.mat_m_vals,
    subtype.val_eq_coe, Gamma_N_mem] at *,
  simp only [hA, eq_self_iff_true, and_self],
end

lemma Gamma0_N_is_congruence (N : ℕ) :  is_congruence_subgroup (Gamma0_N N) :=
begin
apply is_congruence_subgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_N_is_congruence N),
end

def conj_cong_subgroup (g : SL2Z)  (Γ : subgroup SL2Z) : subgroup SL2Z :={
carrier := { h : SL2Z | ∃ γ : Γ, g⁻¹ * γ * g = h},
one_mem' := by  {simp, use 1, simp,}  ,
mul_mem' := by {intros a b ha hb, simp at *,
  let aa:= classical.some ha,
  let bb:= classical.some hb,
  have haa:= classical.some_spec ha,
  have hbb:= classical.some_spec hb,
  use aa*bb, rw   ←  haa, rw ← hbb, simp, simp_rw ←  mul_assoc, simp,},
inv_mem' := by {intros x hx, simp at *,
  let a:= classical.some hx,
  have ha:= classical.some_spec hx,
  use a⁻¹ ,
  rw ← ha,
  simp,
  simp_rw ←  mul_assoc,} ,


}
