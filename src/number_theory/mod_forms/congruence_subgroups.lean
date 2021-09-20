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



variable (N : ℕ)
