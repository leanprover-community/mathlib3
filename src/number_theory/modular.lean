import analysis.complex.automorphisms_half_plane
import analysis.complex.basic
import data.matrix.notation
import data.int.basic
import data.int.parity
import data.nat.gcd
import algebra.ordered_ring
import ring_theory.int.basic
import data.real.sqrt

open complex
open matrix
open matrix.special_linear_group
noncomputable theory


local notation `|` x `|` := _root_.abs x
local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

-- special linear group over ℤ

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance SL2Z_action : mul_action SL(2, ℤ) H :=
mul_action.comp_hom H (SL_n_insertion (int.cast_ring_hom ℝ))

@[simp]
lemma smul_def_int (g : SL(2,ℤ)) (z : H) : ↑(g • z) = smul_aux g z :=
begin
  refl,
end

lemma smul_neg_SL2_int (g : SL(2,ℤ)) (z : H) : -g • z = g • z :=
begin
  rw subtype.ext_iff,
  simp only [smul_def_int, smul_aux_def, top, bottom],
  rw ← neg_div_neg_eq,
  congr' 1; simp; ring,
end


@[simp]
lemma bottom_def {g : SL(2,ℤ)} {z : ℂ} : bottom g z = g.1 1 0 * z + g.1 1 1 := by simp

@[simp]
lemma top_def {g : SL(2,ℤ)} {z : ℂ} : top g z = g.1 0 0 * z + g.1 0 1 := by simp



lemma im_smul_SL' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (g.1 1 0 * z + g.1 1 1)) :=
by simpa using im_smul_SL g z

lemma im_smul_SL'' (g : SL(2, ℤ)) (z : H) :
(g • z).val.im = z.val.im / (complex.norm_sq (bottom g z)) :=
im_smul_mat_complex


@[simp]
lemma smul_sound {g : SL(2,ℤ)} {z : H} : ((g:SL(2,ℝ)) • z).1 = smul_aux g z :=
rfl

-- T and S

def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property := by simp [det2] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property := by simp [det2] }

example : T⁻¹ * T = 1 := inv_mul_self T

example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

example { x y : SL(2,ℤ)} (h : x.1 = y.1) : x = y := subtype.eq h

@[simp]
lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

@[simp]
lemma mat_ext_iff  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
  x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
begin
  rw ←matrix.ext_iff,
  split,
  {
    intro h,
    rw h,
    tauto },
  {
    rintros ⟨h1, h2, h3, h4⟩ i j,
    fin_cases i; fin_cases j; assumption,
  }
end

@[simp]
lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
  = (1 : matrix (fin 2) (fin 2) F) := by {simp}


lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
begin
  suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
  { exact inv_eq_of_mul_eq_one this},
  simp [T],
end

lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

lemma T_pow_ℕ {n : ℕ} : T ^ n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  { simp },
  { rw [pow_succ', hn, T],
    simp [add_comm] }
end

lemma T_inv_pow_ℕ {n : ℕ} : (T⁻¹)^n = { val := ![![1, -n], ![0, 1]], property := by simp [det2] } :=
begin
  induction n with n hn,
  simp,
  have : (T⁻¹) ^ n.succ = ((T⁻¹)^n)* (T⁻¹),
  {
    exact pow_succ' (T⁻¹) n,
  },
  rw this,
  rw hn,
  rw T_inv,
  simp,
end


lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
begin
  by_cases n_ge_0 : 0 ≤ n,
  lift n to ℕ with n_ge_0,
  refine T_pow_ℕ,
  exact n_ge_0,
  have : T ^ n = T ^ (- (-n)) := by simp,
  rw this,
  rw T_n_def,
  generalize' hk : -n=k,
  have k_ge_0 : 0 ≤ k,
  {
    rw ← hk,
    linarith,
  },
  have : n = -k,
  {
    rw ← hk,
    ring,
  },
  rw this,
  lift k to ℕ using k_ge_0,
  rw gpow_coe_nat,
  norm_cast,
  rw T_inv_pow_ℕ,
end

lemma T_action {z : H} : (T • z).1 = z + 1 :=
begin
  convert @smul_sound T z,
  simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
end


lemma Tn_action {z : H} {n : ℤ} : (T^n • z).1 = z + n :=
begin
  have := @smul_sound (T^n) z,
  convert this,
  rw smul_aux,
  rw T_pow,
  rw top,
  rw bottom,
  simp,
end

lemma S_action (z : H) : (S • z).1 = -z⁻¹ :=
begin
  convert @smul_sound S z,
  simp only [smul_aux_def, top, bottom, S, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
  ring,
end


def fundamental_domain : set H :=
{ z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟°` := interior 𝒟

def fundamental_domain' : set H :=
{ z | 1 < (complex.norm_sq z) ∧ |(complex.re z)| < (1 :ℝ)/ 2 }

notation `𝒟'` := fundamental_domain'

notation `𝒟'c` := closure 𝒟'


lemma whatever : 𝒟'c = 𝒟 :=
begin

  sorry,
end

def coprime_ints := { cd :  ℤ × ℤ //  int.gcd cd.1 cd.2 = 1 }

instance : has_coe coprime_ints (ℤ×ℤ) := ⟨ λ x, x.val⟩

section finite_pairs

open filter continuous_linear_map

lemma tendsto_at_top_norm_sq : tendsto norm_sq (cocompact ℂ) at_top :=
begin
  convert tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top,
  { simp [mul_self_abs] },
  { apply_instance },
  { apply_instance }
end

lemma filter.tendsto.finite_preimage {α : Type*} {f : α → ℝ} (hf : tendsto f cofinite at_top) (M : ℝ) :
  set.finite {c : α | f c ≤ M} :=
begin
  obtain ⟨v, hv, hvM⟩ : ∃ v ∈ cofinite, ∀ y ∈ v, M + 1 ≤ f y,
  { rw tendsto_at_top at hf,
    have := hf (M + 1),
    rwa eventually_iff_exists_mem at this },
  rw mem_cofinite at hv,
  refine hv.subset _,
  rintros y (hy : f y ≤ M) hy',
  have : M + 1 ≤ f y := hvM y hy',
  linarith
end

lemma filter.tendsto.exists_forall_le {α β : Type*} [linear_order β] {f : α → β}
  (hf : tendsto f cofinite at_top) :
  ∃ a₀, ∀ a, f a₀ ≤ f a :=
begin
  sorry
end

lemma tendsto_cocompact_of_left_inverse {α β : Type*} [topological_space α] [topological_space β]
  {f : α → β} {g : β → α} (hg : continuous g) (hfg : function.left_inverse g f) :
  tendsto f (cocompact α) (cocompact β) :=
begin
  rw tendsto_iff_eventually,
  simp only [mem_cocompact, eventually_iff_exists_mem],
  rintros p ⟨v, hv, hvp⟩,
  rw mem_cocompact at hv,
  obtain ⟨t, ht, htv⟩ := hv,
  refine ⟨(g '' t)ᶜ, _, _⟩,
  { rw mem_cocompact,
    refine ⟨g '' t, ht.image hg, rfl.subset⟩ },
  intros x hx,
  have : f x ∈ v,
  { apply htv,
    intros h,
    apply hx,
    have h₁ : g (f x) ∈ g '' t := ⟨f x, h, rfl⟩,
    convert h₁,
    calc x = id x : by simp
    ... = (g ∘ f) x : by { congr, rw hfg } },
  exact hvp (f x) this
end

lemma finite_pairs (M : ℝ) (z : H) :
  set.finite {cd : coprime_ints | (((cd : ℤ×ℤ).1 : ℂ) * z + ((cd : ℤ × ℤ).2 : ℂ)).norm_sq ≤ M} :=
begin
  have h₁ : tendsto (λ c : ℝ × ℝ, ↑c.1 * (z:ℂ) + c.2) (cocompact _) (cocompact _),
  { let g : ℂ →L[ℝ] ℝ×ℝ := (continuous_linear_map.im).prod
      (continuous_linear_map.im.comp (((z:ℂ)• continuous_linear_map.conj ))),
    apply tendsto_cocompact_of_left_inverse ((z:ℂ).im⁻¹ • g).continuous,
    rintros ⟨c₁, c₂⟩,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne.symm,
    field_simp [g],
    ring },
  have h₂ : tendsto (λ c : ℤ × ℤ, ((c.1 : ℝ), (c.2 : ℝ))) cofinite (cocompact _),
  { convert int.tendsto_coe_cofinite.prod_map_coprod int.tendsto_coe_cofinite;
    simp [coprod_cocompact, coprod_cofinite] },
  have h₃ : tendsto (λ c : ℤ × ℤ, ((c.1 : ℂ) * z + (c.2 : ℂ)).norm_sq) cofinite at_top,
  { convert tendsto_at_top_norm_sq.comp (h₁.comp h₂),
    ext,
    simp },
  exact (h₃.comp (tendsto_embedding_cofinite (function.embedding.subtype _))).finite_preimage M,
end

end finite_pairs

variables {g : SL(2,ℤ)} {z : H}

lemma gcd_eq_one_iff_coprime' (a b : ℤ) : gcd a b = 1 ↔ is_coprime a b :=
begin
  rw [←int.coe_gcd, ←int.coe_nat_one, int.coe_nat_inj', int.gcd_eq_one_iff_coprime],
end

lemma exists_g_with_min_bottom (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (bottom g z).norm_sq ≤ (bottom g' z).norm_sq  :=
begin
  let f : coprime_ints → ℝ := λ cd,  (((cd : ℤ×ℤ).1:ℂ) * z + (cd : ℤ×ℤ).2).norm_sq,
  let s : finset coprime_ints := set.finite.to_finset (finite_pairs (1) z),
  have in_s_then_ge_1 : ∀ x, x ∈ s ↔ f x ≤ 1 := by simp [s],
  have : s.nonempty,
  {
    use (0,1),
    simp,
    simp,
  },
  obtain ⟨⟨ cd, hhcd⟩ , cdInS, hcd⟩ := finset.exists_min_image s f this,
  let a := int.gcd_b cd.1 cd.2,
  let b := -int.gcd_a cd.1 cd.2,
  let g := ![![a,b],![cd.1,cd.2]],
  have : 1 = det g,
  {
    rw det2,
    suffices : 1 = a * cd.2 - cd.1 * b ,
    convert this,
    suffices : 1 = a * cd.snd + cd.fst * int.gcd_a cd.fst cd.snd,
    {
      simp [g],
      exact this,
    },

    convert int.gcd_eq_gcd_ab cd.1 cd.2 using 1,
    rw  hhcd,
    simp,
    ring,
  },
  use ⟨ g, this.symm⟩ ,
  intros,
  have hcd' : ∀ (x' : coprime_ints), f ⟨cd,hhcd⟩ ≤ f x',
  {
    intros ,
    by_cases hx' : x' ∈ s,
    {
      exact hcd x' hx',
    },
    {
      rw in_s_then_ge_1  at hx',
      rw in_s_then_ge_1  at cdInS,
      linarith,
    },
  },
  have : int.gcd  (g'.val 1 0) (g'.val 1 1) = 1,
  {
    simp,
    let cc : ℤ  := (g'.val 1 0),
    let dd : ℤ  := (g'.val 1 1),
    have : int.gcd (g'.val 1 0) (g'.val 1 1) = int.gcd cc dd := rfl,

    convert this,
    symmetry,
    convert hhcd,
    sorry,
    simp [cc, g', g],
    simp [dd],
    rw gcd_eq_one_iff_coprime',
    use [(- (g'.val 0 1)) , ((g'.val 0 0))],

    have := g'.2,
    rw det2 at this,
    convert this using 1,
    simp [cc, dd],
    ring,
  },
  convert hcd' ⟨ (g'.val 1 0 , g'.val 1 1) , this ⟩ ,
  {
    rw bottom,
    simp [g],
  },
  rw bottom,
  simp,
end

lemma exists_g_with_max_Im (z : H) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ),  (g' • z).val.im ≤ (g • z).val.im :=
begin
  have := exists_g_with_min_bottom z,
  have im_z_pos : 0 < (z:ℂ ).im := im_pos_of_in_H.mp z.2,
  cases this with gg hg,
  use gg,
  intros g',
  rw im_smul_SL'',
  rw im_smul_SL'',
  have bg_n_pos : (bottom gg z).norm_sq > 0,
  {
    have bg : (bottom gg z) ≠ 0,
    {
      refine bottom_nonzero im_z_pos,
    },
    exact norm_sq_pos.mpr bg,
  },
  have bg'_n_pos : (bottom g' z).norm_sq > 0,
  {
    have bg' : (bottom g' z) ≠ 0,
    {
      refine bottom_nonzero im_z_pos,
    },
    exact norm_sq_pos.mpr bg',
  },
  have hgg' := hg g',
  have : 1/ norm_sq (bottom g' z) ≤ 1/ norm_sq (bottom gg z) ,
  {
    exact (one_div_le_one_div bg'_n_pos bg_n_pos).mpr (hg g'),
  },
  exact (div_le_div_left im_z_pos bg'_n_pos bg_n_pos).mpr (hg g'),
end

def G' : subgroup SL(2,ℤ) := subgroup.closure {S, T}

lemma exists_g_with_max_Im' (z : H) :
  ∃ g : SL(2,ℤ), (g ∈ G') ∧  ∀ g' : SL(2,ℤ), g' ∈ G' → ((g' : SL(2,ℤ)) • z).val.im ≤ ((g : SL(2,ℤ)) • z).val.im :=
begin
  -- Alex, can you do this one as well?
  -- I don't understand; how am I supposed to show g ∈ G' without proving S,T generate SL(2,Z)?...
  sorry
end


example : T ∈ (subgroup.closure ({S, T} : set SL(2,ℤ))) :=
begin
  apply subgroup.mem_closure',
  simp only [set.mem_insert_iff, true_or, set.mem_singleton, or_true, eq_self_iff_true],
end

example {G' : subgroup SL(2,ℤ)} {x y : SL(2,ℤ)} (hx : x ∈ G') (hy : y ∈ G') : x * y ∈ G' :=
begin
  exact subgroup.mul_mem G' hx hy,
end

example {n : ℤ} {g : SL(2,ℤ)} (hg : g ∈ G') : S * T^n * g ∈ G' :=
begin
  have hS : S ∈ G' :=
    by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' :=
    by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' :=
    by {apply subgroup.gpow_mem G' hT},
  apply subgroup.mul_mem G',
  { apply subgroup.mul_mem G' hS hTn },
  exact hg,
end

example {g : SL(2,ℤ)} {z z' : H} : g • z = z' ↔ z = g⁻¹ • z' :=
begin
  exact eq_inv_smul_iff.symm,
end

lemma abs_floor_ineq (a : ℝ) : |a + -⌊a + 2⁻¹⌋| ≤ 2⁻¹ :=
begin
  rw abs_le,
  split,
  {
    calc
    -2⁻¹ = a - (a + 2⁻¹)    : by ring
    ... ≤ a - ↑⌊a + 2⁻¹⌋    : _
    ... = a + -↑⌊a + 2⁻¹⌋  : by ring,

    simp,
    exact floor_le _,
  },

  calc
  a + -↑⌊a + 2⁻¹⌋ = a - ↑⌊a + 2⁻¹⌋ : by ring
  ... ≤ a - a + 2⁻¹ : _
  ... = 2⁻¹ : by ring,

  simp,
  apply le_of_lt,
  suffices : a - 2⁻¹ < ↑⌊a + 2⁻¹⌋,
  {
    linarith,
  },
  have := sub_one_lt_floor (a + 2⁻¹),
  convert this using 1,
  ring,
end

lemma find_appropriate_T (z : H) : ∃ (n : ℤ), | (T^n • z).val.re | ≤ 1/2 :=
begin
  let n := -floor ((z:ℂ ).re+1/2),
  use n,
  rw Tn_action,
  simp,
  apply abs_floor_ineq,
end

lemma im_S_z {z : H} : (S • z).val.im = z.val.im / z.val.norm_sq :=
begin
  rw im_smul_SL'',
  rw bottom,
  simp,
  rw S,
  simp,
end

lemma im_Tn_z {z : H} {n : ℤ} : (T^n • z).val.im = z.val.im :=
begin
  rw im_smul_SL'',
  rw bottom,
  simp,
  rw T_pow,
  simp,
end

lemma im_lt_im_S {z : H} (h: norm_sq z.val < 1) : z.val.im < (S • z).val.im :=
begin
  rw im_S_z,
  have imz : 0 < z.val.im := im_pos_of_in_H',
  have hnz : 0 < norm_sq z.val,
  {
    rw norm_sq_pos,
    intro h,
    rw h at imz,
    rw zero_im at imz,
    linarith,
  },
  set N := norm_sq z.val with hN,
  set zim := z.val.im with hzim,
  have : zim * N < zim, by nlinarith,
  exact (lt_div_iff hnz).mpr this,
end

/- TODO : prove directly instead of by contradiction
-/
lemma norm_sq_ge_one_of_act_S {z : H} (h : (S • z).val.im ≤ z.val.im) : 1 ≤ norm_sq z.val :=
begin
  by_contradiction hcontra,
  push_neg at hcontra,
  have := im_lt_im_S hcontra,
  linarith,
end

example {a b : ℤ} (ha : 0 ≤ a) (hp : a * b = 1) : a = 1 :=
begin
  exact int.eq_one_of_mul_eq_one_right ha hp,
end

/- By choosing from g or -g, we can impose conditions on the coefficients of g -/
lemma sign_coef { z z' : H } (h : ∃ g : SL(2, ℤ), z' = g • z) :
  ∃ g : SL(2, ℤ), 0 ≤ g.1 1 0 ∧ (g.1 1 0 = 0 → g.1 1 1 = 1 ∧ g.1 0 0 = 1) ∧ z' = g • z :=
begin
  obtain ⟨g, hg⟩ := h,
  by_cases hc : g.val 1 0 = 0,
  {
    have hdet := g.2,
    rw det2 at hdet,
    simp [hc] at hdet,
    by_cases hdsgn : 0 ≤ g.val 1 1,
    {
      use g,
      have hd := int.eq_one_of_mul_eq_one_left hdsgn hdet,
      have ha : g.val 0 0 = 1,
      {
        replace hdet : g.val 0 0 * g.val 1 1 = 1, by tauto,
        simpa [hd] using hdet,
      },
      exact ⟨eq.ge hc, λ _, ⟨hd, ha⟩, hg⟩,
    },
    {
      use -g,
      have hd : (-g).val 1 1 = 1,
      {
        suffices : g.val 1 1 = -1,
        {
          simp [this],
          sorry,
        },
        sorry,
      },
      sorry
    },
  },
  {
    by_cases hcpos : 0 < g.val 1 0,
    {
      use g,
      repeat{split},
      { linarith }, { tauto }, { exact hg }
    },
    {
      use -g,
      repeat {split},
      {
        sorry
      },
      {
        sorry
      },
      {
        sorry
      },
    }
  }
end

lemma is_fundom {z : H} : ∃ g : SL(2,ℤ), g ∈ G' ∧ g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg1, hg2⟩ := exists_g_with_max_Im' z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g) hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq, by exact ⟨hTng,⟨this, hn⟩⟩,
  set w := (S * T^n * g) • z with hw,
  apply norm_sq_ge_one_of_act_S,
  replace hw : w = S•z',
  {rw [hw, z'df, smul_smul, mul_assoc]},
  rw [imz', ← hw],
  exact hg2,
end


lemma is_fundom' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg2⟩ := exists_g_with_max_Im z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
--  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
--  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g), -- hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq,
  -- by exact ⟨hTn,⟨this, hn⟩⟩,
  {
    exact ⟨this, hn⟩,
  },

  set w := (S * T^n * g) • z with hw,
  apply norm_sq_ge_one_of_act_S,
  replace hw : w = S•z',
  {rw [hw, z'df, smul_smul, mul_assoc]},
  rw [imz', ← hw],
  exact hg2,
end

@[simp]
lemma fundom_aux_1 {z : H} (hz : z ∈ 𝒟) (h' : T • z ∈ 𝒟) : z.val.re = -1/2 := sorry

@[simp]
lemma fundom_aux_2 {z : H} (hz : z ∈ 𝒟) (h' : T⁻¹ • z ∈ 𝒟) : z.val.re = 1/2 := sorry

@[simp]
lemma fundom_aux_3 {z : H} (hz : z ∈ 𝒟) (h' : S • z ∈ 𝒟) : z.val.abs = 1 := sorry

/- Why is this not doable by linarith directly? -/
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ a / b) : b ≤ 1 :=
begin
  suffices: a * b ≤ a, nlinarith,
  rw le_div_iff hb at h,
  exact h,
end

lemma namedIs (c :ℕ ) (h: c≤ 1) :  c=0 ∨ c=1 :=
begin
  cases nat.of_le_succ h,
  {
    left,
    exact le_zero_iff.mp h_1,
  },
  right,
  exact h_1,
end

lemma namedIsZ (c :ℤ  ) (h: c≤ 1) (h2: 0≤ c) :  c=0 ∨ c=1 :=
begin
  --lift n to ℕ using hn
  lift c to ℕ using h2,
  norm_cast,
  refine namedIs _ _ ,
  exact_mod_cast h,
end

-- Describe closure of D as union of boundary segments and interior.
-- Then the lemma goes by cases on where z and z'

lemma fundom_no_repeats' (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟') (hz' : z' ∈ 𝒟') :
  (z = z') :=
begin
  sorry,
end

lemma is_fundom'' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ closure fundamental_domain' :=
begin
  sorry,
end


lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
  (z = z') ∨
  (z.val.re = -1/2 ∧ z' = T • z) ∨
  (z'.val.re = -1/2 ∧ z = T • z') ∨
  (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
begin
  wlog hwlog : z.val.im ≤ z'.val.im,
  {
    by_cases hne : z = z', tauto,
    right,
    replace h := sign_coef h,
    obtain ⟨g, hcpos, hac, hg⟩ := h,
    set a := g.1 0 0,
    set b := g.1 0 1,
    set c := g.1 1 0 with ←cdf,
    set d := g.1 1 1 with ←ddf,
    have hcd : complex.norm_sq (c * z + d) ≤ 1,
    {
      have himzpos : 0 < z.val.im := im_pos_of_in_H',
      have hnz : 0 < complex.norm_sq (c * z + d),
      {
        rw norm_sq_pos,
        intro hcontra,
        rw [← cdf, ← ddf, ← bottom_def] at hcontra,
        exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
      },
      suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
      rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
      exact hwlog,
    },
    have hc : _root_.abs c ≤ 1,
    {
      sorry
    },
    replace hc : c = 0 ∨ c = 1,
    {

      rw abs_le at hc,
      exact namedIsZ c hc.2 hcpos,
    },
    rcases hc with  hc | hc ,
    { -- case c = 0
      have ha : a = 1 := (hac hc).2,
      have hd : d = 1 := (hac hc).1,
      have hgT : g = T^b,
      {
        rw T_pow,
        apply subtype.eq,
        simp,
        tauto,
      },
      have hb : _root_.abs c ≤ 1,
      {
        sorry
      },
      replace hb : b = -1 ∨ b = 0 ∨ b = 1,
      {
        sorry
      },
      rcases hb with hb | hb | hb,
      all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
      {
        right, left,
        rw ←inv_smul_eq_iff at hg,
        rw ←hg at hz,
        rw fundom_aux_1 hz' hz,
        tauto,
      },
      { tauto },
      {
        left,
        rw hg at hz',
        rw fundom_aux_1 hz hz',
        tauto,
      }
    },
    { -- case c = 1
      sorry
    }
  },
  obtain ⟨g, hg⟩ := h,
  have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
  specialize this hh hz' hz,
  tauto,
end


-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form1

-- define Eisenstein series

-- prove E-sereis are modular

-- E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}} 1/(cz+d)^k

/-
  human:
  d/ dz E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}}  d/ dz 1/(cz+d)^k

  OR

  E(z,k) - E(w,k)
  =
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)
=
(z-w)   *
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)

-/

/- define Ramanujan delta

-/


-- @[simp]
-- lemma coeff_coe {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)).val i j = ((g.val i j) : ℝ) := by refl

-- @[simp]
-- lemma coeff_coe' {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)) i j = ((g i j) : ℝ) := by refl

-- lemma div_eq_mul_conj_div_norm_sq {z w : ℂ} : z / w = (z * (w.conj)) / complex.norm_sq w :=
-- begin
--   rw [div_eq_mul_inv, inv_def, div_eq_mul_inv, mul_assoc],
--   norm_num,
-- end


-- @[simp]
-- lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by simp




-- lemma e14 : at_top ≤ cocompact ℝ :=
-- begin
--   intros s hs,
--   simp only [mem_at_top_sets],
--   simp only [mem_cocompact] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ := e7 ht.bounded,
--   use r + 1,
--   intros b hb,
--   apply hts,
--   intros hb',
--   have := hr _ hb',
--   simp only [real.norm_eq_abs, abs_le] at this,
--   linarith
-- end

-- lemma e16 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (s : set ℝ) :
--   norm ⁻¹' s ∈ cocompact E ↔ s ∈ (at_top : filter ℝ) :=
-- begin
--   rw [mem_at_top_sets, mem_cocompact],
--   split,
--   { rintros ⟨t, ht, hts⟩,
--     obtain ⟨r, hr⟩ := e7 ht.bounded,
--     use r + 1,
--     intros b hb,
--     obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
--     have h_norm : ∥b • (∥x∥)⁻¹ • x∥ = b := sorry,
--     have : b • (∥x∥)⁻¹ • x ∈ tᶜ,
--     { have := mt (hr (b • (∥x∥)⁻¹ • x)),
--       apply this,
--       linarith },
--     simpa [h_norm] using hts this },
--   { rintros ⟨r, hr⟩,
--     refine ⟨metric.closed_ball 0 r, proper_space.compact_ball 0 r, _⟩,
--     intros x hx,
--     simp at hx,
--     exact hr (∥x∥) hx.le },
-- end

-- lemma e17 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] :
--   map norm (cocompact E) = (at_top : filter ℝ) :=
-- begin
--   ext s,
--   exact e16 s
-- end

-- lemma e15 {α : Type*} {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (l : filter α) {f : α → E} :
--   tendsto f l (cocompact E) ↔ tendsto (norm ∘ f) l at_top :=
-- begin
--   split,
--   { exact tendsto_norm_cocompact_at_top.comp },
--   sorry
-- end


-- lemma finite_integers {M : ℝ} :
--   set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
-- begin
--     let s:= finset.Ico_ℤ (⌊-M⌋) (⌊M⌋+1),
--     suffices : {c : ℤ | |↑c| ≤ M} ⊆  s,
--     {
--       refine set.finite.subset s.finite_to_set this,
--     },
--     intros c,
--     simp [s],
--     intros h,
--     rw abs_le at h,
--     have h1 := h.1,
--     have h2 := h.2,
--     split,
--     {
--       have : (⌊-M⌋ :ℝ ) ≤ -M :=  floor_le (-M),
--       have := le_trans this h1,
--       exact_mod_cast this,
--     },
--     {
--       have : (c:ℝ ) < (⌊M⌋:ℝ) + 1,
--       {
--         calc
--         (c:ℝ) ≤ M           : h2
--         ...   < (⌊M⌋:ℝ) + 1 : M_lt_Mp1 M,
--       },

--       norm_cast at this,
--       exact this,
--     },
-- end

-- -- for `normed_space.basic`
-- lemma metric.bounded.exists_norm_le {α : Type*} [normed_group α] {s : set α} (hs : metric.bounded s) :
--   ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
-- begin
--   rcases s.eq_empty_or_nonempty with (rfl | hs'),
--   { simp },
--   obtain ⟨R₁, hR₁⟩ := hs,
--   obtain ⟨x, hx⟩ := hs',
--   use ∥x∥ + R₁,
--   intros y hy,
--   have : ∥x - y∥ ≤ R₁ := by simpa [dist_eq_norm] using hR₁ x y hx hy,
--   have := norm_le_insert x y,
--   linarith
-- end

-- -- for `order.filter.basic`
-- lemma e9 {α : Type*} (l : filter α) {s t : set α} (hst : s ∪ tᶜ ∈ l) (ht : t ∈ l) : s ∈ l :=
-- begin
--   refine mem_sets_of_superset _ (s.inter_subset_left t),
--   convert inter_mem_sets hst ht using 1,
--   ext,
--   simp only [set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
--   finish
-- end


-- lemma e10 {α : Type*} {l : filter α} {E F : Type*} [normed_group E] [normed_group F] [proper_space E]
--   {f : α → E} {g : α → F} (h : asymptotics.is_O f g l) (hf : tendsto f l (cocompact E)) :
--   tendsto g l (cocompact F) :=
-- begin
--   rw tendsto_def at ⊢ hf,
--   intros s hs,
--   simp [filter.mem_cocompact'] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ sᶜ, ∥p∥ ≤ r := (ht.bounded.subset hts).exists_norm_le,
--   rw asymptotics.is_O_iff at h,
--   obtain ⟨c, hc⟩ := h,
--   rw eventually_iff_exists_mem at hc,
--   obtain ⟨v, hv, hvfg⟩ := hc,
--   have : ∀ x ∈ v ∩ g ⁻¹' sᶜ, x ∈ f ⁻¹' metric.closed_ball (0:E) (c * r),
--   { rintros x ⟨hxv, hxgs⟩,
--     have := hr (g x) hxgs,
--     have := hvfg x hxv,
--     simp,
--     sorry },
--   have h₂ : f ⁻¹' (metric.closed_ball (0:E) (c * r))ᶜ ⊆ g ⁻¹' s ∪ vᶜ,
--   { intros x,
--     have := this x,
--     simp only [set.mem_preimage, set.mem_inter_eq, set.mem_compl_eq] at this,
--     simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq],
--     contrapose!,
--     finish },
--   have h₃ : f ⁻¹' (metric.closed_ball 0 (c * r))ᶜ ∈ l,
--   { apply hf (metric.closed_ball (0:E) (c * r))ᶜ,
--     simp only [mem_cocompact'],
--     refine ⟨metric.closed_ball (0:E) (c * r), proper_space.compact_ball 0 (c * r), _⟩,
--     simp },
--   have : g ⁻¹' s ∪ vᶜ ∈ l := mem_sets_of_superset h₃ h₂,
--   refine e9 l this hv
-- end


-- lemma tendsto_cocompact_of_antilipschitz {α β : Type*} [metric_space α] [proper_space α]
--   [metric_space β] {c : nnreal} {f : α → β} (hf : antilipschitz_with c f) :
--   tendsto f (cocompact α) (cocompact β) :=
-- begin
--   rw tendsto_iff_eventually,
--   simp only [mem_cocompact, eventually_iff_exists_mem],
--   rintros p ⟨v, hv, hvp⟩,
--   rw mem_cocompact' at hv,
--   obtain ⟨t, ht, htv⟩ := hv,
--   obtain ⟨r, hr⟩ := ht.bounded,
--   -- have := hf.bounded_preimage ht.bounded,
--   by_cases h : ∃ x, ¬ p (f x),
--   { obtain ⟨x, hx⟩ := h,
--     have hxt : f x ∈ t := htv (mt (hvp (f x)) hx),
--     refine ⟨(metric.closed_ball x (c * r))ᶜ, _, _⟩,
--     { rw mem_cocompact,
--       refine ⟨metric.closed_ball x (c * r), proper_space.compact_ball x (↑c * r), rfl.subset⟩ },
--     intros x' hx',
--     have hxx'r : r < dist (f x) (f x'),
--     { simp at hx',
--       rw dist_comm at hx',
--       rw antilipschitz_with_iff_le_mul_dist at hf,
--       have : dist x x' ≤ c * dist (f x) (f x') := hf x x',
--       have := lt_of_lt_of_le hx' this,
--       sorry }, -- this follows from the previous line except with a special case for `c = 0`
--     have := mt (hr (f x) (f x') hxt),
--     push_neg at this,
--     have := (mt (@htv (f x'))) (this hxx'r),
--     apply hvp,
--     simpa using this },
--   { push_neg at h,
--     refine ⟨set.univ, univ_mem_sets, _⟩,
--     intros x hx,
--     exact h x },
-- end

-- lemma tendsto_at_top_sum_sq :
--   tendsto (λ x : ℝ × ℝ, x.1 ^ 2 + x.2 ^ 2) (cocompact (ℝ × ℝ)) at_top :=
-- begin
--   refine tendsto_at_top_mono _
--     (tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top),
--   rintros ⟨x₁, x₂⟩,
--   simp only [prod.norm_def, real.norm_eq_abs],
--   cases max_choice (|x₁|) (|x₂|) with h h;
--   { rw [h, abs_mul_abs_self],
--     nlinarith },
-- end

-- @[simp] lemma expand_sum_01 {R : Type*} [ring R] (f : fin 2 → R ) :
-- (∑ (x : fin 2), f x) = f 0 + f 1 :=
-- by simp [fin.sum_univ_succ]
