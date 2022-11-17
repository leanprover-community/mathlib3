import number_theory.general_bernoullli_number_properties_three
import number_theory.teich_char

open_locale big_operators
local attribute [instance] zmod.topological_space

open filter
open_locale topological_space

open_locale big_operators

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

/-- Gives the equivalence (ℤ/(m * n)ℤ)ˣ ≃* (ℤ/mℤ)ˣ × (ℤ/nℤ)ˣ -/
-- It would be nice to use units.homeomorph.prod_units instead, however no way to identify it as a mul_equiv.
abbreviation units.chinese_remainder {m n : ℕ} (h : m.coprime n) :
  (zmod (m * n))ˣ ≃* (zmod m)ˣ × (zmod n)ˣ :=
mul_equiv.trans (units.map_equiv (zmod.chinese_remainder h).to_mul_equiv) mul_equiv.prod_units

lemma h1 (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :
  filter.tendsto f.comp (nhds ((continuous_map.id (zmod d)ˣ).prod_map
    (continuous_map.id ℤ_[p]ˣ))) (nhds f) :=
begin
  convert_to filter.tendsto f.comp (nhds (continuous_map.id _)) (nhds f),
  { congr, ext a,
    { congr, },
    { simp only [continuous_map.id_apply], rw units.ext_iff, congr, }, },
  { delta filter.tendsto, delta filter.map, rw filter.le_def,
    intros x hx, simp,
    rw mem_nhds_iff at *,
    rcases hx with ⟨s, hs, h1, h2⟩,
    refine ⟨f.comp ⁻¹' s, _, _, _⟩,
    { intros a ha,
      rw set.mem_preimage at *,
      apply hs ha, },
    { refine is_open.preimage _ h1, exact continuous_map.continuous_comp f, },
    { rw set.mem_preimage, rw continuous_map.comp_id, apply h2, }, },
end

open continuous_map

private lemma preimage_gen {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] (g : C(β, γ)) {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.comp g ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [set.image_comp, set.image_subset_iff]
end

lemma helper_char (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (g : ℕ → C((zmod d)ˣ × ℤ_[p]ˣ, (zmod d)ˣ × ℤ_[p]ˣ))
  (h : filter.tendsto (λ j : ℕ, g j) filter.at_top (nhds (continuous_map.id _))) :
  filter.tendsto (λ j : ℕ, continuous_map.comp f (g j)) filter.at_top (nhds f) :=
begin
  apply topological_space.tendsto_nhds_generate_from,
  simp only [exists_prop, set.mem_set_of_eq, filter.mem_at_top_sets, ge_iff_le, set.mem_preimage, forall_exists_index, and_imp],
  simp_rw [← @set.mem_preimage _ _ f.comp _ _],
  rintros s t compt a opena hs mems,
  simp_rw [hs, preimage_gen _ compt opena],
  rw tendsto_nhds at h, simp only [filter.mem_at_top_sets, ge_iff_le, set.mem_preimage] at h,
  apply h,
  { apply continuous_map.is_open_gen compt (continuous.is_open_preimage (map_continuous _) _ opena), },
  { rw ← preimage_gen _ compt opena, rw set.mem_preimage, rw comp_id, rw ← hs, apply mems, },
end

/-lemma fn_eq_sum_char_fn [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) := sorry-/

lemma integral_loc_const_eval [normed_algebra ℚ R] [norm_one_class R]
  (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  measure.integral (bernoulli_measure' p d R hc hc' hd na) f =
  (bernoulli_measure' p d R hc hc' hd na).val f :=
begin
  delta measure.integral, simp,
  convert dense_inducing.extend_eq (measure.dense_ind_inclusion _ _) (measure.integral_cont _) _,
  apply_instance,
  apply_instance,
  apply_instance,
end

lemma trying [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R))
  (i : ℕ → locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (hf : filter.tendsto (λ j : ℕ, (i j : C((zmod d)ˣ × ℤ_[p]ˣ, R))) (filter.at_top) (nhds f)) :
  filter.tendsto (λ j : ℕ, (bernoulli_measure' p d R hc hc' hd na).1 (i j)) (filter.at_top)
  (nhds (measure.integral (bernoulli_measure' p d R hc hc' hd na) f)) :=
begin
  convert filter.tendsto.comp (continuous.tendsto (continuous_linear_map.continuous (measure.integral
     (bernoulli_measure' p d R hc hc' hd na) )) f) hf,
  ext,
  simp,
  rw integral_loc_const_eval, simp,
end

lemma locally_constant.to_continuous_map_smul (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) (r : R) :
  ((r • f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) =
  r • (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) :=
begin
  ext,
  simp only [locally_constant.coe_continuous_map, locally_constant.coe_smul,
    continuous_map.coe_smul],
end

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

-- this is the difficult simp
lemma mul_equiv.prod_units.coe_symm_apply {M : Type*} {N : Type*} [monoid M] [monoid N]
  (a : Mˣ) (b : Nˣ) : (mul_equiv.prod_units.symm (a, b) : M × N) = (a, b) :=
by { delta mul_equiv.prod_units, simp }

lemma prod.eq_fst_snd {α β : Type*} (a : α × β) : a = (a.fst, a.snd) := by refine prod.ext rfl rfl

lemma ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun {R S : Type*} [semiring R] [semiring S]
  (h : R ≃+* S) : (h : R ≃* S).inv_fun = h.inv_fun := by { ext, solve_by_elim }

lemma units.chinese_remainder_symm_apply_fst {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod d) =
  (a.fst : zmod d) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_right d (p^n)) (zmod d))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.fst),
  rw proj_fst',
end

lemma units.chinese_remainder_symm_apply_snd {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * (p^n))) : zmod (p^n)) =
  (a.snd : zmod (p^n)) :=
begin
  delta units.chinese_remainder,
  simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.symm_trans_apply],
  rw units.map_equiv, simp, rw prod.eq_fst_snd a,
  rw mul_equiv.prod_units.coe_symm_apply, rw ← mul_equiv.inv_fun_eq_symm,
  rw ring_equiv.to_monoid_hom_inv_fun_eq_inv_fun (zmod.chinese_remainder
    (nat.coprime_pow_spl p d n hd)),
  change (zmod.cast_hom (dvd_mul_left (p^n) d) (zmod (p^n)))((zmod.chinese_remainder _).inv_fun
    (↑(a.fst), ↑(a.snd))) = ↑(a.snd),
  rw proj_snd',
end

lemma padic_int.is_unit_to_zmod_pow_of_is_unit (n : ℕ) (hn : 1 < n) (x : ℤ_[p])
  (hx : is_unit (padic_int.to_zmod_pow n x)) : is_unit x :=
begin
  rw padic_int.is_unit_iff,
  by_contra h,
  have hx' := lt_of_le_of_ne (padic_int.norm_le_one _) h,
  rw padic_int.norm_lt_one_iff_dvd at hx',
  cases hx' with y hy,
  rw hy at hx,
  rw ring_hom.map_mul at hx,
  rw is_unit.mul_iff at hx,
  simp only [map_nat_cast] at hx,
  have : ¬ is_unit (p : zmod (p^n)),
  { intro h,
    set q : (zmod (p^n))ˣ := is_unit.unit h,
    have := zmod.val_coe_unit_coprime q,
    rw is_unit.unit_spec at this,
    rw nat.coprime_pow_right_iff (lt_trans zero_lt_one hn) at this,
    rw zmod.val_cast_of_lt _ at this,
    simp only [nat.coprime_self] at this,
    apply @nat.prime.ne_one p (fact.out _),
    rw this,
    conv { congr, rw ← pow_one p, },
    rw pow_lt_pow_iff _, apply hn,
    apply nat.prime.one_lt (fact.out _),
    apply_instance, },
  apply this, apply hx.1,
end

lemma helper_289 {n : ℕ} (hn : 1 < n) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  loc_const_ind_fn R p d (locally_constant.char_fn R (is_clopen_units_clopen_from p d n a)) =
  locally_constant.char_fn R (is_clopen_clopen_from p d n (↑(((units.chinese_remainder
  (nat.coprime_pow_spl p d n hd)).symm) a))) :=
begin
  ext,
  rw loc_const_ind_fn, rw ← locally_constant.to_fun_eq_coe,
  simp only, rw ind_fn, simp only, split_ifs,
  { by_cases hx : x ∈ clopen_from p d n ↑(((units.chinese_remainder
      (nat.coprime_pow_spl p d n hd)).symm) a),
    { rw (locally_constant.char_fn_one R x _).1 hx, rw ← locally_constant.char_fn_one R _ _,
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw mem_clopen_from at hx, rw hx.1, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw ← hx.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, },
    { rw (locally_constant.char_fn_zero R x _).1 hx, rw ← locally_constant.char_fn_zero R _ _,
      -- this should be a separate lemma mem_units_clopen_from
      rw set.mem_prod, rw set.mem_preimage, rw set.mem_singleton_iff, rw set.mem_singleton_iff,
      rw units.ext_iff, rw units.ext_iff, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, intro h', apply hx, rw mem_clopen_from, rw h'.1,
      rw ring_hom.to_monoid_hom_eq_coe at h', rw ring_hom.coe_monoid_hom at h',
      rw h'.2, rw units.chinese_remainder_symm_apply_fst,
      rw units.chinese_remainder_symm_apply_snd, refine ⟨rfl, rfl⟩, }, },
  rw (locally_constant.char_fn_zero R x _).1 _,
  rw mem_clopen_from, intro h', apply h, rw units.chinese_remainder_symm_apply_fst at h',
  rw units.chinese_remainder_symm_apply_snd at h', split,
  { rw h'.1, apply units.is_unit _, },
  { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn x.snd, rw ← h'.2, apply units.is_unit _, },
end

variable [fact (0 < d)]

lemma ring_equiv.eq_inv_fun_iff {α β : Type*} [semiring α] [semiring β] (h : α ≃+* β) (x : β) (y : α) :
  y = h.inv_fun x ↔ h y = x := ⟨λ h, by simp only [h, ring_equiv.inv_fun_eq_symm,
    ring_equiv.apply_symm_apply], λ h, by { rw [ring_equiv.inv_fun_eq_symm, ← h,
    ring_equiv.symm_apply_apply], }⟩

lemma proj_fst'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : zmod d) = a.fst :=
proj_fst' _ _ _ _ _

lemma proj_snd'' {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
(padic_int.to_zmod_pow n) ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
begin
  rw ← zmod.int_cast_cast,
  rw ring_hom.map_int_cast,
  rw zmod.int_cast_cast, convert proj_snd' _ _ _ _ _,
end

lemma bernoulli_measure'_eval_char_fn [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  (bernoulli_measure' p d R hc hc' hd na).val (locally_constant.char_fn R
  (is_clopen_units_clopen_from p d n a)) =
  (algebra_map ℚ R (E_c p d hc n ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) :=
begin
  delta bernoulli_measure', simp only [linear_map.coe_mk, ring_equiv.inv_fun_eq_symm],
  delta bernoulli_distribution, simp only [linear_map.coe_mk],
  rw sequence_limit_eq _ n _,
  { delta g, simp only [algebra.id.smul_eq_mul],
    convert finset.sum_eq_single_of_mem _ _ (λ b memb hb, _),
    swap 2, { refine ((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
      ((a.1 : zmod d), (a.2 : zmod (p^n)))), },
    { conv_lhs { rw ← one_mul ((algebra_map ℚ R)
        (E_c p d hc n (((zmod.chinese_remainder _).symm) (↑(a.fst), ↑(a.snd))))), },
      congr,
      rw loc_const_ind_fn, simp only [ring_equiv.inv_fun_eq_symm, locally_constant.coe_mk],
      rw ind_fn, simp only, rw dif_pos _,
      { symmetry, rw ← locally_constant.char_fn_one, rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw is_unit.unit_spec, rw units.coe_map, rw is_unit.unit_spec,
        rw ← ring_equiv.inv_fun_eq_symm,
        rw proj_fst'', rw ring_hom.coe_monoid_hom (@padic_int.to_zmod_pow p _ n),
        rw proj_snd'', simp only [eq_self_iff_true, and_self], },
      { rw ← ring_equiv.inv_fun_eq_symm,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
        split,
        { rw proj_fst'', apply units.is_unit, },
        { apply padic_int.is_unit_to_zmod_pow_of_is_unit p n hn,
          rw proj_snd'', apply units.is_unit, }, }, },
    { delta zmod', apply finset.mem_univ, },
    { rw mul_eq_zero_of_left _, rw helper_289 p d R hd hn a,
      rw ← locally_constant.char_fn_zero R _ _, rw mem_clopen_from, intro h, apply hb,
      rw units.chinese_remainder_symm_apply_snd at h,
      rw units.chinese_remainder_symm_apply_fst at h,
      rw h.2, rw ← h.1,
      rw ring_equiv.eq_inv_fun_iff, rw ← ring_equiv.coe_to_equiv,
      change (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).to_equiv b = _,
      rw prod.ext_iff, rw inv_fst', rw inv_snd',
      simp only [prod.fst_zmod_cast, eq_self_iff_true, prod.snd_zmod_cast, true_and],
      conv_rhs { rw ← zmod.int_cast_cast, }, rw ring_hom.map_int_cast,
      rw zmod.int_cast_cast, }, },
  { convert seq_lim_g_char_fn p d R n
      ((units.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm a : zmod (d * p^n)) hc hc' hd _,
    { apply helper_289 p d R hd hn a, },
    { apply fact.out _, apply_instance, }, },
end

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))
-- Idea 1 : replacing k by m + k so we can remove (hk : m ≤ k)
-- Idea 2 : Use `asso_dirichlet_character` instead to get rid of hk, since coercion on non-units
-- can be anywhere

lemma finset.sum_equiv' {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : t → α) : ∑ (x : t), f x = ∑ (x : s), f (h x) :=
begin
  apply finset.sum_bij,
  swap 5, { rintros, refine h.inv_fun a, },
  { rintros, apply finset.mem_univ _, },
  { simp only [equiv.inv_fun_as_coe, equiv.apply_symm_apply, eq_self_iff_true, implies_true_iff], },
  { simp only [equiv.inv_fun_as_coe, embedding_like.apply_eq_iff_eq, imp_self, forall_2_true_iff], },
  { refine λ a ha, ⟨h a, finset.mem_univ _, _⟩,
    simp only [equiv.inv_fun_as_coe, equiv.symm_apply_apply], },
end

lemma finset.sum_equiv {s t α : Type*} [fintype s] [fintype t] [add_comm_monoid α] (h : s ≃ t)
  (f : s → α) : ∑ (x : s), f x = ∑ (x : t), f (h.inv_fun x) :=
begin
  rw finset.sum_equiv' h, simp,
end

noncomputable def units.equiv_is_unit {α : Type*} [monoid α] : units α ≃ {x : α // is_unit x} :=
{ to_fun := λ u, ⟨u, units.is_unit u⟩,
  inv_fun := λ ⟨u, hu⟩, is_unit.unit hu,
  left_inv := λ x, units.ext_iff.2 (is_unit.unit_spec _),
  right_inv := λ x, by { apply subtype.ext_val, tidy, }, }

lemma U [normed_algebra ℚ R] [norm_one_class R] [no_zero_divisors R] (n : ℕ) (hn : 1 < n)
  (hχ : χ.is_even) (hp : 2 < p)
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) :=
begin
  delta U_def,
  have h1 := lim_even_character d p m χ na hn hχ hp,
  have h2 := filter.tendsto.const_mul ((asso_dirichlet_character
    (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p * ↑p ^ (n - 1)) h1,
  have h3 := filter.tendsto.sub h1 h2,
  clear h1 h2,
  convert h3, -- might need a tendsto_congr' here
  { clear h3,
    sorry, },
  { clear h3, sorry, },
end

lemma teichmuller_character_mod_p_change_level_def :
  teichmuller_character_mod_p_change_level p d R m = dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹ )
  (begin apply dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))), apply_instance, end) := rfl

variable (c)

noncomputable def V_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

variables (hc) (hc')

noncomputable def V_h_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n) x) *
(↑(c ^ (n - 1)) * (algebra_map ℚ R) (↑(n - 1) * (↑d * (↑p ^ k *
(↑⌊↑((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) : zmod (p^k)).val) / ((d : ℚ) * ↑p ^ k)⌋ *
(↑d * (↑p ^ k * int.fract (((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) : zmod (p^k)).val : ℕ) /
((d : ℚ) * ↑p ^ k))))^(n - 1 - 1)))) * (↑c * int.fract ((((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k)))
* (x : ℚ)) / ((d : ℚ) * ↑p ^ k)))))

--lemma coprime_prime_non_zero {n : ℕ} (hn : nat.coprime n p) : n ≠ 0 := sorry

lemma exists_V_h1_1 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) : ∃ z : ℕ,
  c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k)) (λ h, 1 + z * (d * p^(2 * k))) (λ h, 0) :=
begin
  have c_cop : c.coprime (d * p^(2 * k)) := sorry,
  by_cases (d * p^(2 * k)) = 1,
  { have k_zero : ¬ 1 < d * p^(2 * k), sorry,
    refine ⟨1, _⟩, rw dif_neg k_zero,
    /-rw h, simp_rw mul_one, simp_rw add_comm, rw fin.coe_fin_one, refine ⟨c * ((c : zmod (d * p^(2 * k)))⁻¹.val) - 1, _⟩,
    rw nat.sub_add_cancel _,
    { refl, }, -/
    sorry, },
  have h' : d * p^(2 * k) > 1, sorry,
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1, simp,
    rw ← this,
    rw zmod.val_cast_of_lt h', },
  simp_rw dif_pos h',
  conv { congr, funext, find 1 {rw ← h}, },
  conv { congr, funext, rw mul_comm z _, },
--  simp_rw mul_comm _ (d * p^(2 * k)),
  apply (zmod.nat_coe_zmod_eq_iff _ _ _).1 _,
  { apply imp p d _, },
  { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ c_cop _,
    rw zmod.cast_nat_cast _, apply zmod.coe_mul_inv_eq_one _ c_cop,
    swap 2, { refine zmod.char_p _, },
    any_goals { apply dvd_rfl, }, },
  -- apply (zmod.nat_coe_zmod_eq_iff (d * p^(2 * k)) (c *
  --   ((c : zmod (d * p^(2 * k)))⁻¹.val : zmod (d * p^k)).val) 1).1 _,
  -- { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
  --   rw zmod.cast_inv _ _, },
end

lemma exists_V_h1_3 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℕ, ((x : zmod (d * p^k)).val)^n = c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val)^n - z * (d * p^(2 * k)) :=
begin
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c k,
  --obtain ⟨z₂, hz₂⟩ := exists_V_h1_2 p d R c _ x,
  rw hz₁,
  by_cases (d * p^(2 * k)) = 1,
  { refine ⟨0, _⟩, rw zero_mul, sorry, },
  have h' : d * p^(2 * k) > 1, sorry,
  rw dif_pos h',
  rw add_pow, rw finset.sum_range_succ, rw one_pow, rw one_mul, rw nat.sub_self, rw pow_zero,
  rw one_mul, rw nat.choose_self, rw nat.cast_one, rw add_comm, rw add_mul, rw one_mul,
  simp_rw one_pow, simp_rw one_mul, simp_rw mul_pow _ (d * p^(2 * k)),
  conv { congr, funext, conv { to_rhs, congr, congr, skip, congr, apply_congr, skip,
    rw ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero H)),
    rw pow_succ (d * p^(2 * k)) _, rw ← mul_assoc _ (d * p^(2 * k)) _,
    rw mul_comm _ (d * p^(2 * k)), rw mul_assoc, rw mul_assoc, }, },
  rw ← finset.mul_sum, rw mul_assoc, rw mul_comm (d * p^(2 * k)) _,
  refine ⟨(∑ (x : ℕ) in finset.range n, z₁ ^ (n - x).pred.succ *
    ((d * p ^ (2 * k)) ^ (n - x).pred * ↑(n.choose x))) * (x : zmod (d * p^k)).val ^ n, _⟩,
  rw nat.add_sub_cancel _ _,
end

lemma sq_mul (a b : ℚ) : (a * b)^2 = a * b^2 * a := by linarith

lemma exists_V_h1_5 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : n ≠ 0) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℤ, ((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ) : ℚ)^n = (z * (d * p^(2 * k)) : ℚ) + n * (d * p^k) * ((int.floor (( (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k) : ℚ))))) * (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^(n - 1) + (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  (x : zmod (d * p^k)).val : ℕ)) / (d * p^k)))^n :=
begin
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d k), },
  conv { congr, funext, conv { to_lhs, rw [← mul_div_cancel'
        ((((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) : ℕ) : ℚ) h1,
  ← int.floor_add_fract ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) / (d * p^k) : ℚ),
  mul_add, add_pow, finset.sum_range_succ', pow_zero, one_mul, nat.sub_zero, nat.choose_zero_right,
  nat.cast_one, mul_one, ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), finset.sum_range_succ',
  zero_add, pow_one, nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero hn), nat.choose_one_right,
  mul_comm _ (n : ℚ), ← mul_assoc (n : ℚ) _ _, ← mul_assoc (n : ℚ) _ _],
  congr, congr, apply_congr, skip, conv { rw pow_succ, rw pow_succ, rw mul_assoc (d * p^k : ℚ) _,
    rw ← mul_assoc _ ((d * p^k : ℚ) * _) _, rw ← mul_assoc _ (d * p^k : ℚ) _,
    rw mul_comm _ (d * p^k : ℚ), rw ← mul_assoc (d * p^k : ℚ) _ _,
    rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← mul_assoc (d * p^k : ℚ) _ _, rw ← sq, rw sq_mul,
    rw ← pow_mul', rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_assoc (d * p^(2 * k) : ℚ) _ _,
    rw mul_assoc (d * p^(2 * k) : ℚ) _ _, rw mul_comm (d * p^(2 * k) : ℚ),
    congr, congr, congr, skip, congr, congr, skip,
    rw ← nat.cast_pow,
    rw ← nat.cast_mul d (p^k),
    rw fract_eq_of_zmod_eq _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)).val (d * p^k) _,
    rw nat.cast_mul d (p^k), rw nat.cast_pow,
    rw fract_eq_self (zero_le_and_lt_one p d _ _).1 (zero_le_and_lt_one p d _ _).2, skip,
    rw ← zmod.cast_id (d * p^k) ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)),
    rw ← zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) : ℕ) : zmod (d * p^k)), apply_congr refl, }, }, },
  rw [← finset.sum_mul, mul_div_cancel' _ h1],
  simp only [nat.cast_mul, --zmod.nat_cast_val,
    add_left_inj, mul_eq_mul_right_iff, mul_eq_zero,
    nat.cast_eq_zero, ← int.cast_coe_nat],
  norm_cast,
  refine ⟨∑ (x_1 : ℕ) in finset.range n.pred, ↑d * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val) ↑(d * p ^ k)⌋ * (↑(d * p ^ k) *
    ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val)
    ↑(d * p ^ k)⌋) ^ x_1 * ↑((((c : zmod (d * p^(2 * k)))⁻¹.val *
    (x : zmod (d * p^k)).val : ℕ) : zmod (d * p^k)).val ^ (n - (x_1 + 1 + 1))) *
    ↑(n.choose (x_1 + 1 + 1)), _⟩,
  left, apply finset.sum_congr rfl (λ y hy, rfl),
end

lemma nat.sub_ne_zero {n k : ℕ} (h : k < n) : n - k ≠ 0 := sorry

lemma helper_300 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) : (λ k : ℕ,
  (V_def p d R m χ c n k) - (((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))) *
  (c : R)^n * (U_def p d R m χ n k) + (V_h_def p d R m χ c n k))) =ᶠ[@at_top ℕ _]
  (λ k : ℕ, (∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) *
  (algebra_map ℚ R) ((↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val *
  (x : zmod (d * p^k)).val) / (↑d * ↑p ^ k)))) ^ (n - 1) *
  (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k))))) -
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n) c) *
  (↑c ^ n * (U_def p d R m χ n k)) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (((c ^ (n - 1) : ℕ) : R) * (algebra_map ℚ R) (↑(n - 1 : ℕ) *
  (↑d * (↑p ^ k * (↑⌊(((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val : ℕ) : ℚ) / (↑d * ↑p ^ k)⌋ *
  (↑d * (↑p ^ k * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) /
  (↑d * ↑p ^ k)))) ^ (n - 1 - 1)))) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ *
  (x : ℚ) / (↑d * ↑p ^ k))))) - V_h_def p d R m χ c n k) + (∑ (x : (zmod (d * p ^ k))ˣ),
  (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (x : zmod (d * p^m))) * (-↑(classical.some (exists_V_h1_3 p d R c (n - 1) k x) * (d * p ^ (2 * k))) *
  (algebra_map ℚ R) (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))) +
  ∑ (x : (zmod (d * p ^ k))ˣ), (asso_dirichlet_character
  (χ * teichmuller_character_mod_p_change_level p d R m ^ n) (x : zmod (d * p^m))) * (↑(c ^ (n - 1) : ℕ) *
  (algebra_map ℚ R) (↑(classical.some (exists_V_h1_5 p d R c (n - 1) k (nat.sub_ne_zero hn) x)) *
  (↑d * ↑p ^ (2 * k)) * (↑c * int.fract (↑(c : zmod (d * p^(2 * k)))⁻¹ * ↑x / (↑d * ↑p ^ k)))))))) := sorry
.


/-@[to_additive]
lemma tendsto_finset_prod' {α M : Type*} --[preorder ι] [nonempty ι] [semilattice_sup ι]
  [topological_space M] [comm_monoid M] [has_continuous_mul M] [has_Sup M] (β : ℕ → Type*)
  --(g : (Π (i : ℕ), β i → M) → M)
  {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) (h : tendsto (λ b : ℕ, ⨆ (i : β b), f b i) at_top (𝓝 1)) :
  tendsto (λ b, ∏ c in s b, f b c) at_top (𝓝 1) :=
begin
--  simp,
  intros U hU,
  specialize h hU,
  simp only [mem_map] at h, simp only [mem_map],
  rw mem_at_top_sets at *,
  cases h with a ha,
  simp at ha,
  simp only [ge_iff_le, set.mem_preimage] at *,
  sorry
end-/

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

@[to_additive]
lemma tendsto_finset_prod' {α M : Type*} --[preorder ι] [nonempty ι] [semilattice_sup ι]
  [topological_space M] [comm_monoid M] [has_continuous_mul M] (β : ℕ → Type*)
  [∀ b : ℕ, preorder (β b)]
  --(g : (Π (i : ℕ), β i → M) → M)
  {f : Π(i : ℕ), (β i) → M} --{x : filter ι} --{a : M}
  (s : Π(i : ℕ), finset (β i)) (h : ∀ b : ℕ, tendsto (f b) at_top (𝓝 1)) :
  tendsto (λ b, ∏ c in s b, f b c) at_top (𝓝 1) :=
begin
  intros U hU,
  simp,
  refine ⟨0, λ b hb, _⟩,
  specialize h b hU,
  sorry
end

instance {n : ℕ} : preorder (fin n) := subtype.preorder _

instance {n : ℕ} : preorder (zmod n) :=
begin
  cases n,
  { change preorder ℤ,
    apply_instance, },
  change preorder (fin n.succ),
  apply_instance,
end

--instance units_as_naturals {n : ℕ} : fintype {x : ℕ // x.coprime (d * p^n)} := sorry

example (f : Π (n : ℕ), (zmod (d * p^n))ˣ → ℝ)
  (h : ∀ n : ℕ, tendsto (f n) at_top (nhds 0)) :
  tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  intros U hU,
  simp,
  refine ⟨0, λ b hb, _⟩,
  --specialize h b,
--  set s : finset ℕ := ⟨{x : ℕ | x.coprime (d * p^b)}, _ ⟩,
--  have := tendsto_finset_sum , --_ (λ (i : ℕ) hi, h i),
--  swap 2, { exact (zmod (d * p^b))ˣ, },
  sorry
end

lemma na_tendsto (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (f : Π (n : ℕ), (zmod (d * p^n))ˣ → R)
  (h : tendsto (λ n : ℕ, ⨆ (i : (zmod (d * p^n))ˣ), ∥f n i∥) at_top (nhds 0)) :
  tendsto (λ n : ℕ, (∑ i : (zmod (d * p^n))ˣ, f n i )) at_top (nhds 0) :=
begin
  rw metric.tendsto_at_top at *,
  intros ε hε, specialize h ε hε, simp_rw dist_zero_right _ at *,
  cases h with N h,
  refine ⟨N, λ n hn, _⟩,
  specialize h n hn,
  apply lt_of_le_of_lt (na (d * p^n) (f n)) _,
  convert h, rw real.norm_eq_abs,
  symmetry,
  rw abs_eq_self,
  apply le_csupr_of_le _ _ _,
  { sorry, },
  { exact 1, },
  { apply norm_nonneg _, },
end

lemma V_h1 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ (x : ℕ), V_def p d R m χ c n x -
  (↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.mpr ⟨hc', p.coprime_pow_spl c m hc⟩))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x)) filter.at_top (nhds 0) :=
begin
  rw filter.tendsto_congr' (helper_300 p d R m χ c hd hc' hc n hn),
  conv { congr, skip, skip, congr, rw ← add_zero (0 : R), rw ← add_zero ((0 : R) + 0), },
  apply tendsto.add, apply tendsto.add,
  { sorry, },
  { sorry, },
  { simp_rw [← finset.sum_add_distrib, ← mul_add, ring_hom.map_mul, ← mul_assoc, ← add_mul,
      mul_assoc _ (algebra_map ℚ R (d : ℚ)) _, ← ring_hom.map_mul _ (d : ℚ) _, ← nat.cast_pow,
      ← nat.cast_mul d _, map_nat_cast, mul_assoc _ d _, nat.cast_mul _ (d * p^(2 * _)),
      mul_comm _ ((d * p^(2 * _) : ℕ) : R), neg_mul_eq_mul_neg, ← mul_add, mul_assoc _ (c : R) _,
      mul_assoc, mul_comm ((d * p^(2 * _) : ℕ) : R), ← mul_assoc _ _ ((d * p^(2 * _) : ℕ) : R)],
    rw tendsto_zero_iff_norm_tendsto_zero,
--    conv { congr, skip, skip, rw ← @norm_zero R _, },
    rw ← tendsto_zero_iff_norm_tendsto_zero,
    convert na_tendsto p d R na _ _,
    swap 2, { intros e x,
      refine (asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑x *
        ((-↑(classical.some (exists_V_h1_3 p d R c (n - 1) e x)) + ↑(c ^ (n - 1) : ℕ) *
        (algebra_map ℚ R) ↑(classical.some (exists_V_h1_5 p d R c (n - 1) e (nat.sub_ne_zero hn) x))) *
        (↑c * (algebra_map ℚ R) (int.fract (↑(c : zmod (d * p^(2 * e)))⁻¹ * ↑x / ↑(d * p ^ e : ℕ))))) *
      ↑(d * p ^ (2 * e) : ℕ), },
    { ext, apply finset.sum_congr,
      sorry, -- two kinds of fintype on units
      -- why is any of this needed?
      { intros y hy, congr, apply congr_arg, congr,
        rw mul_assoc (↑(n - 1) * (↑d * ↑p ^ x)) _ _,
        rw mul_assoc ↑(n - 1) (↑d * ↑p ^ x) _,
        rw mul_assoc ↑d (↑p^x) _, rw ← nat.cast_pow p x, rw ← nat.cast_mul d (p^x), rw nat.cast_pow,
        rw nat.cast_pow, }, },
    admit, },
end

lemma V_h2 [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p)
  (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ (x : ℕ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.mpr ⟨hc', p.coprime_pow_spl c m hc⟩))) *
  ↑c ^ n * U_def p d R m χ n x + V_h_def p d R m χ c n x) filter.at_top (nhds (((algebra_map ℚ R)
  ((↑n + 1) / ↑n) - (algebra_map ℚ R) (1 / ↑n) *
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p * ↑p ^ (n - 1)) *
  general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))) :=
begin
  admit,
end

lemma V [normed_algebra ℚ R] [norm_one_class R] (hd : d.coprime p) (hc' : c.coprime d) (hc : c.coprime p)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (n : ℕ) (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds (( algebra_map ℚ R ((n + 1) / n) - (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) ) :=
begin
  conv { congr, funext, rw ← sub_add_cancel (V_def p d R m χ c n j) (((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m χ n j : R) + (V_h_def p d R m χ c n j)), skip, skip,
  rw ← zero_add (((algebra_map ℚ R) ((↑n + 1) / ↑n) - (algebra_map ℚ R) (1 / ↑n) *
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
    ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n)), },
  apply filter.tendsto.add,
  { apply V_h1 p d R m χ c hd hc' hc na n hn, },
  { apply V_h2 p d R m χ c hd hc' hc n hn, },
end

lemma W [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ), ((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) x : R) *
  ((((x : zmod (d * p^j))).val)^(n - 1) : R)) • (algebra_map ℚ R) ((↑c - 1) / 2)) filter.at_top (nhds 0) :=
begin
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨1, λ n hn, _⟩,
  rw dist_eq_norm,
  rw sub_zero, simp_rw smul_eq_mul R, simp_rw ← finset.sum_mul,
  sorry
end
