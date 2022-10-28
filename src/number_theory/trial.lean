import number_theory.general_bernoullli_number_properties_three
import number_theory.teich_char

open_locale big_operators
local attribute [instance] zmod.topological_space

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

lemma bernoulli_measure'_eval_char_fn [normed_algebra ℚ R] [norm_one_class R] (n : ℕ)
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
        rw is_unit.unit_spec, rw units.coe_map, rw is_unit.unit_spec, sorry, },
      { sorry, }, },
    { delta zmod', apply finset.mem_univ, },
    { sorry, }, },
  sorry
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

lemma U [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, U_def p d R m χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) :=
begin
  sorry
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

lemma V [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ)
  (hn : 1 < n) :
  filter.tendsto (λ j : ℕ, V_def p d R m χ c n j)
  filter.at_top (nhds (( algebra_map ℚ R ((n + 1) / n) - (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) ) := sorry

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

lemma helpful_much {α β : Type*} [nonempty β] [semilattice_sup β] [topological_space α]
  [t2_space α] {a b : α} {f : filter β} [f.ne_bot] {g : β → α}
  (h1 : filter.tendsto g filter.at_top (nhds a))
  (h2 : filter.tendsto g filter.at_top (nhds b)) : a = b :=
begin
  haveI : (@filter.at_top β _).ne_bot,
  { apply filter.at_top_ne_bot, },
  have h3 := @filter.tendsto.lim_eq _ _ _ _ _ _ infer_instance _ h2,
  have h4 := @filter.tendsto.lim_eq _ _ _ _ _ _ infer_instance _ h1,
  rw ← h3, rw ← h4,
end

lemma helper_254 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  (algebra_map ℚ R) (1 / ↑n) * -(1 - ↑(χ (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.2 ⟨hc', p.coprime_pow_spl c m hc⟩))) * (neg_pow' p d R n)
  (zmod.unit_of_coprime c hc', (is_unit.unit (is_unit_iff_not_dvd _ _
  ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)))))) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n =
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n +
  ((algebra_map ℚ R) ((↑n + 1) / ↑n) - (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n) + 0 := sorry

noncomputable abbreviation pls_help (y : ℕ) : (zmod d)ˣ × ℤ_[p]ˣ →* (zmod (d * p^y))ˣ :=
monoid_hom.comp (units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d y hd)).symm.to_monoid_hom)
(monoid_hom.comp (mul_equiv.to_monoid_hom mul_equiv.prod_units.symm) ((monoid_hom.prod_map (monoid_hom.id (zmod d)ˣ)
(units.map (@padic_int.to_zmod_pow p _ y).to_monoid_hom))))
-- dot notation does not work for mul_equiv.to_monoid_hom?

lemma helper_255 (n y : ℕ) (x : (zmod d)ˣ × ℤ_[p]ˣ) : (∑ (a : (zmod (d * p ^ y))ˣ),
  ((asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑a *
  ↑((a : zmod (d * p^y)).val) ^ (n - 1)) • locally_constant.char_fn R (is_clopen_units_clopen_from p d y
  ((units.chinese_remainder (p.coprime_pow_spl d y hd)) a)) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) x =
  ((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (pls_help p d hd m x) *
  ↑((pls_help p d hd y x : zmod (d * p^y))) ^ (n - 1)) := sorry

/-noncomputable abbreviation supporting_fn (n y : ℕ) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R :=
⟨λ x, (((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (pls_help p d hd m x) : R) *
  ((pls_help p d hd y x : zmod (d * p^y)) : R) ^ (n - 1)),
  begin simp_rw [← helper_255], apply locally_constant.is_locally_constant, end⟩

lemma helper_256 (n y : ℕ) : (∑ (a : (zmod (d * p ^ y))ˣ),
  ((asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑a *
  ↑((a : zmod (d * p^y)).val) ^ (n - 1)) • locally_constant.char_fn R (is_clopen_units_clopen_from p d y
  ((units.chinese_remainder (p.coprime_pow_spl d y hd)) a)) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) =
  supporting_fn p d R m hd χ n y := sorry-/

lemma is_loc_const_pls_help (y : ℕ) : is_locally_constant (pls_help p d hd y) := sorry

lemma helper_256 (n y : ℕ) : (∑ (a : (zmod (d * p ^ y))ˣ),
  ((asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑a *
  ↑((a : zmod (d * p^y)).val) ^ (n - 1)) • locally_constant.char_fn R (is_clopen_units_clopen_from p d y
  ((units.chinese_remainder (p.coprime_pow_spl d y hd)) a)) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) =
  (⟨λ x, ((χ * teichmuller_character_mod_p_change_level p d R m) ((pls_help p d hd m) x) : R),
  begin apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, end⟩) *
  ((⟨λ x, ((teichmuller_character_mod_p_change_level p d R m ^ (n - 1)) ((pls_help p d hd m) x) : R) *
  ↑(pls_help p d hd y x : zmod (d * p^y)) ^ (n - 1),
  begin apply is_locally_constant.mul,
    { apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, },
    { apply is_locally_constant.comp₂,
      { apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, },
      { apply is_locally_constant.const, }, }, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)) := sorry

lemma weight_space.to_monoid_hom_apply {X A : Type*} [mul_one_class X] [topological_space X]
  [topological_space A] [mul_one_class A] (w : weight_space X A) :
  (w.to_monoid_hom : X → A) = w.to_fun := rfl

lemma helper_257 (f g : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  (((f * g) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) = f * g :=
by { ext, simp }

theorem p_adic_L_function_eval_neg_int_new [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n) :
   (p_adic_L_function' p d R m hd χ hc hc' na (neg_pow' p d R (n - 1))) = (algebra_map ℚ R) (1 / n : ℚ) *
   -(1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (neg_pow' p d R n (zmod.unit_of_coprime c hc', is_unit.unit ((is_unit_iff_not_dvd p c)
   ((nat.prime.coprime_iff_not_dvd (fact.out _)).1 (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n)) n) :=
begin
  delta p_adic_L_function',
  have h1 := filter.tendsto.add (filter.tendsto.add (U p d R m χ n) (V p d R m χ c hc' hc n hn))
    (W p d R m χ c n),
  conv at h1 { congr, skip, skip, rw ← helper_254 p d R m χ c hc hc' n, },
  symmetry, apply helpful_much h1, clear h1,
  swap 3, { apply filter.at_top_ne_bot, },
  convert trying p d R hd hc hc' na _ (λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ), (((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) a : R) *
    ((((a : zmod (d * p^j))).val)^(n - 1) : R))) • (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))) _,
  { simp only, ext, sorry, },
  { simp_rw [helper_256, helper_257],
    change filter.tendsto _ filter.at_top (nhds
    (⟨((units.coe_hom R).comp (pri_dir_char_extend' p d R m hd (χ * teichmuller_character_mod_p_change_level p d R m))), units.continuous_coe.comp (pri_dir_char_extend'_continuous p d R m hd _)⟩ *
    ⟨((neg_pow' p d R (n - 1)).to_monoid_hom), ((neg_pow' p d R (n - 1))).continuous_to_fun⟩))
    apply filter.tendsto.mul _ _,
    have calc1 : n = 1 + (n - 1), sorry,
    conv { congr, funext, conv { congr, congr, funext, rw calc1, rw pow_add, rw pow_one,
      rw ← mul_assoc, rw monoid_hom.mul_apply, rw units.coe_mul, rw mul_assoc, }, },
    convert filter.tendsto.mul _ _,
    rw metric.tendsto_at_top, intros ε hε,
    refine ⟨1, λ y hy, _⟩,
    rw dist_eq_norm, rw norm_eq_supr_norm,
    have isunit : ∀ x : (zmod d)ˣ × ℤ_[p]ˣ, is_unit (pls_help p d hd y x : zmod m), sorry,
    have calc1 : n = 1 + (n - 1), sorry,
    conv { congr, congr, funext, conv { congr, rw coe_sub, rw pi.sub_apply,
      congr, rw locally_constant.coe_continuous_map, rw helper_255 p d R m hd χ n y x,
      --rw asso_dirichlet_character_eq_char' ((χ * teichmuller_character_mod_p_change_level p d R m ^ n)) (isunit x),
      skip, rw ← to_fun_eq_coe, }, },
    simp only [pi.mul_apply], delta pri_dir_char_extend', delta neg_pow', delta neg_pow'_to_hom,
    conv { congr, congr, funext, conv { congr, congr, rw calc1, rw pow_add, rw pow_one,
      rw ← mul_assoc, rw monoid_hom.mul_apply, rw units.coe_mul, rw mul_assoc, skip,
      rw weight_space.to_monoid_hom_apply, }, },
    simp only [monoid_hom.to_fun_eq_coe], simp_rw [monoid_hom.comp_apply, units.coe_hom_apply],
    -- simp_rw [← mul_sub (↑((χ * teichmuller_character_mod_p_change_level p d R m)
    --   ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
    --   ((mul_equiv.to_monoid_hom (@mul_equiv.prod_units (zmod d) ℤ_[p] _ _).symm)
    --   (((monoid_hom.id (zmod d)ˣ).prod_map (units.map (@padic_int.to_zmod_pow p _ m).to_monoid_hom)) _))
    --   ))) _ _],
    conv { congr, congr, funext, conv { congr, rw ← mul_sub, }, },
    sorry, },
  -- add filter.tendsto.lim_eq later
  swap 3, { refine λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ), (((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) a : R) *
    ((((a : zmod (d * p^j))).val)^(n - 1) : R))) • (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a))), },
    -- refine λ j : ℕ, ∑ (a : (zmod d)ˣ × (zmod (p ^ j))ˣ),
    -- (used_map p d R m hd χ n) (a.fst, rev_coe p a.snd) • (locally_constant.char_fn R
    -- (is_clopen_units_clopen_from p d j a)), },
  swap, { convert fn_eq_sum_char_fn p d R hd _, ext,
  --rw locally_constant.coe_continuous_map,
  --convert finset.sum_apply' a,
  simp_rw ← locally_constant.to_continuous_map_smul p d R _ _,
  rw continuous_map.coe_sum,
  rw locally_constant.coe_continuous_map,
  rw finset.sum_apply,
  conv_rhs { congr, skip, funext, rw locally_constant.coe_continuous_map, },
  rw [← locally_constant.coe_fn_add_monoid_hom_apply, add_monoid_hom.map_sum
    (@locally_constant.coe_fn_add_monoid_hom ((zmod d)ˣ × ℤ_[p]ˣ) R _ _) _ (finset.univ),
    finset.sum_apply],
  simp_rw locally_constant.coe_fn_add_monoid_hom_apply,
  apply finset.sum_congr _ _,
  { ext, simp, },
  intros y hy, refl, },
  --rw filter.lim_eq_iff _,
  conv at this { congr, funext, rw linear_map.map_sum,
    conv { apply_congr, skip, rw linear_map.map_smul, rw bernoulli_measure'_eval_char_fn, rw E_c,
    simp only, --rw alg_hom.map_add,
    rw map_add, rw map_sub, rw smul_add, rw smul_sub, }, rw finset.sum_add_distrib,
    rw finset.sum_sub_distrib, },
  apply helpful_much this, clear this,
  swap 3, { apply filter.at_top_ne_bot, },
  conv { congr, skip, skip, congr, rw ← add_zero ((algebra_map ℚ R) (1 / n : ℚ) *
   -(1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (neg_pow' p d R n (zmod.unit_of_coprime c hc', is_unit.unit ((is_unit_iff_not_dvd p c)
   ((nat.prime.coprime_iff_not_dvd (fact.out _)).1 (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n)) n) ), },
  apply filter.tendsto.add,
  { convert filter.tendsto.sub (U p d R m hd χ n) (V p d R m hd χ c hc' hc n _ na'),
    { ext, rw U_def, rw V_def, congr,
      { rw simplifying, },
      { ext, congr, apply congr_arg, apply congr_arg2 _ rfl _,
        rw zmod.nat_cast_val, --apply congr_arg, apply congr_arg2 _ _ rfl, apply congr_arg2 _ rfl _, --congr,
        delta units.chinese_remainder, delta mul_equiv.prod_units, delta units.map_equiv,
        simp, }, },

    sorry, },
  { apply W, },
  sorry
end
