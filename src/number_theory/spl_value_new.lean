import number_theory.general_bernoullli_number_properties_three
import topology.compact_open

open_locale big_operators
local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

/-- Takes an element of `(ℤ/d * p^n ℤ)ˣ` to `ℤₚˣ` : it is 1 for n = 0 and lifts a to a.
  Note that this cannot be a monoid homomorphism. -/
noncomputable abbreviation rev_coe {n : ℕ} (a : (zmod (p^n))ˣ) : ℤ_[p]ˣ :=
begin
  by_cases hn : n ≠ 0,
  { apply is_unit.unit,
    swap, exact (a : ℤ_[p]),
    change is_unit ↑(a : zmod (p^n)),
    rw ← zmod.nat_cast_val _,
    apply is_unit_padic_of_is_unit_zmod,
    have c := units.map (zmod.cast_hom (dvd_pow (dvd_refl p) hn) (zmod p)).to_monoid_hom,
    { rw zmod.nat_cast_val _,
      rw ← zmod.cast_hom_apply _,
      swap 3, { refine zmod.char_p _, },
      swap, { apply dvd_pow_self p hn, },
      rw ← ring_hom.coe_monoid_hom,
      rw ← ring_hom.to_monoid_hom_eq_coe,
      rw ← units.coe_map ((zmod.cast_hom ((dvd_pow_self p hn)) (zmod p)).to_monoid_hom) _,
      apply units.is_unit,
      apply fact_iff.2,
      apply pow_pos (nat.prime.pos infer_instance), apply fact.out, },
    { apply (nat.coprime_pow_right_iff (nat.pos_of_ne_zero hn) _ _).1,
      apply zmod.val_coe_unit_coprime, },
    { apply fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _), assumption, }, },
    { exact 1, },
end

lemma lets_see : @padic_int.lift p _ ℤ_[p] _ (λ k, padic_int.to_zmod_pow k)
  (λ k₁ k₂ hk, by {simp only [padic_int.zmod_cast_comp_to_zmod_pow]}) = ring_hom.id ℤ_[p] :=
begin
  ext,
  simp only [padic_int.lift_self, ring_hom.id_apply],
end

lemma hmm (n : ℕ) : @continuous ((zmod d)ˣ × (zmod (p^n))ˣ) ((zmod d)ˣ × ℤ_[p]ˣ) _ _
  (prod.map (@id (zmod d)ˣ) ((rev_coe p) )) :=
begin
  apply continuous.prod_mk,
  { simp only [id.def], exact continuous_fst, },
  { apply continuous_of_discrete_topology, },
end

lemma tbu (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (n : ℕ) :
  is_locally_constant (f ∘ (prod.map id ((@rev_coe p _ n) ))) :=
begin
  apply is_locally_constant.comp, apply is_locally_constant.prod_mk,
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (p ^ n))ˣ), id x.fst),
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (p ^ n))ˣ), rev_coe p x.snd),
end

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

lemma fn_eq_sum_char_fn [normed_algebra ℚ R] [norm_one_class R] (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) : filter.tendsto
  (λ j : ℕ, ∑ a : (zmod (d * (p^j)))ˣ, (f (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))  : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  (filter.at_top) (nhds f) := sorry

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

/-- Comes up everywhere ahead : returns `χω^{-n}(x)*x^{n - 1}` -/
noncomputable abbreviation used_map (n : ℕ) : C((zmod d)ˣ × ℤ_[p]ˣ, R) :=
⟨(units.coe_hom R) ∘ (χ * teichmuller_character_mod_p_change_level p d R m) ∘
  ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom) ∘
  (mul_equiv.prod_units.symm)) ∘ prod.map (monoid_hom.id (zmod d)ˣ)
  (units.map ↑(@padic_int.to_zmod_pow p _ m)) * ((neg_pow' p d R (n - 1)).to_monoid_hom),
  by { simp, apply cont_paLf', }⟩
-- Might be worthwhile to prove that `units.chinese_remainder.symm` is
--`((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom) ∘  (mul_equiv.prod_units.symm))`

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

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ j) :=
  ∑ (x : (zmod (d * p ^ k))ˣ),
  (((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p^m))).to_monoid_hom x)) * ((((x : zmod (d * p^k))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ k)))

lemma U [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, U_def p d R m hd χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) :=
begin
  sorry
end

noncomputable def M2 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ (hz : m ≤ z) (hk : k ≥ z), ∥(U_def p d R m hd χ n k) - ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))∥ < ε}

lemma M2_spec [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) (k : ℕ)
  (hk : M2 p d R m hd χ n ε hε ≤ k) :
  ∥(U_def p d R m hd χ n k) - ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))∥ < ε :=
begin
  delta M2 at hk,
  apply nat_spec' _ _ k hk,
  have := metric.tendsto_at_top.1 (U p d R m hd χ n) ε hε,
  simp_rw dist_eq_norm at this,
  refine ⟨classical.some this, classical.some_spec this⟩,
end

lemma weight_space.to_monoid_hom_apply {X A : Type*} [mul_one_class X] [topological_space X]
  [topological_space A] [mul_one_class A] (w : weight_space X A) :
  (w.to_monoid_hom : X → A) = w.to_fun := rfl

lemma zmod.cast_cast {n : ℕ} [fact (0 < n)] (l m : ℕ) (a : zmod n) (h1 : l ∣ m) :
  ((a : zmod m) : zmod l) = (a : zmod l) :=
begin
  rw ← zmod.nat_cast_val a, rw zmod.cast_nat_cast h1,
  { rw zmod.nat_cast_val, },
  { refine zmod.char_p _, },
end

lemma used_map_ext_h1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) : (((a : zmod (d * p^k)) : zmod d), (@padic_int.to_zmod_pow p _ m)
  (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p^k)) (a : zmod (d * p^k)))) =
  ((zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)) ((a : zmod (d * p^k)) : zmod (d * p^m))) :=
begin
  apply prod.ext,
  { rw zmod.chinese_remainder, simp only [ring_equiv.coe_mk, zmod.cast_hom_apply,
      prod.fst_zmod_cast],
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (dvd_mul_right d (p^m)), },
  { rw zmod.chinese_remainder,
    simp only [zmod.cast_hom_apply, ring_equiv.coe_mk, prod.snd_zmod_cast],
    rw ← padic_int.zmod_cast_comp_to_zmod_pow m k hk,
    rw ring_hom.comp_apply,
    simp only [zmod.nat_cast_val, zmod.ring_hom_map_cast, zmod.cast_hom_apply],
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (pow_dvd_pow p hk),
    rw zmod.cast_cast _ _ (a : zmod (d * p^k)) (dvd_mul_left (p^m) d), },
end

lemma used_map_ext_1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ k) (a : (zmod (d * p ^ k))ˣ) :
  (units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm)
  (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(@padic_int.to_zmod_pow p _ m))
  ((units.map ↑(zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d))) a,
  rev_coe p (units.map (@zmod.cast_hom (d * p^k) _ (dvd_mul_left _ _) (zmod (p^k)) _ _).to_monoid_hom a)))) =
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) a :=
begin
  simp only [ring_hom.to_monoid_hom_eq_coe, prod.map_mk, monoid_hom.id_apply],
  delta rev_coe,
  simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom, units.coe_map, ne.def, coe_coe, dite_not],
  rw dif_neg, ext,
  rw units.coe_map, simp_rw units.coe_map _ a,
  { delta ring_equiv.to_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
    simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom],
    rw mul_equiv.prod_units, simp,
    rw ring_equiv.to_ring_hom_eq_coe,
    rw ring_equiv.coe_to_ring_hom,
    rw ← ring_equiv.symm_apply_apply (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd))
      ((a : zmod (d* p^k)) : zmod (d * p^m)),
    apply congr_arg (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm,
    rw is_unit.unit_spec,
    rw ← used_map_ext_h1 p d R m hd n k hk,
    rw ← padic_int.cast_to_zmod_pow _ _ hk _, rw ← padic_int.cast_to_zmod_pow _ _ hk _,
    simp only [zmod.cast_hom_apply], },
    --apply used_map_ext_h1 p d R m hd n k hk, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
      apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end
.

lemma h3 {M N : Type*} [mul_one_class M] [comm_group N] (f : M →*N) (n : ℕ) (a : M) : (f^n) a = (f a)^n := rfl

-- this should already be somewhere ; also not needed
lemma h2 (k : ℕ) (χ : dirichlet_character R k) (n : ℕ) (a : (zmod k)ˣ) : (χ^n) a = (χ a)^n :=
begin
  induction n with d hd,
  { simp only [pow_zero, monoid_hom.one_apply], },
  { rw pow_succ', rw pow_succ', simp only [monoid_hom.mul_apply, mul_left_inj], rw hd, },
end

lemma teichmuller_character_mod_p_change_level_def :
  teichmuller_character_mod_p_change_level p d R m = dirichlet_character.change_level (((units.map ((algebra_map ℚ_[p] R).comp
  (padic_int.coe.ring_hom)).to_monoid_hom).comp (teichmuller_character_mod_p p) : dirichlet_character R p)⁻¹ )
  (begin apply dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))), apply_instance, end) := rfl

lemma h4 {R S T : Type*} [non_assoc_semiring R] [non_assoc_semiring S] [non_assoc_semiring T]
  (f : R →+* S) (g : S →+* T) : (g.comp f).to_monoid_hom = monoid_hom.comp g.to_monoid_hom f.to_monoid_hom :=
  by { ext, simp, }

lemma h5 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) : ((units.map (@padic_int.to_zmod p _).to_monoid_hom)
  (rev_coe p (units.map (@zmod.cast_hom (d * p^k) _ (dvd_mul_left _ _) (zmod (p^k)) _ _).to_monoid_hom a))) =
  (units.map ↑(zmod.cast_hom (dvd_mul_of_dvd_right (@dvd_pow_self _ _ p m (ne_of_gt (fact.out _))) d) (zmod p)))
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) a) :=
begin
  delta rev_coe,
  simp only [zmod.cast_hom_apply, ring_hom.coe_monoid_hom, units.coe_map, ne.def, coe_coe, dite_not],
  rw dif_neg,
  { ext, rw units.coe_map, rw is_unit.unit_spec,
    conv_rhs { rw ← monoid_hom.comp_apply, },
    rw ← units.map_comp,
    simp_rw units.coe_map _ a, simp,
    rw ←zmod.int_cast_cast,
    change (ring_hom.comp padic_int.to_zmod (int.cast_ring_hom ℤ_[p]))
      (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ) = _,
    rw ring_hom.eq_int_cast _ (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ),
    rw zmod.int_cast_cast,
    haveI : fact (0 < d * p^k) := fact_iff.2 (mul_prime_pow_pos p d k),
    rw zmod.cast_cast p (p^k) _ (dvd_pow_self p (ne_of_gt (lt_of_lt_of_le (fact.out _) hk))),
    rw zmod.cast_cast p (d * p^m) _ (dvd_mul_of_dvd_right (dvd_pow_self p (ne_of_gt (fact.out _))) d),
    { apply_instance, },
    { apply_instance, }, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
    apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end

lemma used_map_ext_2 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p ^ k))ˣ) :
  ↑((teichmuller_character_mod_p_change_level p d R m) ((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm) (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(@padic_int.to_zmod_pow p _ m))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p (units.map (@zmod.cast_hom (d * p^k) _ (dvd_mul_left _ _) (zmod (p^k)) _ _).to_monoid_hom a)))))) *
  ((algebra_map ℚ_[p] R).to_monoid_hom).comp (padic_int.coe.ring_hom.to_monoid_hom.comp ((units.coe_hom ℤ_[p]).comp
  (monoid_hom.comp (monoid_hom.comp (teichmuller_character_mod_p p)⁻¹ (units.map (@padic_int.to_zmod p _).to_monoid_hom))
    (monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ)^(n - 1))))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ((teichmuller_character_mod_p_change_level p d R m ^ n) ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk)) (zmod (d * p ^ m))).to_monoid_hom) a)).val :=
begin
  conv_rhs { rw [← nat.add_sub_cancel_left 1 n, nat.add_sub_assoc hn _, pow_add, pow_one,
    monoid_hom.mul_apply], },
  rw units.val_eq_coe, rw units.coe_mul,
  apply congr_arg2 _ _ _,
  { apply congr_arg, apply congr_arg, rw ring_hom.to_monoid_hom_eq_coe  (zmod.cast_hom _ (zmod d)),
    apply used_map_ext_1 p d R m hd n k hk a, },
  { rw teichmuller_character_mod_p_change_level_def,
    -- simp,
    -- delta does not work without the simp above, for which squeeze_simp does not work; lot of work needs to be repeated because of simp
    rw dirichlet_character.change_level,
    rw h2,
    conv_rhs { rw monoid_hom.comp_apply, }, rw monoid_hom.inv_apply, -- rw inv_pow,
    rw ← monoid_hom.comp_assoc, rw ← h4,
    rw monoid_hom.comp_apply, rw monoid_hom.comp_apply, rw units.coe_hom_apply,
    rw ← units.coe_map, rw h3, rw monoid_hom.map_pow, congr,
    apply eq_inv_of_mul_eq_one_left,
    simp_rw monoid_hom.comp_apply,
    rw ← monoid_hom.map_mul,
    convert monoid_hom.map_one (units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom),
    rw monoid_hom.inv_apply, rw ← monoid_hom.map_inv, rw ← monoid_hom.map_mul,
    convert monoid_hom.map_one _,
    rw monoid_hom.coe_snd, rw h5 p d R m n k hn hk a, rw inv_mul_eq_one, },
end

lemma used_map_ext_3 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k) (a : (zmod (d * p ^ k))ˣ) :
  ((algebra_map ℚ_[p] R).to_monoid_hom.comp (padic_int.coe.ring_hom.to_monoid_hom.comp
  ((units.coe_hom ℤ_[p]).comp(monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ ^ (n - 1)))))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ↑(((a : zmod (d * p^k)) : zmod (p^k)).val) ^ (n - 1) :=
begin
  simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_comp, ring_hom.coe_monoid_hom,
    function.comp_app, units.coe_hom_apply],
  rw h3, rw units.coe_pow, rw ring_hom.map_pow, rw ring_hom.map_pow, congr,
  rw monoid_hom.coe_snd, delta rev_coe, rw dif_pos,
  { rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)),
    rw ring_hom.comp_apply, apply congr_arg, apply congr_arg,
    rw is_unit.unit_spec,
    simp only [coe_coe, units.coe_map, ring_hom.coe_monoid_hom, zmod.cast_hom_apply,
      zmod.nat_cast_val],
    rw ←zmod.int_cast_cast, conv_rhs { rw ←zmod.int_cast_cast },
    --apply congr_arg,
    sorry, },
/-    apply congr_arg, -- if `rev_coe` is defined on zmod (p^k), this breaks, because we get (a : zmod (p^k)).val = a.val, which is false
    rw ring_hom.eq_int_cast _ (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ),
    rw zmod.int_cast_cast,
    sorry, }, -/
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
    apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end

lemma used_map_ext [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p^k))ˣ) :
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p^m))).to_monoid_hom a)) * ((((a : zmod (d * p^k)) : zmod (p^k)).val)^(n - 1) : R) :=
  -- ((algebra_map ℚ_[p] R)) (((@padic_int.coe.ring_hom p _)) ((units.coe_hom ℤ_[p])
  -- (rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p^k))).to_monoid_hom) a^(n - 1))))) :=
begin
  delta used_map, delta neg_pow', delta neg_pow'_to_hom, rw ← continuous_map.to_fun_eq_coe,
  simp_rw weight_space.to_monoid_hom_apply _,
  rw monoid_hom.to_fun_eq_coe,
  rw mul_pow,
  repeat { rw monoid_hom.comp_mul, },
  repeat { rw monoid_hom.mul_apply, },
  rw mul_comm ((algebra_map ℚ_[p] R).to_monoid_hom.comp
  (padic_int.coe.ring_hom.to_monoid_hom.comp
     ((units.coe_hom ℤ_[p]).comp (monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ ^ (n - 1)))))  _,
  sorry,
/-  simp only [monoid_hom.mul, pi.mul_apply, function.comp_apply],
  rw [monoid_hom.map_mul, units.coe_hom_apply, units.coe_hom_apply],
  rw ← mul_assoc,
  rw mul_assoc _ (↑((teichmuller_character_mod_p_change_level p d R m) _)) _,
  congr,
  { apply used_map_ext_1 p d R m hd n k hk _, },
  { -- hn used here
    apply used_map_ext_2 p d R m hd n k hn hk _, },
  { apply used_map_ext_3 p d R m n k hn hk a, }, -/
end

variable (c)

noncomputable def V_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) (hj : m ≤ j) :=
∑ (x : (zmod (d * p ^ j))ˣ), (((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^j, from mul_dvd_mul_left d (pow_dvd_pow p hj))
  (zmod (d * p^m))).to_monoid_hom x) : R) * ((((x : zmod (d * p^j))).val)^(n - 1) : R)) •
  (algebra_map ℚ R) (↑c * int.fract (((((c : zmod (d * p^(2 * j))))⁻¹ : zmod (d * p^(2 * j))) * x : ℚ) / (↑d * ↑p ^ j)))

variables (hc) (hc')

noncomputable def V_h_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) :=
dite (m ≤ k) (λ hk, ∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk)) (zmod (d * p ^ m))).to_monoid_hom) x)) *
(↑(c ^ (n - 1)) * (algebra_map ℚ R) (↑(n - 1) * (↑d * (↑p ^ k *
(↑⌊↑((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) : zmod (p^k)).val) / ((d : ℚ) * ↑p ^ k)⌋ *
(↑d * (↑p ^ k * int.fract (((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) : zmod (p^k)).val : ℕ) /
((d : ℚ) * ↑p ^ k))))^(n - 1 - 1)))) * (↑c * int.fract ((((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k)))
* (x : ℚ)) / ((d : ℚ) * ↑p ^ k))))))
(λ hk, 0)

lemma exists_V_h1_1 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ)
  (x : (zmod (d * p^k))ˣ) : ∃ z : ℕ,
  c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = 1 + z * (d * p^(2 * k)) :=
begin
  by_cases (d * p^(2 * k)) = 1,
  { rw h, simp_rw mul_one, simp_rw add_comm, sorry, },
  have h' : d * p^(2 * k) > 1, sorry,
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1, simp,
    rw ← this,
    rw zmod.val_cast_of_lt h', },
  conv { congr, funext, find 1 {rw ← h}, },
  conv { congr, funext, rw mul_comm z _, },
--  simp_rw mul_comm _ (d * p^(2 * k)),
  apply (zmod.nat_coe_zmod_eq_iff _ _ _).1 _,
  { apply imp p d _, },
  { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.cast_inv _ _ _ _ _,
    rw zmod.cast_nat_cast _, apply zmod.coe_mul_inv_eq_one,
    swap 3, { refine zmod.char_p _, },
    any_goals { apply dvd_rfl, },
    sorry, sorry, },
  -- apply (zmod.nat_coe_zmod_eq_iff (d * p^(2 * k)) (c *
  --   ((c : zmod (d * p^(2 * k)))⁻¹.val : zmod (d * p^k)).val) 1).1 _,
  -- { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
  --   rw zmod.cast_inv _ _, },
end

lemma exists_V_h1_2 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℕ, ((x : zmod (d * p^k)) : zmod (p^k)).val = (c * ((c : zmod (d * p^(2 * k))))⁻¹.val) *
  ((x : zmod (d * p^k)) : zmod (p^k)).val - z * (d * p^k) * ((x : zmod (d * p^k)) : zmod (p^k)).val :=
begin
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c _ x,
  rw hz₁,
  refine ⟨z₁ * p^k, _⟩,
  rw add_mul, rw one_mul,
  have : p^(2 * k) = p^k * p^k,
  { rw pow_mul', rw pow_two, },
  rw this, rw ← mul_assoc d (p^k), rw mul_comm (d * p^k) (p^k), rw ← mul_assoc z₁ _ _,
  rw nat.add_sub_cancel,
end

lemma exists_V_h1_3 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℕ, (((x : zmod (d * p^k))).val)^n = c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k))).val)^n - z * (p^(2 * k)) :=
begin
  rw mul_pow, rw ← mul_assoc, rw ← mul_pow,
  obtain ⟨z₁, hz₁⟩ := exists_V_h1_1 p d R c _ x,
  --obtain ⟨z₂, hz₂⟩ := exists_V_h1_2 p d R c _ x,
  rw hz₁,
  rw add_pow, rw finset.sum_range_succ, rw one_pow, rw one_mul, rw nat.sub_self, rw pow_zero,
  rw one_mul, rw nat.choose_self, rw nat.cast_one, rw add_comm, rw add_mul, rw one_mul,
  simp_rw one_pow, simp_rw one_mul, simp_rw mul_pow _ (d * p^(2 * k)),
  conv { congr, funext, conv { to_rhs, congr, congr, skip, congr, apply_congr, skip,
    rw ← nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero (finset.mem_range_sub_ne_zero H)),
    rw pow_succ (d * p^(2 * k)) _, rw ← mul_assoc _ (d * p^(2 * k)) _,
    rw mul_comm _ (d * p^(2 * k)), rw mul_assoc, rw mul_assoc, }, },
  rw ← finset.mul_sum, rw mul_assoc, rw mul_comm (d * p^(2 * k)) _, rw ← mul_assoc _ d _,
  refine ⟨(∑ (x : ℕ) in finset.range n, z₁ ^ (n - x).pred.succ *
    ((d * p ^ (2 * k)) ^ (n - x).pred * ↑(n.choose x))) * (((x : zmod (d * p^k)))).val ^ n * d, _⟩,
  rw nat.add_sub_cancel _ _,
end

lemma zmod.unit_ne_zero {n m : ℕ} [fact (1 < m)] (a : (zmod n)ˣ) (h : m ∣ n) : (a : zmod m).val ≠ 0 :=
begin
  intro h1,
  rw zmod.val_eq_zero at h1,
  have : is_unit (0 : zmod m),
  { rw ← h1, simp only [coe_coe],
    rw ← @zmod.cast_hom_apply _ _ _ _ (zmod.char_p _) h _, apply is_unit.map,
    simp only [units.is_unit], },
  rw is_unit_zero_iff at this,
  apply @zero_ne_one _ _ _,
  rw this,
  apply zmod.nontrivial,
end

lemma exists_V_h1_4 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hk : k ≠ 0)
  (x : (zmod (d * p^k))ˣ) :
  c^n * (((c : zmod (d * p^(2 * k))))⁻¹.val * ((x : zmod (d * p^k))).val)^n >
  (classical.some (exists_V_h1_3 p d R c n k x)) * (p^(2 * k)) :=
begin
  apply nat.lt_of_sub_eq_succ,
  rw ← classical.some_spec (exists_V_h1_3 p d R c _ _ x),
  swap, { apply (((x : zmod (d * p^k))).val^n).pred, },
  rw (nat.succ_pred_eq_of_pos _),
  apply pow_pos _, apply nat.pos_of_ne_zero,
  haveI : fact (1 < d * p^k), sorry,
  have := zmod.unit_ne_zero x dvd_rfl, intro h, apply this, convert h,
  --apply zmod.unit_ne_zero _ (dvd_mul_left _ _),
  apply_instance,
end

lemma sq_mul (a b : ℚ) : (a * b)^2 = a * b^2 * a := by linarith

lemma exists_V_h1_5 [normed_algebra ℚ R] [norm_one_class R] (n k : ℕ) (hn : n ≠ 0) (x : (zmod (d * p^k))ˣ) :
  ∃ z : ℤ, ((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : ℕ) : ℚ)^n = (z * (d * p^(2 * k)) : ℚ) + n * (d * p^k) * ((int.floor (( (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : ℕ)) / (d * p^k) : ℚ))))) * (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : ℕ)) / (d * p^k)))^(n - 1) + (d * p^k * int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : ℕ)) / (d * p^k)))^n :=
begin
  have h1 : (d * p^k : ℚ) ≠ 0,
  { norm_cast, apply ne_zero_of_lt, refine fact_iff.1 (imp p d k), },
  conv { congr, funext, conv { to_lhs, rw [← mul_div_cancel'
        ((((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val) : ℕ) : ℚ) h1,
  ← int.floor_add_fract ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k)) ).val) : ℕ) / (d * p^k) : ℚ),
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
    --rw units.ext,
    rw fract_eq_of_zmod_eq _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k)) ).val) : ℕ) : zmod (d * p^k)).val (d * p^k) _,
    rw nat.cast_mul d (p^k), rw nat.cast_pow,
    rw fract_eq_self (zero_le_and_lt_one p d _ _).1 (zero_le_and_lt_one p d _ _).2, skip,
    rw ← zmod.cast_id (d * p^k) ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k)) ).val) : ℕ) : zmod (d * p^k)),
    rw ← zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k)) ).val) : ℕ) : zmod (d * p^k)), apply_congr refl, }, }, },
  rw [← finset.sum_mul, mul_div_cancel' _ h1],
  simp only [nat.cast_mul, --zmod.nat_cast_val,
    add_left_inj, mul_eq_mul_right_iff, mul_eq_zero,
    nat.cast_eq_zero, ← int.cast_coe_nat],
  norm_cast,
  refine ⟨∑ (x_1 : ℕ) in finset.range n.pred, ↑d * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    ((x : zmod (d * p^k)) ).val) ↑(d * p ^ k)⌋ * ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val *
    ((x : zmod (d * p^k)) ).val) ↑(d * p ^ k)⌋ * (↑(d * p ^ k) *
    ⌊rat.mk ↑((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k)) ).val)
    ↑(d * p ^ k)⌋) ^ x_1 * ↑((((c : zmod (d * p^(2 * k)))⁻¹.val *
    ((x : zmod (d * p^k)) ).val : ℕ) : zmod (d * p^k)).val ^ (n - (x_1 + 1 + 1))) *
    ↑(n.choose (x_1 + 1 + 1)), _⟩,
  left, apply finset.sum_congr rfl (λ y hy, rfl),
end

lemma helper_1 (a b c d e f : R) : a + b + c + d - e - f = d - e + (c - f) + (a + b) := by ring

lemma helper_2 (a b c : R) (ε : ℝ) (hε : 0 < ε) (h1 : ∥a∥ < ε/3) (h2 : ∥b∥ < ε/3)
  (h3 : ∥c∥ < ε/3) : ∥a + b + c∥ < ε :=
begin
  have : ε/3 + ε/3 + ε/3 = ε, linarith,
  rw ← this,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ h3,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add h1 h2,
end

lemma helper_3 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : ℕ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k)) ).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  rw ← nat.cast_pow,
  rw ← nat.cast_mul d (p^k),
  rw fract_eq_of_zmod_eq _ ((((c : zmod (d * p^(2 * k)))⁻¹.val *
    ((x : zmod (d * p^k))).val) : ℕ) : zmod (d * p^k)).val (d * p^k) _,
  rw ← nat.cast_mul,
  rw zmod.nat_cast_val ((((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k))).val) : ℕ) : zmod (d * p^k)),
  rw zmod.cast_id,
end
--also used in the major lemma above

lemma helper_4 [normed_algebra ℚ R] [norm_one_class R] (k : ℕ) (x : (zmod (d * p^k))ˣ) :
  int.fract (((((((c : zmod (d * p^(2 * k))))⁻¹ : zmod (d * p^(2 * k))) : ℚ) *
  x : ℚ)) / (d * p^k) : ℚ) = int.fract (((((c : zmod (d * p^(2 * k))))⁻¹.val *
  ((x : zmod (d * p^k))).val : zmod(d * p^k))).val / (d * p^k) : ℚ) :=
begin
  convert helper_3 p d R c k x,
  rw nat.cast_mul,
  rw zmod.nat_cast_val _,
  rw zmod.nat_cast_val _,
  simp only [coe_coe],
  any_goals { apply imp p d _, },
end

lemma helper_5 (a b c : R) : a * b * c = a * c * b := by ring

lemma helper_6 {n : ℕ} [fact (0 < n)] (x : (zmod n)ˣ) : (x : ℚ) = ((x : zmod n).val : ℚ) :=
begin
  simp,
end

lemma helper_7 {k : ℕ} (a₁ a₂ : (zmod (d * p^k))ˣ)
  (h : (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₁ : zmod (d * p^k)) = (((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) : zmod (d * p^k)) *
  (a₂ : zmod (d * p^k))) : a₁ = a₂ :=
begin
  rw units.ext_iff, rw zmod.cast_inv at h, rw zmod.cast_nat_cast _ at h,
  have := congr_arg2 has_mul.mul (eq.refl (c : zmod (d * p^k))) h,
  simp_rw ← mul_assoc at this,
  rw zmod.mul_inv_of_unit _ _ at this, simp_rw one_mul at this,
  exact this,
  sorry,
  swap, { refine zmod.char_p _, },
  sorry,
  sorry,
  sorry,
end

noncomputable def M5 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ y ≥ z, ∥((p ^ y : ℕ) : R)∥ * (χ * teichmuller_character_mod_p_change_level p d R m ^ n).bound < ε}

lemma M5_spec [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) (y : ℕ) (hy : M5 p d R m χ n ε hε ≤ y) :
  ∥((p ^ y : ℕ) : R)∥ * (χ * teichmuller_character_mod_p_change_level p d R m ^ n).bound < ε :=
begin
  apply nat_spec _ _ y hy,
  refine ⟨classical.some (norm_lim_eq_zero' 1 p hε (le_of_lt (dirichlet_character.bound_pos
    (χ * teichmuller_character_mod_p_change_level p d R m ^ n)))), λ x hx, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  rw ← nat.one_mul (p^x),
  apply classical.some_spec (norm_lim_eq_zero' 1 p hε (le_of_lt (dirichlet_character.bound_pos
    (χ * teichmuller_character_mod_p_change_level p d R m ^ n)))) x hx,
end

instance zmod.units_fintype (n : ℕ) : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : fact (0 < n),
    { apply fact_iff.2, apply nat.pos_of_ne_zero h, },
    apply_instance, },
end

lemma helper_10 (n : ℤ) : ∥((n : ℤ_[p]) : ℚ_[p])∥ ≤ 1 := sorry

lemma helper_9 (n : ℕ) (ε : ℝ) (k : ℕ) (hk : m ≤ k) [normed_algebra ℚ R] [norm_one_class R]
  (hn : 1 < n) (hε : 0 < ε) (h1 : (d : ℚ) * ↑p ^ k ≠ 0) (h2 : d * p ^ m ∣ d * p ^ k) (h3 : k ≠ 0)
  (h4 : n - 1 ≠ 0) (h' : d * p ^ k ∣ d * p ^ (2 * k))
  (hk' : k ≥ max m (M5 p d R m χ n (ε/6) (by linarith)))
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) :
  ∥∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * ((-↑(classical.some (exists_V_h1_3 p d R c (n - 1) k x)) +
  ↑(c ^ (n - 1)) * (algebra_map ℚ R) ↑(classical.some (exists_V_h1_5 p d R c (n - 1) k h4 x))) * (↑c * (algebra_map ℚ R)
  (int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k))))) * ↑(d * p ^ (2 * k))∥ < ε / 3 :=
begin
  have : 0 < ε/3, linarith,
  simp_rw [nat.cast_mul d (p^k), nat.cast_pow, helper_4 p d R c k _],
  simp_rw [mul_assoc],
  conv { congr, congr, apply_congr, skip, conv { congr, skip, congr, skip,
    rw fract_eq_self (zero_le_and_lt_one p d k _).1 (zero_le_and_lt_one p d k _).2,
    rw ← map_nat_cast (algebra_map ℚ R) (d * p^(2 * k)), rw ← ring_hom.map_mul, rw two_mul,
    rw pow_add, rw ← mul_assoc d (p^k) _, rw nat.cast_mul _ (p^k), rw ← mul_assoc,
    rw nat.cast_mul d (p^k), rw nat.cast_pow, rw div_mul_cancel _ h1, rw ring_hom.map_mul,
    rw map_nat_cast, rw ← nat.cast_pow, rw map_nat_cast, }, },
  simp_rw [← mul_assoc], -- ← finset.sum_mul],
  --apply lt_of_le_of_lt (norm_mul_le _ _),
  apply lt_of_le_of_lt (na (d * p^k) _) _,
  have div_four_pos : 0 < ε/6, { linarith, },
  have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
  apply lt_of_le_of_lt _ div_four_lt_div_two,
  apply cSup_le _ _,
  { apply set.range_nonempty _, apply_instance, },
  { intros b hb, cases hb with y hy, rw ← hy, simp only,
    apply le_trans (norm_mul_le _ _) _,
    simp_rw [mul_assoc],
    apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (norm_nonneg _) _) _,
    { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
    rw mul_assoc,
    rw ← asso_dirichlet_character_eq_char,
    apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _ (le_of_lt (dirichlet_character.bound_pos _))) _,
    { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
    rw mul_comm, rw mul_assoc, rw ring_hom.map_int_cast,
    simp_rw [← nat.cast_pow, ← nat.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg,
      ← int.cast_add, ← int.cast_mul],
      rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
      rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
      apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
      { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
      { apply zero_le_one, },
      { rw one_mul, apply le_of_lt, rw int.cast_coe_nat, apply M5_spec,
        apply (max_le_iff.1 hk').2, }, },
end

lemma V_h1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n) --(k : ℕ) (hk : m ≤ k)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) : ∃ (z : ℕ) (hz : m ≤ z), ∀ k ≥ z,
  ∥(V_def p d R m χ c n k (le_trans hz H)) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε :=
begin
  have : ε/3 > 0, linarith,
  have div_six_pos : ε/6 > 0, linarith,
  refine ⟨max m (M5 p d R m χ n (ε / 6) div_six_pos), le_max_left _ _, λ k hk, _⟩,
  delta V_def,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  conv { congr, congr, congr, congr, apply_congr, skip, --rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1,
    conv { congr, congr, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw ← nat.cast_pow, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^(n - 1)) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
        ((x : zmod (d * p^k))).val) ^ (n - 1)),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * ((x : zmod (d * p^k))).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, },
  simp_rw [smul_eq_mul, mul_assoc,
    ring_hom.map_add, mul_add, ← add_assoc, add_mul, mul_add, finset.sum_add_distrib,
    mul_assoc ((c^(n - 1) : ℕ) : R), ← ring_hom.map_mul],
  simp_rw [helper_1 R],
  apply helper_2 R _ _ _ ε hε _ _ _,
  { rw U_def,
    conv { congr, congr, congr, skip, congr, skip, congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1, },
    convert this,
    rw norm_eq_zero,
    rw sub_eq_zero,
    simp_rw [helper_3 p d R, helper_4 p d R, finset.mul_sum, ← mul_assoc, smul_eq_mul, ← mul_assoc],
    apply finset.sum_bij,
    { intros a ha, apply finset.mem_univ _, },
    swap 4, { intros a ha, apply is_unit.unit,
      swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
      sorry, },
    { intros a ha, conv_rhs { rw helper_5 R _ (c^n : R) _, rw mul_assoc, rw mul_assoc, },
      rw mul_assoc, apply congr_arg2,
      { simp_rw ← units.coe_hom_apply,
        rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul, congr,
        rw units.ext_iff, simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
          ring_hom.to_monoid_hom_eq_coe, units.coe_map,
          ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
        rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
        rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
        rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
        sorry,
        any_goals { refine zmod.char_p _, },
        any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
      { rw ring_hom.map_mul, rw fract_eq_self _, rw mul_div_cancel' _,
        rw ← mul_assoc, rw ring_hom.map_mul, rw ← mul_assoc, rw map_nat_cast,
        rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
        { rw nat.cast_pow, rw ← pow_succ', rw nat.sub_add_cancel _, sorry, }, --might need change
        { simp_rw [helper_6],
          rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
          { rw nat.cast_pow, congr, rw is_unit.unit, },
          { apply (zero_le_and_lt_one p d _ _).1, },
          { apply (zero_le_and_lt_one p d _ _).2, }, },
        { apply h1, },
        { apply (zero_le_and_lt_one p d _ _).2, },
        { apply (zero_le_and_lt_one p d _ _).1, }, }, },
    { intros a₁ a₂ ha₁ ha₂ h,
      simp only at h, rw units.ext_iff at h,
      rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
      simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
      apply helper_7 p d c _ _ h, },
    { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
      refine ⟨is_unit.unit _, _, _⟩,
      { exact c * (b : zmod (d * p^k)), },
      { apply is_unit.mul _ (units.is_unit _), sorry, },
      { apply finset.mem_univ _, },
      { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
        rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
        { sorry, },
        { refine zmod.char_p _, },
        { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, }, },
  { convert this, rw norm_eq_zero,
    rw sub_eq_zero, delta V_h_def, rw dif_pos, },
    -- { rw nat.cast_mul, apply finset.sum_congr rfl _,
    --   intros x hx, convert refl _,
    --   apply congr_arg, apply_instance, apply congr_arg2 _ rfl _, },
    -- apply hk,
    -- simp_rw [units.coe_hom_apply],
    -- apply finset.sum_congr rfl (λ x hx, _),
    -- simp_rw mul_assoc, apply congr_arg2 _ rfl _,
    --apply (max_le_iff.1 hk).1, },
  { simp_rw [← finset.sum_add_distrib, ← mul_add, ring_hom.map_mul, ← mul_assoc, ← add_mul,
      mul_assoc _ (algebra_map ℚ R (d : ℚ)) _, ← ring_hom.map_mul _ (d : ℚ) _, ← nat.cast_pow,
      ← nat.cast_mul d _, map_nat_cast, mul_assoc _ d _, nat.cast_mul _ (d * p^(2 * k)),
      mul_comm _ ((d * p^(2 * k) : ℕ) : R), neg_mul_eq_mul_neg, ← mul_add, mul_assoc _ (c : R) _,
      mul_assoc, mul_comm ((d * p^(2 * k) : ℕ) : R), ← mul_assoc _ _ ((d * p^(2 * k) : ℕ) : R)],
    convert helper_9 p d R m χ c n ε k (max_le_iff.1 hk).1 hn hε h1 h2 h3 h4 h' hk na,
    ext, congr, apply congr_arg, congr, ext, simp_rw [nat.cast_mul, nat.cast_pow, mul_assoc],
    simp only [nat.cast_mul], },
--  { refl, }, -- get a det timeout if i remove this
end

noncomputable def M1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(V_def p d R m hd χ c n k) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε}

lemma M1_spec [normed_algebra ℚ R] [norm_one_class R] --(hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : M1 p d R m hd χ c hc hc' n ε hε ≤ k) :
  ∥(V_def p d R m hd χ c n k) - ((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n k) - (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta M1 at hk,
  apply nat_spec' _ _ k hk,
  refine ⟨classical.some (V_h1 p d R m hd χ c hc hc' n hn na ε hε),
    classical.some_spec (V_h1 p d R m hd χ c _ _ n hn na ε hε)⟩,
end
.
lemma helper_13 (a b c d e f : R) : a + b + c + (d - e - f) = a + b + (c - f) + (d - e) := by ring

lemma nat.le_two_mul_of_half_le (k n : ℕ) (hn : k/2 ≤ n) : k ≤ 2 * n := by { sorry }

lemma V_h2_1 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m ((M5 p d R m χ n (ε / 6) (by linarith))/2) ≤ k) :
  ∥(algebra_map ℚ R) ((n - 1 : ℕ) * (d * p^k) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n))) -
  (n * (d * p^k)) * (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta U_def,
  have div_four_pos : 0 < ε/6, { linarith, },
--  refine ⟨(M5 p d R m χ n (ε / 6) div_four_pos)/2, λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ), sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n ≠ 0, sorry,
  have h5 : ε = ε/3 + ε/3 + ε/3, linarith,
  have h6 : 0 < ε/3, linarith,
  conv { congr, congr, congr, congr, rw finset.mul_sum, apply_congr, skip,
    rw mul_smul_comm,
    rw h2,
    rw fract_eq_self (zero_le_and_lt_one p d k x).1 (zero_le_and_lt_one p d k x).2,
    rw ← ring_hom.map_mul, rw mul_assoc, rw mul_div_cancel' _ h1,
    rw ← nat.cast_mul (n - 1) _, rw map_nat_cast,
    rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, --skip,
    rw smul_eq_mul, rw mul_assoc, rw ← nat.cast_pow, rw ← nat.cast_mul, rw ← mul_assoc,
    rw mul_comm _ (n - 1), rw mul_assoc, rw ← pow_succ',
    rw nat.sub_add_cancel (le_of_lt hn),
    conv { congr, congr, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      --rw ← nat.cast_pow,
      rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw nat.cast_mul,
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^n) _, rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
        (x : zmod (d * p^k)).val) ^ n),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, skip,
      rw ← zmod.nat_cast_val, apply_congr, skip, rw h2, rw nat.cast_mul, rw nat.cast_pow p,
      rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
      simp_rw [ring_hom.map_add, mul_add, finset.sum_add_distrib, ← add_assoc, ← add_sub, helper_13],
      conv { congr, skip, rw h5, },
      apply lt_of_le_of_lt (norm_add_le _ _) _,
      apply add_lt_add,
      { apply lt_of_le_of_lt (norm_add_le _ _) _,
        apply add_lt_add,
        { simp_rw [← finset.sum_add_distrib, ← mul_add], --nat.cast_mul, nat.cast_pow, ],
          convert lt_of_le_of_lt (na (d * p^k) _) _,
          have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
          apply lt_of_le_of_lt _ div_four_lt_div_two,
          apply cSup_le _ _,
          { apply set.range_nonempty _, apply_instance, },
          { intros b hb, cases hb with y hy, rw ← hy, simp only,
            apply le_trans (norm_mul_le _ _) _,
            simp_rw [mul_assoc],

            conv { congr, congr, skip, congr, congr, skip, conv { rw ← mul_assoc, rw ← mul_assoc, --congr, skip, --rw mul_assoc _ d _,
              rw nat.cast_mul, rw ← neg_mul, --rw mul_assoc _ (d : ℚ) _,
              rw ring_hom.map_mul, --rw ring_hom.map_mul,
            --rw map_nat_cast,
            conv { congr, skip, congr, skip, congr, skip, rw ← nat.cast_pow, rw map_nat_cast, },
            rw ← mul_assoc, rw ← add_mul, }, },
            simp_rw [← mul_assoc], --rw ← finset.sum_mul,
            apply le_trans (mul_le_mul le_rfl (norm_mul_le _ _) _ (norm_nonneg _)) _,
            { apply norm_nonneg _, },
            rw ← asso_dirichlet_character_eq_char,
            apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _
              (le_of_lt (dirichlet_character.bound_pos _))) _,
            { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
            rw mul_comm, rw mul_assoc, rw ring_hom.map_mul, rw ring_hom.map_int_cast,
            rw map_nat_cast,
            simp_rw [← nat.cast_pow, ← nat.cast_mul, ← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg,
              ← int.cast_add, ← int.cast_mul],
            rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
            rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
            apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
            { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
            { apply zero_le_one, },
            { rw one_mul, apply le_of_lt, rw int.cast_coe_nat, apply M5_spec,
              apply nat.le_two_mul_of_half_le _ _ (max_le_iff.1 hk).2, }, }, },
--            ring_hom.map_mul _ _ _, ← mul_assoc (c^n : R) _ _, map_nat_cast], sorry, },
        { delta V_h_def, rw dif_pos (max_le_iff.1 hk).1,
          convert h6,
          rw norm_eq_zero,
          -- convert ← @norm_zero R _,
          -- apply congr_arg,
          rw sub_eq_zero, rw finset.mul_sum, apply finset.sum_congr rfl (λ x hx, _),
          rw mul_comm ((n : R) * _) _,
          rw mul_assoc _ _ ((n : R) * _), apply congr_arg2 _ rfl _,
          rw ← nat.pred_eq_sub_one,
          rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          rw pow_succ _ (n.pred.pred),
          have : 0 < n, sorry,
          rw ← nat.succ_pred_eq_of_pos this,
          rw pow_succ' c n.pred,
          rw nat.cast_mul _ c,
          rw nat.succ_pred_eq_of_pos this,
          rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
            mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
          rw ← mul_assoc, rw ← mul_assoc _ _ (c : R), rw mul_comm ((n - 1 : ℕ) : R) _,
          rw mul_assoc, rw mul_assoc, rw mul_assoc _ _ (n * (d * p^k : ℕ) : R),
          apply congr_arg2 _ rfl _, simp_rw [mul_assoc], apply congr_arg2 _ rfl _,
          ring, repeat { apply congr_arg2 _ _ rfl },
          conv_rhs { rw mul_assoc, rw mul_comm, },
          simp_rw [← h2, ← zmod.nat_cast_val],
          conv_rhs { congr, skip, rw h2, rw ← nat.cast_mul, }, }, },
      { convert h6, rw norm_eq_zero,
        -- rw ← @norm_zero R _, apply congr_arg,
        rw sub_eq_zero,
        apply finset.sum_congr _ (λ x hx, _),
        { convert refl _, apply_instance, },
        { apply congr_arg2 _ rfl _, rw mul_assoc ((n - 1 : ℕ) : R) _ _, }, }, -- why does rw not solve this?
      --convert_to ∥_ + _ + _ + ((0 : R) - _)∥ < ε,
end
.

lemma helper_11 (ε : ℝ) (hε : 0 < ε) : 0 < ε /2 / 6 :=
begin
  apply div_pos (half_pos hε) _,
  linarith,
end

lemma V_h2_2 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε) / 2) ≤ k) :
  ∥(n * (d * p^k) : R) * (V_h_def p d R m χ c n k) -
  ((n - 1 : ℕ) * (d * p^k) : R) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)∥ < ε :=
begin
  have div_two_div_six_pos : 0 < ε / 2 / 6, sorry,
  --refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) div_two_div_six_pos / 2), λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ), sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  rw norm_sub_rev,
  rw ← sub_add_sub_cancel,
  swap, { refine (algebra_map ℚ R) ((n - 1 : ℕ) * (d * p^k) : ℚ) * (U_def p d R m hd χ n k) -
    (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
    ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
    (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
    ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n))), },
  conv { congr, skip, rw ← half_add_self ε, },
  rw add_div,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ (V_h2_1 p d R m χ c hd n hn na _ (half_pos hε) _ _),
  rw [mul_sub, mul_one, sub_mul, sub_sub, add_comm, ← sub_sub, ← sub_add, add_sub_assoc,
    ring_hom.map_mul, ← nat.cast_pow p _, ← nat.cast_mul d _, ← nat.cast_pow p _,
    ← nat.cast_mul d _, map_nat_cast, map_nat_cast, sub_self, zero_add],
  convert half_pos hε, rw norm_eq_zero, rw sub_eq_zero, delta U_def,
  conv_rhs { congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, },
  rw finset.mul_sum,
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   sorry, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) * (d * p^k : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) * (d * p^k : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5, rw mul_comm, rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      sorry,
      any_goals { refine zmod.char_p _, },
      -- { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
    { --rw ring_hom.map_mul,
      rw nat.cast_mul d _, rw nat.cast_pow p _,
      rw helper_4 p d R c k a, rw fract_eq_self _, rw mul_div_cancel' _,
      simp_rw [mul_assoc], apply congr_arg2 _ rfl _, rw ← nat.cast_pow c, rw map_nat_cast,
      rw map_nat_cast,
      rw ← mul_assoc, rw mul_comm _ ((c^n : ℕ) : R), rw mul_assoc, apply congr_arg2 _ rfl _,
      -- rw ring_hom.map_mul, -- rw ← mul_assoc,
      -- rw map_nat_cast,
      conv_rhs { rw h5, }, rw ← nat.cast_pow p _, rw ← nat.cast_mul d _, rw fract_eq_val,
      rw mul_comm (↑(d * p^k)) _, rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) (d * p^k),
      rw ← ring_hom.map_mul, rw div_mul_cancel _, rw map_nat_cast, rw ← pow_succ',
      rw nat.sub_one, rw nat.add_one, rw nat.succ_pred_eq_of_pos _,
      rw ← map_nat_cast (algebra_map ℚ R) _, congr, rw ← map_nat_cast (algebra_map ℚ R) _,
      apply congr_arg,
      rw is_unit.unit_spec,
      { apply lt_trans _ hn, apply nat.zero_lt_one, },
--      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, --might need change
      { apply h1, },
        -- { simp_rw [helper_6],
        --   rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
        --   { rw nat.cast_pow, congr, },
        --   { apply (zero_le_and_lt_one p d _ _).1, },
        --   { apply (zero_le_and_lt_one p d _ _).2, }, },
        -- { apply h1, },
      { apply (zero_le_and_lt_one p d _ _).2, },
      { apply (zero_le_and_lt_one p d _ _).1, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7 p d c _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), sorry, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { sorry, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
--  simp_rw [← sub_add, sub_add_eq_add_sub], delta U_def, simp_rw [used_map_ext],
end

lemma V_h2_3 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m ((M5 p d R m χ n (ε / 6) (by linarith))) ≤ k) :
  ∥(algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n) * (algebra_map ℚ R) (1 / (d * p^k)))) -
  n * (V_h_def p d R m χ c n k)∥ < ε :=
begin
  delta U_def,
  have div_four_pos : 0 < ε/6, { linarith, },
--  refine ⟨(M5 p d R m χ n (ε / 6) div_four_pos)/2, λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)).val : ℚ), sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n ≠ 0, sorry,
  have h5 : ε = ε/3 + ε/3 + ε/3, linarith,
  have h6 : 0 < ε/3, linarith,
  have h7 : (d * p^(2 * k) : ℚ) / (d * p^k) = (p^k : ℚ), sorry,
  conv { congr, congr, congr, congr, rw finset.mul_sum, apply_congr, skip,
    rw smul_eq_mul, -- rw mul_smul_comm,
    rw h2,
    rw fract_eq_self (zero_le_and_lt_one p d k x).1 (zero_le_and_lt_one p d k x).2,
    -- rw ← ring_hom.map_mul, -- rw mul_assoc, rw mul_div_cancel' _ h1,
    -- rw ← nat.cast_mul (n - 1) _, rw map_nat_cast,
    rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, --skip,
    -- rw smul_eq_mul,
    rw mul_assoc, rw ← map_nat_cast (algebra_map ℚ R) _,
    rw ← ring_hom.map_pow, rw ← ring_hom.map_mul, rw mul_div _ _ (d * p^k : ℚ), rw ← pow_succ', -- rw ← nat.cast_pow, rw ← nat.cast_mul,
    rw ← mul_assoc,
    -- rw mul_comm _ (n - 1), rw mul_assoc, rw ← pow_succ',
    rw nat.sub_add_cancel (le_of_lt hn),
    conv { congr, congr, skip, skip, --rw rev_coe, rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      rw ← nat.cast_pow,
      rw classical.some_spec (exists_V_h1_3 p d R c _ _ x),
      -- rw nat.cast_mul,
      rw nat.cast_sub (le_of_lt (exists_V_h1_4 p d R c _ _ h3 x)),
      rw sub_eq_neg_add _ _,
      rw nat.cast_mul (c^n) _,
      -- rw ← map_nat_cast (algebra_map ℚ R) (((c : zmod (d * p^(2 * k)))⁻¹.val *
      --   (x : zmod (d * p^k)).val) ^ n),
      rw nat.cast_pow ((c : zmod (d * p^(2 * k)))⁻¹.val * (x : zmod (d * p^k)).val) _,
      rw classical.some_spec (exists_V_h1_5 p d R c _ _ h4 x), }, skip,
      rw ← zmod.nat_cast_val, apply_congr, skip, rw h2, rw nat.cast_mul, rw nat.cast_pow p,
      rw ← nat.cast_mul _ (x : zmod (d * p^k)).val, rw ← ring_hom.map_pow, },
      simp_rw [add_div, ring_hom.map_add, mul_add, add_div, ring_hom.map_add, mul_add,
        finset.sum_add_distrib, ← add_assoc, ← add_sub, helper_13],
      conv { congr, skip, rw h5, },
      apply lt_of_le_of_lt (norm_add_le _ _) _,
      apply add_lt_add,
      { apply lt_of_le_of_lt (norm_add_le _ _) _,
        apply add_lt_add,
        { simp_rw [← finset.sum_add_distrib, ← mul_add], --nat.cast_mul, nat.cast_pow, ],
          convert lt_of_le_of_lt (na (d * p^k) _) _,
          have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
          apply lt_of_le_of_lt _ div_four_lt_div_two,
          apply cSup_le _ _,
          { apply set.range_nonempty _, apply_instance, },
          { intros b hb, cases hb with y hy, rw ← hy, simp only,
            apply le_trans (norm_mul_le _ _) _,
            simp_rw [mul_assoc],

            conv { congr, congr, skip, congr, congr, skip, conv { rw ← mul_assoc, rw ← mul_assoc, --congr, skip, --rw mul_assoc _ d _,
              rw mul_assoc, rw ← mul_div, rw h7, rw ring_hom.map_mul, congr, skip, rw ← nat.cast_pow p k,
              rw map_nat_cast, }, },
            conv { congr, congr, congr, skip, congr, congr, rw nat.cast_mul, rw nat.cast_mul,
              rw nat.cast_pow, rw ← neg_mul, rw ← mul_div, rw h7, rw ring_hom.map_mul, rw ← nat.cast_pow, rw map_nat_cast, },
            --   rw nat.cast_mul, rw ← neg_mul, --rw mul_assoc _ (d : ℚ) _,
            --   rw ring_hom.map_mul, --rw ring_hom.map_mul,
            -- --rw map_nat_cast,
            -- conv { congr, skip, congr, skip, congr, skip, rw ← nat.cast_pow, rw map_nat_cast, },
            -- rw ← mul_assoc, rw ← add_mul, }, },
            simp_rw [← mul_assoc], --rw ← finset.sum_mul,
            apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl (norm_nonneg _) _) _,
            { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
            rw ← asso_dirichlet_character_eq_char,
            rw mul_comm (∥(algebra_map ℚ R) ↑(n - 1)∥) _, rw mul_assoc,
            apply le_trans (mul_le_mul (le_of_lt (dirichlet_character.lt_bound _ _)) le_rfl _
              (le_of_lt (dirichlet_character.bound_pos _))) _,
            { apply (mul_nonneg (norm_nonneg _) (norm_nonneg _)), },
            rw mul_comm, rw mul_assoc, rw ring_hom.map_mul, rw ring_hom.map_int_cast,
            rw map_nat_cast, simp_rw [← add_mul],
            rw ← ring_hom.map_int_cast (algebra_map ℚ R), rw ← ring_hom.map_mul, rw ← ring_hom.map_add,
            --rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R), --rw ← ring_hom.map_mul, rw ← ring_hom.map_add,
            simp_rw [← int.cast_coe_nat, ← int.cast_mul, ← int.cast_neg, ← int.cast_add, ring_hom.map_int_cast],
            rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
            rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
            apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ _) _,
            { apply (mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _))), },
            { apply zero_le_one, },
            { rw one_mul, -- apply le_of_lt,
              rw int.cast_coe_nat (p^k),
              apply le_trans (mul_le_mul (norm_mul_le _ _) le_rfl
                (le_of_lt (dirichlet_character.bound_pos _)) _) _,
              { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
              rw ← ring_hom.map_int_cast (algebra_map ℚ_[p] R),
              rw ← padic_int.coe_coe_int, rw norm_algebra_map, rw norm_one_class.norm_one, rw mul_one,
              rw mul_assoc,
              apply le_trans (mul_le_mul (helper_10 _ _) le_rfl _ (zero_le_one)) _,
              { apply mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _)), },
              rw one_mul, apply le_of_lt,
              -- rw mul_comm _ ↑(p^k),
              apply M5_spec, apply (max_le_iff.1 hk).2, }, }, },
--            ring_hom.map_mul _ _ _, ← mul_assoc (c^n : R) _ _, map_nat_cast], sorry, },
        { delta V_h_def, rw dif_pos (max_le_iff.1 hk).1,
          convert h6,
          rw norm_eq_zero,
          -- convert ← @norm_zero R _,
          -- apply congr_arg,
          rw sub_eq_zero, rw finset.mul_sum, apply finset.sum_congr rfl (λ x hx, _),
          rw mul_comm (n : R) _,
          rw mul_assoc _ _ (n : R), rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc,
          apply congr_arg2 _ rfl _,
          rw ← nat.pred_eq_sub_one,
          rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          rw pow_succ _ (n.pred.pred),
          have : 0 < n, sorry,
          rw ← nat.succ_pred_eq_of_pos this,
          rw pow_succ' c n.pred,
          rw nat.cast_mul _ c,
          rw nat.succ_pred_eq_of_pos this,
          rw nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hn),
          simp_rw [← mul_assoc (d : ℚ) _ _, ← nat.cast_pow p _, ← nat.cast_mul d _,
            mul_pow, ring_hom.map_mul, map_nat_cast, nat.pred_eq_sub_one],
          rw ← mul_assoc, rw ← mul_assoc ((c^(n - 1) : ℕ) : R) (((n - 1 : ℕ) : R) * _) _,
          rw ← mul_assoc ((c^(n - 1) : ℕ) : R) ((n - 1 : ℕ) : R) _,
          rw mul_comm _ ((n - 1 : ℕ) : R), rw mul_assoc ((n - 1 : ℕ) : R) _ _,
          rw mul_assoc ((n - 1 : ℕ) : R) _ _, rw mul_assoc ((n - 1 : ℕ) : R) _ _,
          apply congr_arg2 _ rfl _, rw ← mul_div,
          simp_rw [ring_hom.map_mul, map_nat_cast, mul_assoc], apply congr_arg2 _ rfl _,
          rw ← mul_div, rw mul_div_left_comm, rw div_self, rw mul_one,
          ring, simp_rw [nat.cast_mul _ (x : zmod (d * p^k)).val, ← h2, zmod.nat_cast_val],
          repeat { apply congr_arg2 _ _ rfl, },
          simp_rw [ring_hom.map_mul], rw mul_assoc, apply congr_arg2 _ rfl _, rw mul_comm,
          { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, }, },
      { convert h6, rw norm_eq_zero,
        -- rw ← @norm_zero R _, apply congr_arg,
        rw sub_eq_zero,
        apply finset.sum_congr _ (λ x hx, _),
        { convert refl _, apply_instance, },
        { rw mul_comm ((algebra_map ℚ R) ↑(n - 1)) _, rw mul_assoc, apply congr_arg2 _ rfl _,
          rw ← mul_div, rw ring_hom.map_mul, rw map_nat_cast, rw map_nat_cast, rw ← mul_assoc,
          rw mul_assoc (↑(n - 1) * ↑(c ^ n)) _ _, apply congr_arg2 _ rfl _, rw ← ring_hom.map_mul,
          rw mul_one_div, }, }, -- why does rw not solve this?

end

lemma V_h2_4 [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε)) ≤ k) :
  ∥(n : R) * (V_h_def p d R m χ c n k) -
  ((n - 1 : ℕ) : R) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)∥ < ε :=
begin
  -- have h1 := V_h2_2 p d R m hd χ c hc' hc n hn na (∥(d * p^k : R)∥ * ε) _ k _,
  -- rw mul_comm ↑n _ at h1, rw mul_comm ↑(n - 1) _ at h1, rw mul_assoc at h1,
  -- rw mul_assoc (d * p^k : R) _ _ at h1, rw mul_assoc (d * p^k : R) _ _ at h1, rw ← mul_sub at h1,
  -- rw ← nat.cast_pow p _ at h1, rw ← nat.cast_mul d _ at h1, rw ← map_nat_cast (algebra_map ℚ R) at h1,
  -- rw ← smul_eq_mul at h1,
  -- rw @algebra_map_smul _ _ R _ _ _ _ _ _ _ ((d * p^k : ℕ) : ℚ) _ at h1, rw norm_smul at h1,
  -- rw map_nat_cast at h1,
  have div_two_div_six_pos : 0 < ε / 2 / 6, sorry,
  --refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) div_two_div_six_pos / 2), λ k hk, _⟩,
  have h1 : (d * p^k : ℚ) ≠ 0, sorry,
  have h2 : d * p^m ∣ d * p^k, sorry,
  have h3 : k ≠ 0, sorry,
  have h4 : n - 1 ≠ 0, sorry,
  have h5 : ∀ (x : (zmod (d * p^k))ˣ), (x : ℚ) = ((x : zmod (d * p^k)) : ℚ), sorry,
  have h' : d * p ^ k ∣ d * p ^ (2 * k), sorry,
  rw norm_sub_rev,
  rw ← sub_add_sub_cancel,
  swap, { refine (algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (U_def p d R m hd χ n k) -
  (∑ (x : (zmod (d * p ^ k))ˣ), ↑((χ * teichmuller_character_mod_p_change_level p d R m ^ n)
  ((units.map (zmod.cast_hom (show d * p ^ m ∣ d * p ^ k, from mul_dvd_mul_left d (pow_dvd_pow p (max_le_iff.1 hk).1))
  (zmod (d * p ^ m))).to_monoid_hom) x)) * (((n - 1 : ℕ) : R) * ((c^n : ℕ) : R) * ((algebra_map ℚ R)
  ((d * p^k : ℚ) * int.fract (↑((c : zmod (d * p^(2 * k)))⁻¹ : zmod (d * p^(2 * k))) * ↑x / ↑(d * p ^ k)))^n) * (algebra_map ℚ R) (1 / (d * p^k)))), },
  conv { congr, skip, rw ← half_add_self ε, },
  rw add_div,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply add_lt_add _ (V_h2_3 p d R m χ c hd n hn na _ (half_pos hε) _ _),
  rw [mul_sub, mul_one, sub_mul, sub_sub, add_comm, ← sub_sub, ← sub_add, add_sub_assoc, map_nat_cast, sub_self, zero_add],
  -- rw [ring_hom.map_mul, ← nat.cast_pow p _, ← nat.cast_mul d _, ← nat.cast_pow p _,
  --   ← nat.cast_mul d _, map_nat_cast],
  convert half_pos hε, rw norm_eq_zero, rw sub_eq_zero, delta U_def,
  conv_rhs { congr, skip, apply_congr, skip, rw used_map_ext p d R m hd χ n k (le_of_lt hn) (max_le_iff.1 hk).1 _, },
  rw finset.mul_sum,
  apply finset.sum_bij,
  { intros a ha, apply finset.mem_univ _, },
  swap 4, { intros a ha, apply is_unit.unit,
   swap, { exact (c : zmod (d * p^(2 * k)))⁻¹.val * (a : zmod (d * p^k)).val, },
   sorry, },
  { intros a ha,
    --rw ← asso_dirichlet_character_eq_char, rw ← asso_dirichlet_character_eq_char,
    rw smul_eq_mul, rw mul_comm _ ((algebra_map ℚ R) (c^n : ℚ)),
    rw ← mul_assoc ((n - 1 : ℕ) : R) _ _,
    rw mul_assoc (((n - 1 : ℕ) : R) * (algebra_map ℚ R) (c^n : ℚ)) _ _,
    conv_rhs { congr, skip, conv { congr, skip, rw mul_assoc, }, rw ← mul_assoc, },
    conv_rhs { rw ← mul_assoc, rw helper_5, rw mul_comm, rw ← asso_dirichlet_character_eq_char, },
    apply congr_arg2,
    { rw ← asso_dirichlet_character_eq_char,
      -- rw ← dirichlet_character.asso_dirichlet_character_mul,
      --simp_rw ← units.coe_hom_apply,
      rw ← monoid_hom.map_mul (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) _ _,
      --rw ← monoid_hom.map_mul (units.coe_hom R), rw ← monoid_hom.map_mul,
      congr,
      --rw units.ext_iff,
      simp only [units.coe_hom_apply, zmod.nat_cast_val, zmod.cast_id', id.def,
        ring_hom.to_monoid_hom_eq_coe, units.coe_map,
        ring_hom.coe_monoid_hom, zmod.cast_hom_apply, units.coe_mul, zmod.coe_unit_of_coprime],
      rw is_unit.unit_spec, rw zmod.cast_mul h2, rw zmod.cast_inv _ _ _ _ h',
      rw zmod.cast_nat_cast h' _, rw zmod.cast_inv _ _ _ _ h2, rw zmod.cast_nat_cast h2 _,
      rw ← mul_assoc, rw zmod.mul_inv_of_unit _, rw one_mul,
      sorry,
      any_goals { refine zmod.char_p _, },
      -- { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), },
      any_goals { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c _ hc), }, },
    { --rw ring_hom.map_mul,
      rw nat.cast_mul d _, rw nat.cast_pow p _,
      rw helper_4 p d R c k a, rw fract_eq_self _, rw mul_div_cancel' _,
      simp_rw [mul_assoc], apply congr_arg2 _ rfl _, rw ← nat.cast_pow c, rw map_nat_cast,
      rw map_nat_cast, apply congr_arg2 _ rfl _, rw is_unit.unit_spec,
      simp_rw [← map_nat_cast (algebra_map ℚ R), ← ring_hom.map_pow, ← ring_hom.map_mul, mul_one_div],
      apply congr_arg, rw h5,
      simp_rw is_unit.unit_spec, rw ← nat.cast_pow p _, rw ← nat.cast_mul d _, rw fract_eq_val,
      rw mul_div, rw ← pow_succ',
      rw nat.sub_one, rw nat.add_one, rw nat.succ_pred_eq_of_pos _,
      { apply lt_trans _ hn, apply nat.zero_lt_one, },
      { apply h1, },
--      rw helper_5 R _ _ (c : R), rw mul_assoc, apply congr_arg2,
      -- { rw nat.cast_mul, rw nat.cast_pow, apply h1, }, --might need change
      -- { apply h1, },
        -- { simp_rw [helper_6],
        --   rw fract_eq_self, rw ← nat.cast_pow, rw map_nat_cast, congr,
        --   { rw nat.cast_pow, congr, },
        --   { apply (zero_le_and_lt_one p d _ _).1, },
        --   { apply (zero_le_and_lt_one p d _ _).2, }, },
        -- { apply h1, },
      { apply (zero_le_and_lt_one p d _ _).2, },
      { apply (zero_le_and_lt_one p d _ _).1, }, }, },
  { intros a₁ a₂ ha₁ ha₂ h,
    simp only at h, rw units.ext_iff at h,
    rw is_unit.unit_spec at h, rw is_unit.unit_spec at h,
    simp_rw [zmod.nat_cast_val, zmod.cast_id] at h,
    apply helper_7 p d c _ _ h, },
  { intros b hb, simp_rw [units.ext_iff, is_unit.unit_spec],
    refine ⟨is_unit.unit _, _, _⟩,
    { exact c * (b : zmod (d * p^k)), },
    { apply is_unit.mul _ (units.is_unit _), sorry, },
    { apply finset.mem_univ _, },
    { rw is_unit.unit_spec, simp_rw zmod.nat_cast_val, rw zmod.cast_id, rw ← mul_assoc,
      rw zmod.cast_inv _ _ _ _ h', rw zmod.cast_nat_cast h' _, rw zmod.inv_mul_of_unit _, rw one_mul,
      { sorry, },
      { refine zmod.char_p _, },
      { apply nat.coprime.mul_right hc' (nat.coprime_pow_spl p c (2 * k) hc), }, }, },
end

lemma V_h2 (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d)
  (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) : ∃ z : ℕ, ∀ k ≥ z,
  ∥(V_h_def p d R m χ c n k) - (algebra_map ℚ R) (1 / (n : ℚ)) * ((algebra_map ℚ R) (n - 1 : ℕ) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε :=
begin
  refine ⟨max m (M5 p d R m χ n (ε / 2 / 6) (helper_11 ε hε) / 2), λ k hk, _⟩,
  have h : (algebra_map ℚ R) (1 / (n : ℚ)) * (algebra_map ℚ R) (n : ℚ) = 1, sorry,
  rw ← one_mul (V_h_def p d R m χ c n k),
  conv { congr, congr, congr, rw ← h, rw mul_assoc, },
  rw ← mul_sub,
  rw ← sub_add_sub_cancel _ ((algebra_map ℚ R) ((n - 1 : ℕ) : ℚ) * (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  (algebra_map ℚ R) (c ^ n : ℚ)) * (U_def p d R m hd χ n k)) _,
  -- rw ← sub_add_sub_cancel (V_h_def p d R m χ c n _) _ _,
  rw mul_add,
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  rw ← add_halves ε, apply add_lt_add,
  { apply lt_of_le_of_lt (norm_mul_le _ _) _,
    rw ← lt_div_iff' _,
    { convert V_h2_4 p d R m hd χ c hc' hc n hn na (ε / 2 / ∥(algebra_map ℚ R) (1 / ↑n)∥) _ k _,
      rw map_nat_cast, rw map_nat_cast,
      sorry,
      sorry, },
    { rw norm_pos_iff, sorry, }, },
  --apply classical.some_spec (helper_12 p d R m hd χ c n (ε/2) (half_pos hε)) k _,

  { simp_rw [← nat.cast_pow c _, map_nat_cast],
    conv { congr, congr, congr, skip, -- rw mul_assoc, rw mul_assoc ↑(n - 1) _ _,
      rw ← mul_sub (((n - 1 : ℕ) : R) * _), },
    sorry, },
end

noncomputable def N3' [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(V_h_def p d R m χ c n k) + ((algebra_map ℚ R) (1 / ↑n) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε }

lemma N3'_spec (hd : d.gcd p = 1) [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d)
  (hc : c.coprime p) (n : ℕ) (hn : 1 < n)
  (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥)
  (ε : ℝ) (hε : 0 < ε) (k : ℕ)
  (hk : N3' p d R m χ c n ε hε ≤ k) :
  ∥(V_h_def p d R m χ c n k) + ((algebra_map ℚ R) (1 / ↑n) *
  (1 - (asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n))∥ < ε :=
begin
  delta N3' at hk,
  apply nat_spec' _ _ k hk,
  refine ⟨_, _⟩,
  { refine classical.some (V_h2 p d R m χ c hd hc' hc n hn na ε hε), },
  { rw set.mem_set_of_eq,
    --simp only [ge_iff_le, map_nat_cast, monoid_hom.coe_mk, set.mem_set_of_eq],
    refine classical.some_spec (V_h2 p d R m χ c hd hc' hc n hn na ε hε), },
  refine ⟨classical.some (V_h2 p d R m χ c hd hc' hc n hn na ε hε),
    classical.some_spec (V_h2 p d R m χ c hd hc' hc n hn na ε hε)⟩,
end

lemma V [normed_algebra ℚ R] [norm_one_class R] (hc' : c.coprime d) (hc : c.coprime p) (n : ℕ)
  (hn : 1 < n) (na : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ i : (zmod n)ˣ, f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) :
  filter.tendsto (λ j : ℕ, V_def p d R m hd χ c n j)
  /-∑ (x : (zmod (d * p ^ j))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) (int.fract (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d j hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) x).fst),
  ↑(((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) x).snd))).val) / (↑d * ↑p ^ j))))-/
  -- ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  -- (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R) (↑c * int.fract
  -- (↑((((c : zmod (d * p^(2 * n))) : zmod (d * p^n)))⁻¹ * (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  -- (↑(x.fst), ↑(x.snd))) / (↑d * ↑p ^ j))))
  filter.at_top (nhds (( algebra_map ℚ R ((n + 1) / n) - (algebra_map ℚ R (1 / n)) *
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (c) * c^n ) * ((1 -
  asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n))) ) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  have four_pos : 0 < ε/4, linarith,
  simp_rw dist_eq_norm,
  set s : set ℕ := {m, (M1 p d R m hd χ c hc hc' n (ε/2) (half_pos hε)),
    (M2 p d R m hd χ n (ε/4) four_pos), (N3' p d R m χ c n (ε/4) four_pos)} with hs,
  refine ⟨Sup s, λ x hx, _⟩,
--  conv { congr, congr, conv { congr, apply_congr, skip, rw int.fract_eq_self.2 _,
--  rw [used_map_ext p d R m hd χ _ _ _ _], skip, apply_congr (le_of_max_le_left hx),
--  apply_congr zero_le_and_lt_one, }, },
  --delta used_map, delta neg_pow', delta neg_pow'_to_hom,
  conv { congr, congr, rw ← sub_add_sub_cancel _ (((((χ * ((teichmuller_character_mod_p_change_level p d R m)^n)) (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (c : R)^n)) * U_def p d R m hd χ n x : R) + (V_h_def p d R m χ c n x)), },
  -- conv { congr, congr, rw ← sub_add_sub_cancel _ ((U_def p d R m hd χ n x) -
  --   (V_h_def p d R m χ c n x)) _, },
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  rw ← sub_sub,
  rw ← half_add_self ε, rw add_div, rw add_div,
  have hx' : ∀ y ∈ s, y ≤ x,
  { intros y hy, apply le_trans _ hx,
    apply le_cSup _ hy,
    { apply set.finite.bdd_above,
      simp only [set.finite_singleton, set.finite.insert], }, },
  apply add_lt_add (M1_spec p d R m hd χ c hc hc' n hn na (ε/2) (half_pos hε) x _) _,
  { apply hx', rw hs,
    simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true], },
  rw div_self _,
  { rw ring_hom.map_add, rw ring_hom.map_one, rw ← add_sub (1 : R) _ _,
    rw add_mul, rw one_mul,
    rw [-- ← sub_sub,
    add_sub_right_comm _ (V_h_def p d R m χ c n x) _],-- sub_sub],
    apply lt_of_le_of_lt (norm_sub_le _ _) _,
    rw ← half_add_self (ε/2), rw add_div,
    have : ε/2/2 = ε/4, linarith,
    rw this,
    apply add_lt_add (M2_spec p d R m hd χ n (ε/4) four_pos x _) _,
    { apply hx', rw hs, simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true], },
    conv { congr, congr, congr, skip, congr,
    conv { congr, rw ← mul_one ((algebra_map ℚ R) (1 / ↑n)), }, rw mul_assoc, rw ← mul_sub, },
    apply N3'_spec p d R m hd χ c n (ε/4) four_pos x _,
    { apply hx', rw hs,
      simp only [set.mem_insert_iff, eq_self_iff_true, true_or, or_true],
      simp only [set.mem_singleton, or_true], }, },
  { rw nat.cast_ne_zero, apply hn, },
end

lemma W [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, ∑ (x : (zmod (d * p ^ j))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
-- rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^j) d) (zmod (p ^ j))).to_monoid_hom) x)) •
  (algebra_map ℚ R) ((↑c - 1) / 2))
  -- ∑ (x : (zmod d)ˣ × (zmod (p ^ j))ˣ),
  -- (used_map p d R m hd χ n) (x.fst, rev_coe p x.snd) • (algebra_map ℚ R) ((↑c - 1) / 2))
  filter.at_top (nhds 0) :=
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

theorem p_adic_L_function_eval_neg_int [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
   (n : R) * (p_adic_L_function' p d R m hd χ hc hc' na (neg_pow' p d R (n - 1))) =
   -(1 - (χ (zmod.unit_of_coprime c (nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c m hc⟩))
   * (neg_pow' p d R n (zmod.unit_of_coprime c hc', is_unit.unit ((is_unit_iff_not_dvd p c)
   ((nat.prime.coprime_iff_not_dvd (fact.out _)).1 (nat.coprime.symm hc))
     )) ))) * (1 - ((asso_dirichlet_character (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n))) p * p^(n - 1)) ) *
   (general_bernoulli_number (dirichlet_character.mul χ
     ((teichmuller_character_mod_p_change_level p d R m)^n)) n) :=
begin
  --symmetry,
--  rw ← eq_div_iff_mul_eq',
  delta p_adic_L_function',
  --change (n : R) * (measure.integral (bernoulli_measure' p d R hc hc' hd na))
   --(used_map p d R m hd χ n) = _, --simp,
  delta measure.integral,
  simp only [monoid_hom.coe_comp, ring_hom.to_monoid_hom_eq_coe, mul_equiv.coe_to_monoid_hom,
    monoid_hom.coe_prod_map, continuous_linear_map.coe_mk', linear_map.coe_mk, neg_sub,
    monoid_hom.coe_mk],
  --delta dense_inducing.extend,
  --change (n : R) * lim (filter.comap (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R)
  --  (nhds (used_map p d R m hd χ n))) ((bernoulli_measure' p d R hc hc' hd na).val).to_fun = _,
  have := (trying p d R hd hc hc' na (used_map p d R m hd χ n) _ _),
  -- add filter.tendsto.lim_eq later
  swap 2, { refine λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ),
     (used_map p d R m hd χ n) (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
-- rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
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



  sorry,
end

example (f1 f2 : ℕ → R) (a1 a2 : R)
  (h1 : filter.tendsto f1 filter.at_top (nhds a1)) (h2 : filter.tendsto f2 filter.at_top (nhds a2)) :
  filter.tendsto (f1 + f2) filter.at_top (nhds (a1 + a2)) :=
begin
  apply filter.tendsto.add,
  apply h1,
  apply h2,
end

lemma simplifying [normed_algebra ℚ R] [norm_one_class R] (n x : ℕ) :
  (λ (x_1 : (zmod (d * p ^ x))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^x)) (zmod d)).to_monoid_hom) x_1,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^x) d) (zmod (p ^ x))).to_monoid_hom) x_1)) •
  (algebra_map ℚ R) (int.fract (↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d x hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime_pow_spl p d x hd)) x_1).fst),
  ↑(((units.chinese_remainder (nat.coprime_pow_spl p d x hd)) x_1).snd))).val) / (↑d * ↑p ^ x)))) =
  λ (x_1 : (zmod (d * p ^ x))ˣ), (used_map p d R m hd χ n)
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^x)) (zmod d)).to_monoid_hom) x_1,
  rev_coe p ((units.map (zmod.cast_hom (dvd_mul_left (p^x) d) (zmod (p ^ x))).to_monoid_hom) x_1)) •
  (algebra_map ℚ R) (int.fract (↑x_1 / (↑d * ↑p ^ x))) :=
begin
  ext, congr, apply congr_arg,
  delta units.chinese_remainder, delta mul_equiv.prod_units, delta units.map_equiv,
  simp,
end
.

example {Y A : Type*} [mul_one_class Y] [topological_space Y] [topological_space A]
  [mul_one_class A] (w : weight_space Y A) (x : Y) : w x = w.to_fun x := rfl

lemma helper_254 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  (algebra_map ℚ R) (1 / ↑n) * -(1 - ↑(χ (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.2 ⟨hc', p.coprime_pow_spl c m hc⟩))) * (neg_pow' p d R n)
  (zmod.unit_of_coprime c hc', (is_unit.unit (is_unit_iff_not_dvd _ _
  ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)))))) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n =
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n -
  ((algebra_map ℚ R) ((↑n + 1) / ↑n) - (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c * ↑c ^ n) *
  ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n) :=
begin
  rw ← mul_assoc,
  rw ← sub_mul _ _ _,
  apply congr_arg2 _ _ rfl,
  conv_rhs { congr, rw ← one_mul (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
    ↑p ^ (n - 1)), },
  rw ← sub_mul,
  apply congr_arg2 _ _ rfl, rw add_div, rw div_self _, rw ring_hom.map_add, rw ring_hom.map_one,
  rw add_sub_assoc, rw sub_add_cancel', rw mul_neg, rw ← neg_mul,
  conv_rhs { congr, congr, rw ← mul_one ((algebra_map ℚ R) (1 / ↑n)), },
  rw mul_assoc,
  rw ← mul_sub, rw ← neg_mul,
  apply congr_arg2 _ rfl (congr_arg2 _ rfl _),
  rw dirichlet_character.mul_eval_coprime,
  rw asso_dirichlet_character_eq_char',
  rw mul_assoc,
  apply congr_arg2 _ _ _,
  sorry,
  { change (neg_pow' p d R n).to_fun _ = _,
    delta neg_pow', simp only, delta neg_pow'_to_hom,
    rw asso_dirichlet_character_eq_char',
    simp,
    sorry, sorry, },
  admit,
  sorry,
  sorry,
end

theorem p_adic_L_function_eval_neg_int_new [normed_algebra ℚ R] [norm_one_class R] (n : ℕ)
  (na' : ∀ (n : ℕ) (f : (zmod n)ˣ → R), ∥∑ (i : (zmod n)ˣ), f i∥ ≤ ⨆ (i : (zmod n)ˣ), ∥f i∥) :
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
  --change (measure.integral (bernoulli_measure' p d R hc hc' hd na))
  -- (used_map p d R m hd χ n) = _, --simp,
  have := (trying p d R hd hc hc' na (used_map p d R m hd χ n) _ _),
  -- add filter.tendsto.lim_eq later
  swap 2, { refine λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ),
     (used_map p d R m hd χ n) (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
-- rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
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

  rw metric.tendsto_at_top,
  rintros ε hε,
  refine ⟨1, λ m hm, _⟩,
  apply lt_of_le_of_lt (dist_add_add_le _ _ _ _) _,


  delta measure.integral,
  simp only [monoid_hom.coe_comp, ring_hom.to_monoid_hom_eq_coe, mul_equiv.coe_to_monoid_hom,
    monoid_hom.coe_prod_map, continuous_linear_map.coe_mk', linear_map.coe_mk, neg_sub,
    monoid_hom.coe_mk],
--  delta dense_inducing.extend,
  delta dense_inducing.extend,
  -- haveI : (filter.comap (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R)
  -- (nhds
  --    {to_fun := (units.coe_hom R) ∘
  --                   (χ * teichmuller_character_mod_p_change_level p d R m) ∘
  --                     ((units.map (zmod.chinese_remainder _).symm.to_monoid_hom) ∘
  --                          (mul_equiv.prod_units.symm)) ∘
  --                       prod.map ⇑(monoid_hom.id (zmod d)ˣ) ⇑(units.map ↑(padic_int.to_zmod_pow m)) *
  --                 ((neg_pow' p d R (n - 1)).to_monoid_hom),
  --     continuous_to_fun := _})).ne_bot, sorry,
  convert @filter.tendsto.lim_eq _ _ _ _ _ _ _ _ _,
  delta lim, delta Lim,
  apply dense_inducing.extend_eq_of_tendsto,


/-  --delta dense_inducing.extend,
  --change (n : R) * lim (filter.comap (inclusion ((zmod d)ˣ × ℤ_[p]ˣ) R)
  --  (nhds (used_map p d R m hd χ n))) ((bernoulli_measure' p d R hc hc' hd na).val).to_fun = _,
  have := (trying p d R hd hc hc' na (used_map p d R m hd χ n) _ _),
  -- add filter.tendsto.lim_eq later
  swap 2, { refine λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ),
     (used_map p d R m hd χ n) (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_right _ _)
     (zmod d) _ (zmod.char_p d)).to_monoid_hom a,
     rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
-- rev_coe p (units.map (@zmod.cast_hom (d * p^j) _ (dvd_mul_left _ _) (zmod (p^j)) _ _).to_monoid_hom a)) •
     (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
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
  sorry -/
end
