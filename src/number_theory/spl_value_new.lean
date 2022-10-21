import number_theory.general_bernoullli_number_properties
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
noncomputable abbreviation rev_coe (n : ℕ) (a : (zmod (d * p^n))ˣ) : ℤ_[p]ˣ :=
begin
  by_cases hn : n ≠ 0,
  { apply is_unit.unit,
    swap, exact (a : ℤ_[p]),
    change is_unit ↑(a : zmod (d * p^n)),
    rw ← zmod.nat_cast_val _,
    apply is_unit_padic_of_is_unit_zmod,
    have c := units.map (zmod.cast_hom (dvd_pow (dvd_refl p) hn) (zmod p)).to_monoid_hom,
    { rw zmod.nat_cast_val _,
      rw ← zmod.cast_hom_apply _,
      swap 3, { refine zmod.char_p _, },
      swap, { apply dvd_mul_of_dvd_right (dvd_pow_self p hn) d, },
      rw ← ring_hom.coe_monoid_hom,
      rw ← ring_hom.to_monoid_hom_eq_coe,
      rw ← units.coe_map ((zmod.cast_hom (dvd_mul_of_dvd_right (dvd_pow_self p hn) d) (zmod p)).to_monoid_hom) _,
      apply units.is_unit,
      apply fact_iff.2,
      apply mul_prime_pow_pos p d n, },
      -- apply pow_pos (nat.prime.pos infer_instance), apply fact.out, },
    { apply (nat.coprime_pow_right_iff (nat.pos_of_ne_zero hn) _ _).1,
      apply nat.coprime.coprime_mul_left_right, swap, { exact d, },
      apply zmod.val_coe_unit_coprime, },
    { apply fact_iff.2 (mul_prime_pow_pos p d n), }, },
      -- apply fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _), assumption, }, },
    { exact 1, },
end

lemma lets_see : @padic_int.lift p _ ℤ_[p] _ (λ k, padic_int.to_zmod_pow k)
  (λ k₁ k₂ hk, by {simp only [padic_int.zmod_cast_comp_to_zmod_pow]}) = ring_hom.id ℤ_[p] :=
begin
  ext,
  simp only [padic_int.lift_self, ring_hom.id_apply],
end

lemma hmm (n : ℕ) : @continuous ((zmod d)ˣ × (zmod (d * p^n))ˣ) ((zmod d)ˣ × ℤ_[p]ˣ) _ _
  (prod.map (@id (zmod d)ˣ) ((rev_coe p d n) )) :=
begin
  apply continuous.prod_mk,
  { simp only [id.def], exact continuous_fst, },
  { apply continuous_of_discrete_topology, },
end

lemma tbu (f : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (n : ℕ) :
  is_locally_constant (f ∘ (prod.map id ((rev_coe p d n) ))) :=
begin
  apply is_locally_constant.comp, apply is_locally_constant.prod_mk,
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (d * p ^ n))ˣ), id x.fst),
  exact is_locally_constant.of_discrete (λ (x : (zmod d)ˣ × (zmod (d * p ^ n))ˣ), rev_coe p d n x.snd),
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
     rev_coe p d _ a) •
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
  ((a.1 : zmod d), (a.2 : zmod (p^n))))) ) := sorry

lemma nat_spec' (p : ℕ → Prop) (h : ({n : ℕ | ∀ (x : ℕ), x ≥ n → p x}).nonempty) (x : ℕ)
  (hx : x ≥ Inf {n : ℕ | ∀ (x : ℕ) (hx : x ≥ n), p x}) : p x := nat.Inf_mem h x hx

noncomputable def U_def [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (j : ℕ) :=
  ∑ (x : (zmod (d * p ^ j))ˣ),
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^j)) (zmod d)).to_monoid_hom) x,
  rev_coe p d _ x) •
  (algebra_map ℚ R) (int.fract (↑x / (↑d * ↑p ^ j)))

lemma U [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) :
  filter.tendsto (λ j : ℕ, U_def p d R m hd χ n j)
  filter.at_top (nhds ((1 - asso_dirichlet_character (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) (p) * p^(n - 1) ) *
  (general_bernoulli_number (dirichlet_character.mul χ
  ((teichmuller_character_mod_p_change_level p d R m)^n)) n)) ) := sorry

noncomputable def M2 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (ε : ℝ) (hε : 0 < ε) : ℕ :=
Inf {z : ℕ | ∀ k ≥ z, ∥(U_def p d R m hd χ n k) - ((1 - asso_dirichlet_character (dirichlet_character.mul χ
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

example (m n : ℕ) (h : p^n ∣ m) (x : zmod m) : (padic_int.to_zmod_pow n) (x : ℤ_[p]) = x := sorry

lemma used_map_ext_1 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hk : m ≤ k) (a : (zmod (d * p ^ k))ˣ) :
  (units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm)
  (prod.map (monoid_hom.id (zmod d)ˣ) (units.map ↑(@padic_int.to_zmod_pow p _ m))
  ((units.map ↑(zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d))) a,
  rev_coe p d _ a))) =
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
    simp only [zmod.ring_hom_map_cast], sorry },
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
  (rev_coe p d _ a)) =
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
  rev_coe p d _ a))))) *
  ((algebra_map ℚ_[p] R).to_monoid_hom).comp (padic_int.coe.ring_hom.to_monoid_hom.comp ((units.coe_hom ℤ_[p]).comp
  (monoid_hom.comp (monoid_hom.comp (teichmuller_character_mod_p p)⁻¹ (units.map (@padic_int.to_zmod p _).to_monoid_hom))
    (monoid_hom.snd (zmod d)ˣ ℤ_[p]ˣ)^(n - 1))))
  ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p d _ ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
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
  rev_coe p _ ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ↑((a : zmod (d * p^k)).val) ^ (n - 1) :=
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
    apply congr_arg, apply congr_arg, -- if `rev_coe` is defined on zmod (p^k), this breaks, because we get (a : zmod (p^k)).val = a.val, which is false
    rw ring_hom.eq_int_cast _ (((a : zmod (d * p^k)) : zmod (p^k)) : ℤ),
    rw zmod.int_cast_cast,
    sorry, },
  { intro h, rw h at hk, rw nat.le_zero_iff at hk, revert hk,
    apply ne_zero_of_lt (fact.out _), exact 0, apply_instance, apply_instance, },
end

lemma used_map_ext [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (k : ℕ) (hn : 1 ≤ n) (hk : m ≤ k)
  (a : (zmod (d * p^k))ˣ) :
  (used_map p d R m hd χ n) ((units.map (zmod.cast_hom (dvd_mul_right d (p^k)) (zmod d)).to_monoid_hom) a,
  rev_coe p _ ((units.map (zmod.cast_hom (dvd_mul_left (p^k) d) (zmod (p ^ k))).to_monoid_hom) a)) =
  ((χ * (teichmuller_character_mod_p_change_level p d R m)^n)
  (units.map (zmod.cast_hom (show d * p^m ∣ d * p^k, from mul_dvd_mul_left d (pow_dvd_pow p hk))
  (zmod (d * p^m))).to_monoid_hom a)) * (((a : zmod (d * p^k)).val)^(n - 1) : R) :=
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
  simp only [monoid_hom.mul, pi.mul_apply, function.comp_apply],
  rw [monoid_hom.map_mul, units.coe_hom_apply, units.coe_hom_apply],
  rw ← mul_assoc,
  rw mul_assoc _ (↑((teichmuller_character_mod_p_change_level p d R m) _)) _,
  congr,
  { apply used_map_ext_1 p d R m hd n k hk _, },
  { -- hn used here
    apply used_map_ext_2 p d R m hd n k hn hk _, },
  { apply used_map_ext_3 p d R m n k hn hk a, },
end
