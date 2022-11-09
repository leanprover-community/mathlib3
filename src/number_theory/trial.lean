import number_theory.UVW

open_locale big_operators
local attribute [instance] zmod.topological_space

variables (p : ℕ) [fact (nat.prime p)] (d : ℕ) (R : Type*) [normed_comm_ring R] (m : ℕ)
(hd : d.gcd p = 1) (χ : dirichlet_character R (d*(p^m))) {c : ℕ} (hc : c.gcd p = 1)
(hc' : c.gcd d = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
(w : weight_space (units (zmod d) × units ℤ_[p]) R)

variable [fact (0 < d)]
variables [complete_space R] [char_zero R]

open continuous_map

variables [normed_algebra ℚ_[p] R] [fact (0 < m)]

variable [fact (0 < d)]

variable (c)

variables (hc) (hc')

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

lemma weight_space.to_monoid_hom_apply {X A : Type*} [mul_one_class X] [topological_space X]
  [topological_space A] [mul_one_class A] (w : weight_space X A) :
  (w.to_monoid_hom : X → A) = w.to_fun := rfl

lemma ring_hom.comp_to_monoid_hom {α β γ : Type*} [non_assoc_semiring α] [non_assoc_semiring β] [non_assoc_semiring γ]
  (f : α →+* β) (g : β →+* γ) : (g.comp f).to_monoid_hom = g.to_monoid_hom.comp f.to_monoid_hom :=
by { ext, simp, }

lemma helper_254 [normed_algebra ℚ R] [norm_one_class R] (n : ℕ) (hn : n ≠ 0) :
  (algebra_map ℚ R) (1 / ↑n) * -(1 - ↑(χ (zmod.unit_of_coprime c
  (nat.coprime_mul_iff_right.2 ⟨hc', p.coprime_pow_spl c m hc⟩))) * (neg_pow' p d R n)
  (zmod.unit_of_coprime c hc', (is_unit.unit (is_unit_iff_not_dvd _ _
  ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)))))) *
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)))
  ↑p * ↑p ^ (n - 1)) * general_bernoulli_number
  (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n =
  (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n -
  ((algebra_map ℚ R) ((↑n + 1) / ↑n) - (algebra_map ℚ R) (1 / ↑n) * (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑c *
  ↑c ^ n) * ((1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
  ↑p ^ (n - 1)) * general_bernoulli_number (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n)) n) + 0 :=
begin
  have h2 : nat.coprime c (d * p^m) := nat.coprime_mul_iff_right.2 ⟨hc', nat.coprime_pow_spl p c _ hc⟩,
  have h1 : is_unit (c : zmod (d * p^m)) :=
    is_unit_of_is_coprime dvd_rfl (nat.is_coprime_iff_coprime.2 h2),
--((fact.out (nat.prime p)).coprime_iff_not_dvd.mp (nat.coprime.symm hc)),
  rw add_zero, rw ← mul_assoc, rw ← sub_mul, apply congr_arg2 _ _ rfl, rw add_div, rw div_self _,
  rw ring_hom.map_add, conv_rhs { congr, rw ← one_mul (1 - (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p_change_level p d R m ^ n))) ↑p *
        ↑p ^ (n - 1)), },
  rw ← sub_mul,
  apply congr_arg2 _ _ rfl,
  conv_rhs { congr, skip, rw add_sub_assoc, congr, skip, congr,
    rw ← mul_one ((algebra_map ℚ R) (1 / ↑n)), },
  rw mul_assoc,
  rw ← mul_sub ((algebra_map ℚ R) (1 / ↑n)) _ _, rw ring_hom.map_one, rw sub_add_cancel',
  rw ← mul_neg, rw teichmuller_character_mod_p_change_level_def,
  rw dirichlet_character.mul_eval_coprime, rw mul_assoc, congr,
  { rw asso_dirichlet_character_eq_char' _ h1, congr,
    rw units.ext_iff, rw is_unit.unit_spec, rw zmod.coe_unit_of_coprime, },
  { delta neg_pow',
    change (neg_pow'_to_hom p d R n).to_fun _ = _, delta neg_pow'_to_hom,
    simp only,
    rw asso_dirichlet_character_eq_char' _ h1, rw mul_pow, rw monoid_hom.comp_mul,
    rw monoid_hom.comp_mul, rw monoid_hom.comp_mul, rw monoid_hom.to_fun_eq_coe, rw mul_comm,
    rw monoid_hom.mul_apply,
    congr,
    { simp_rw monoid_hom.comp_apply,
      change _ = ↑((((units.map ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom).to_monoid_hom)
        (((teichmuller_character_mod_p p))⁻¹.change_level _ h1.unit)^n)) ),
      rw units.coe_pow, rw units.coe_map, rw ← monoid_hom.map_pow,
      rw ring_hom.comp_to_monoid_hom,
      rw ← monoid_hom.comp_apply, rw units.coe_hom_apply, rw ← units.coe_pow, congr,
      change ((teichmuller_character_mod_p p)⁻¹ ((units.map (@padic_int.to_zmod p _).to_monoid_hom)
       ((is_unit.unit (is_unit_iff_not_dvd _ _ ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp
        (nat.coprime.symm hc)))) )))^n = _,
      congr, rw units.ext_iff, rw units.coe_map, rw is_unit.unit_spec, rw units.coe_map,
      rw is_unit.unit_spec, rw ring_hom.coe_monoid_hom, rw ring_hom.to_monoid_hom_eq_coe,
      rw ring_hom.coe_monoid_hom, rw map_nat_cast, rw map_nat_cast, },
    { simp_rw monoid_hom.comp_apply,
      change ((algebra_map ℚ_[p] R)) ((padic_int.coe.ring_hom) ((units.coe_hom ℤ_[p])
        ((is_unit.unit (is_unit_iff_not_dvd _ _ ((fact.out (nat.prime p)).coprime_iff_not_dvd.mp
        (nat.coprime.symm hc))))^n))) = _,
      rw units.coe_hom_apply, rw units.coe_pow,
      rw is_unit.unit_spec, rw ring_hom.map_pow, rw ring_hom.map_pow,
      rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp padic_int.coe.ring_hom),
      rw ring_hom.comp_apply, }, },
  { rw nat.is_coprime_iff_coprime, apply nat.coprime.mul_right h2 h2, },
  { norm_cast, apply hn, },
end

noncomputable abbreviation pls_help (y : ℕ) : (zmod d)ˣ × ℤ_[p]ˣ →* (zmod (d * p^y))ˣ :=
monoid_hom.comp (units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d y hd)).symm.to_monoid_hom)
(monoid_hom.comp (mul_equiv.to_monoid_hom mul_equiv.prod_units.symm) ((monoid_hom.prod_map (monoid_hom.id (zmod d)ˣ)
(units.map (@padic_int.to_zmod_pow p _ y).to_monoid_hom))))
-- dot notation does not work for mul_equiv.to_monoid_hom?

lemma is_loc_const_pls_help (y : ℕ) : is_locally_constant (pls_help p d hd y) :=
begin
  delta pls_help,
  apply is_locally_constant.comp_continuous,
  { convert is_locally_constant.of_discrete _, exact units_prod_disc, },
  { simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom,
      monoid_hom.coe_prod_map, function.comp_app, _root_.prod_map, monoid_hom.id_apply],
    refine continuous.comp continuous_of_discrete_topology
      (continuous_fst.prod_mk (continuous.comp (continuous_units p _) continuous_snd)), },
end

lemma helper_265 (n y : ℕ) : continuous
  (λ x, (((χ * teichmuller_character_mod_p_change_level p d R m ^ n) (pls_help p d hd m x) : R) *
  ↑((pls_help p d hd y x : zmod (d * p^y))) ^ (n - 1))) :=
continuous.mul (continuous.comp units.continuous_coe (continuous.comp
(@continuous_of_discrete_topology _ _ _ (disc_top_units' _) _ _)
(is_locally_constant.continuous (is_loc_const_pls_help p d hd _)))) (continuous.pow
(continuous_bot.comp (continuous.comp (units.continuous_coe)
(is_locally_constant.continuous (is_loc_const_pls_help p d hd _)))) _)

open filter
open_locale topological_space

open_locale big_operators
@[simp, to_additive] lemma locally_constant.coe_prod {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → locally_constant α β) :
  ⇑(∏ i in s, f i) = (∏ i in s, (f i : α → β)) :=
map_prod (locally_constant.coe_fn_monoid_hom : locally_constant α β →* _) f s

-- remove prod_apply
@[to_additive]
lemma locally_constant.prod_apply' {α : Type*} {β : Type*} [comm_monoid β]
  [topological_space α] [topological_space β] [has_continuous_mul β]
  {ι : Type*} (s : finset ι) (f : ι → locally_constant α β) (a : α) :
  (∏ i in s, f i) a = (∏ i in s, f i a) :=
by simp

lemma helper_272 (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow m) ↑(a.snd))) = (@padic_int.to_zmod_pow p _ m) ↑(a.snd) :=
begin
  have := proj_snd' _ _ (nat.coprime_pow_spl p d _ hd) (a.fst : zmod d) ((padic_int.to_zmod_pow m) ↑(a.snd)),
  conv_rhs { rw ← this, },
  simp only [ring_equiv.inv_fun_eq_symm, zmod.cast_hom_apply],
  congr,
end

lemma zmod.cast_cast {n : ℕ} [fact (0 < n)] (l m : ℕ) (a : zmod n) (h1 : l ∣ m) :
  ((a : zmod m) : zmod l) = (a : zmod l) :=
begin
  rw ← zmod.nat_cast_val a, rw zmod.cast_nat_cast h1,
  { rw zmod.nat_cast_val, },
  { refine zmod.char_p _, },
end

--the underlying def for to_zmod and to_zmod_pow are different, this causes an issue, dont want to
--  use equi between p and p^1 ; maybe ring_hom.ext_zmod can be extended to ring_hom.padic_ext?
lemma padic_int.to_zmod_pow_cast_to_zmod (n : ℕ) (hn : n ≠ 0) (x : ℤ_[p]) :
  (padic_int.to_zmod_pow n x : zmod p) = padic_int.to_zmod x :=
begin
  apply padic_int.dense_range_int_cast.induction_on x,
  { refine is_closed_eq _ _,
    { continuity, apply padic_int.continuous_to_zmod_pow, },
    { apply continuous_to_zmod p, }, },
  { intro a,
    change (zmod.cast_hom (dvd_pow_self p hn) (zmod p)).comp (padic_int.to_zmod_pow n)
      (a : ℤ_[p]) = padic_int.to_zmod (a : ℤ_[p]),
    rw ring_hom.map_int_cast, rw ring_hom.map_int_cast, },
end

lemma ring_equiv.coe_to_monoid_hom {R S : Type*} [non_assoc_semiring R]
  [non_assoc_semiring S] (e : R ≃+* S) : ⇑e.to_monoid_hom = e :=
by { ext, change e.to_ring_hom.to_monoid_hom x  = _, rw ring_hom.to_monoid_hom_eq_coe,
  rw ring_hom.coe_monoid_hom, rw ring_equiv.to_ring_hom_eq_coe, rw ring_equiv.coe_to_ring_hom, }

lemma ring_equiv.eq_symm_apply {R S : Type*} [non_assoc_semiring R]
  [non_assoc_semiring S] (e : R ≃+* S) (x : S) (y : R) : y = e.symm x ↔ e y = x :=
by { refine ⟨λ h, _, λ h, _⟩, { rw h, simp, }, { rw ← h, simp, }, }

lemma zmod.coe_proj {x : ℕ} (hx : m < x) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d x hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) =
  ((zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm.to_monoid_hom)
  (↑(a.fst), (padic_int.to_zmod_pow m) ↑(a.snd)) :=
begin
  haveI : fact (0 < d * p ^ x), { apply imp p d x, },
  rw ring_equiv.coe_to_monoid_hom (zmod.chinese_remainder (nat.coprime_pow_spl p d x hd)).symm,
  rw ring_equiv.coe_to_monoid_hom (zmod.chinese_remainder (nat.coprime_pow_spl p d m hd)).symm,
  rw ring_equiv.eq_symm_apply, apply prod.ext,
  { rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.to_equiv_eq_coe,
    rw inv_fst' p d _ _ (nat.coprime_pow_spl p d _ hd),
    rw zmod.cast_cast _ _ _ (dvd_mul_right d _),
    rw ← ring_equiv.inv_fun_eq_symm,
    change (zmod.cast_hom (dvd_mul_right d (p^x)) (zmod d))
      ((zmod.chinese_remainder (nat.coprime_pow_spl p d _ hd)).inv_fun
      (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) = _,
    simp_rw proj_fst' _ _ (nat.coprime_pow_spl p d _ hd) _ _,
    apply_instance, },
  { rw ← ring_equiv.coe_to_equiv, rw ← ring_equiv.to_equiv_eq_coe,
    rw inv_snd' p d _ _ (nat.coprime_pow_spl p d _ hd),
    rw zmod.cast_cast _ _ _ (dvd_mul_left _ d),
    have h2 : p^m ∣ p^x, apply pow_dvd_pow p (le_of_lt hx),
    rw ← zmod.cast_cast _ _ _ h2,
    rw ← ring_equiv.inv_fun_eq_symm,
    change _ = (padic_int.to_zmod_pow m) ↑(a.snd),
    rw ← padic_int.cast_to_zmod_pow m x (le_of_lt hx) _,
    apply congr_arg,
    change (zmod.cast_hom (dvd_mul_left (p^x) d) (zmod (p^x)))
      ((zmod.chinese_remainder (nat.coprime_pow_spl p d _ hd)).inv_fun
      (↑(a.fst), (padic_int.to_zmod_pow x) ↑(a.snd))) = _,
    rw proj_snd' _ _ (nat.coprime_pow_spl p d x hd) (↑(a.fst)) _,
    apply_instance,
    apply_instance, },
end

lemma helper_281 {x : ℕ} (hx : m < x) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  (((pls_help p d hd x) a) : zmod (d * p^m)) = ↑((pls_help p d hd m) a) :=
begin
  change ((units.map (zmod.cast_hom (mul_dvd_mul_left d (pow_dvd_pow p (le_of_lt hx)))
    (zmod (d * p^m))).to_monoid_hom) (pls_help p d hd x a) : zmod (d * p^m)) = _,
  rw units.coe_map,
  delta pls_help, simp_rw monoid_hom.comp_apply,
  rw units.coe_map, rw units.coe_map,
  simp only [ring_hom.to_monoid_hom_eq_coe, monoid_hom.coe_prod_map, _root_.prod_map, monoid_hom.id_apply,
    mul_equiv.coe_to_monoid_hom, ring_hom.coe_monoid_hom, zmod.cast_hom_apply],
  delta mul_equiv.prod_units, simp,
  rw zmod.coe_proj p d m hd hx a,
end

lemma units_chinese_remainder_comp_pls_help (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  (units.chinese_remainder (nat.coprime_pow_spl p d x hd)) ((pls_help p d hd x) a) =
  (a.fst, units.map (@padic_int.to_zmod_pow p _ x).to_monoid_hom a.snd) :=
begin
  delta pls_help, rw monoid_hom.comp_apply, convert mul_equiv.apply_symm_apply _ _,
end
.
lemma units_chinese_remainder_comp_pls_help_fst (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ((units.chinese_remainder (nat.coprime_pow_spl p d x hd)) ((pls_help p d hd x) a)).fst =
  a.fst := by { rw units_chinese_remainder_comp_pls_help p d hd x a, }

lemma units_chinese_remainder_comp_pls_help_snd (x : ℕ) (a : (zmod d)ˣ × ℤ_[p]ˣ) :
  ((units.chinese_remainder (nat.coprime_pow_spl p d x hd)) ((pls_help p d hd x) a)).snd =
  units.map (@padic_int.to_zmod_pow p _ x).to_monoid_hom a.snd :=
by { rw units_chinese_remainder_comp_pls_help p d hd x a, }

lemma helper_256 (n : ℕ) (hn : 1 < n) : (λ y : ℕ, ((∑ (a : (zmod (d * p ^ y))ˣ),
  ((asso_dirichlet_character (χ * teichmuller_character_mod_p_change_level p d R m ^ n)) ↑a *
  ↑((a : zmod (d * p^y)).val) ^ (n - 1)) • locally_constant.char_fn R (is_clopen_units_clopen_from p d y
  ((units.chinese_remainder (p.coprime_pow_spl d y hd)) a)) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R))) =ᶠ[at_top]
  (λ y : ℕ, (⟨λ x, ((χ * teichmuller_character_mod_p_change_level p d R m) ((pls_help p d hd m) x) : R),
  is_locally_constant.continuous begin apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, end⟩) *
  (((⟨λ x, ↑(pls_help p d hd y x : zmod (d * p^y)) ^ (n - 1), is_locally_constant.continuous begin apply is_locally_constant.comp₂,
      { apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, },
      { apply is_locally_constant.const, }, end⟩ ) *
  ⟨λ x, ((teichmuller_character_mod_p_change_level p d R m ^ (n - 1)) ((pls_help p d hd m) x) : R),
  is_locally_constant.continuous begin
    apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, end⟩ ))) :=
begin
  rw eventually_eq_iff_exists_mem,
  set s : set ℕ := {x : ℕ | m < x} with hs,
  refine ⟨s, _, _⟩,
  { rw mem_at_top_sets, refine ⟨m.succ, λ b hb, _⟩,
    change m < b, apply nat.succ_le_iff.1 hb, },
  { rw set.eq_on, rintros x hx, ext, simp only, rw coe_mul, rw coe_mul, rw pi.mul_apply,
    rw pi.mul_apply, rw locally_constant.coe_continuous_map, --rw locally_constant.coe_sum,
    rw locally_constant.sum_apply', simp_rw locally_constant.smul_apply,
    have h1 : is_unit ((pls_help p d hd x a) : zmod (d * p^m)),
    { apply units.coe_map_of_dvd, apply mul_dvd_mul_left d (pow_dvd_pow p (le_of_lt hx)), },
    rw finset.sum_eq_single_of_mem (pls_help p d hd x a),
    { rw (locally_constant.char_fn_one R _ _).1, rw smul_eq_mul, rw mul_one,
      conv_rhs { rw mul_comm, rw mul_assoc, rw mul_comm, },
      rw zmod.nat_cast_val, congr, rw ← to_fun_eq_coe, rw ← to_fun_eq_coe, simp only,
      rw ← units.coe_mul, rw asso_dirichlet_character_eq_char' _ h1,
      { apply congr_arg, rw ← monoid_hom.mul_apply,
        apply congr _ _,
        { conv_rhs { rw mul_comm _ (χ * teichmuller_character_mod_p_change_level p d R m), },
          rw mul_assoc, rw ← pow_succ, rw nat.sub_add_cancel (le_of_lt hn), },
        { rw units.ext_iff, rw is_unit.unit_spec h1, rw helper_281, apply hx, }, },
      { rw set.mem_prod,
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, set.mem_singleton_iff,
          ring_hom.to_monoid_hom_eq_coe, set.mem_preimage],
        rw units.ext_iff, rw units.ext_iff,
        rw units_chinese_remainder_comp_pls_help,
        simp only [eq_self_iff_true, ring_hom.to_monoid_hom_eq_coe, and_self], }, },
    { apply finset.mem_univ, },
    { intros b h' hb, clear h',
      rw (locally_constant.char_fn_zero R _ _).1 _,
      { rw smul_zero, },
      { intro h,
        rw set.mem_prod at h, rw set.mem_preimage at h, rw set.mem_singleton_iff at h,
        rw set.mem_singleton_iff at h, cases h with h2 h3,
        conv_lhs at h2 { rw ← units_chinese_remainder_comp_pls_help_fst p d hd x a, },
        conv_lhs at h3 { rw ← units_chinese_remainder_comp_pls_help_snd p d hd x a, },
        apply hb,
        apply mul_equiv.injective (units.chinese_remainder (nat.coprime_pow_spl p d x hd)),
        symmetry,
        apply prod.ext h2 h3, }, }, },
end

lemma helper_257 (f g : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  (((f * g) : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R)) = f * g :=
by { ext, simp }

lemma helper_271 (n : ℕ) : continuous
(λ x : (zmod d)ˣ × ℤ_[p]ˣ, ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (x.snd : ℤ_[p])))) :=
begin continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, end

lemma dirichlet_character.pow_apply (n m : ℕ) (χ : dirichlet_character R n) (a : (zmod n)ˣ) :
  (χ^m : dirichlet_character R n) a = (χ a)^m := by refl

lemma helper_258 (n : ℕ) :
  weight_space.to_continuous_map (neg_pow' p d R (n - 1)) =
  ((⟨λ x, ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom (x.snd : ℤ_[p]))), helper_271 p d R n⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^ (n - 1) *
  (⟨λ x, (((teichmuller_character_mod_p_change_level p d R m)^(n - 1)) ((pls_help p d hd m) x) : R),
  begin
    apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _,
    apply is_loc_const_pls_help, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)) :=
begin
  ext,
  change neg_pow'_to_hom p d R (n - 1) a = _,
  delta neg_pow'_to_hom, rw mul_pow, simp_rw monoid_hom.comp_mul,
  rw coe_mul, rw pi.mul_apply, rw monoid_hom.mul_apply,
  apply congr_arg2 _ _ _,
  { change _ = ((algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑(a.snd)))^(n - 1),
    rw ← ring_hom.map_pow, rw ← ring_hom.map_pow, rw ← units.coe_pow, refl, },
  { change _ = ↑((teichmuller_character_mod_p_change_level p d R m ^ (n - 1)) ((pls_help p d hd m) a)),
    rw dirichlet_character.pow_apply,
    simp_rw monoid_hom.comp_apply,
    change ((algebra_map ℚ_[p] R).to_monoid_hom) ((padic_int.coe.ring_hom.to_monoid_hom)
     ((units.coe_hom ℤ_[p]) (((monoid_hom.comp (teichmuller_character_mod_p p)⁻¹
     (units.map padic_int.to_zmod.to_monoid_hom)) (a.snd)^(n - 1))))) = _,
    rw monoid_hom.map_pow, rw monoid_hom.map_pow, rw monoid_hom.map_pow, rw units.coe_pow,
    apply congr_arg2 _ _ rfl, rw teichmuller_character_mod_p_change_level_def,
    rw units.coe_hom_apply, rw dirichlet_character.change_level,
    conv_rhs { rw monoid_hom.comp_apply, rw monoid_hom.inv_apply, rw monoid_hom.comp_apply, },
    rw ← monoid_hom.map_inv, rw units.coe_map, rw ← monoid_hom.comp_apply,
    rw ← ring_hom.comp_to_monoid_hom, apply congr_arg, rw ← units.ext_iff,
    rw monoid_hom.comp_apply, rw monoid_hom.inv_apply, apply congr_arg, apply congr_arg,
    rw units.ext_iff, rw units.coe_map, rw units.coe_map, rw units.coe_map,
    delta mul_equiv.prod_units, simp,
    have mnz : m ≠ 0, { apply ne_of_gt (fact.out _), apply_instance, apply_instance, },
    rw ← zmod.cast_cast _ _ _ (dvd_pow_self p mnz),
    rw helper_272 p d m hd a,
    rw padic_int.to_zmod_pow_cast_to_zmod p _ mnz _,
    { apply imp p d m, }, },
end

lemma helper_259 (n : ℕ) : filter.tendsto (λ (x : ℕ), ((⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑((χ * teichmuller_character_mod_p_change_level p d R m) ((pls_help p d hd m) x)),
  begin apply is_locally_constant.comp _ _, apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) : C((zmod d)ˣ × ℤ_[p]ˣ, R))) filter.at_top
  (nhds ⟨((units.coe_hom R).comp (pri_dir_char_extend' p d R m hd
  (χ * teichmuller_character_mod_p_change_level p d R m))), units.continuous_coe.comp (pri_dir_char_extend'_continuous p d R m hd _)⟩) :=
begin
-- for later : try to use this instead : convert tendsto_const_nhds,
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨1, λ y hy, _⟩, rw dist_eq_norm,
  rw norm_eq_supr_norm, rw coe_sub, simp_rw pi.sub_apply, simp_rw ← to_fun_eq_coe,
  simp_rw monoid_hom.comp_apply, simp_rw units.coe_hom_apply,
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  convert le_of_lt (half_pos hε), rw norm_eq_zero,
  rw ← locally_constant.to_continuous_map_eq_coe,
  delta locally_constant.to_continuous_map, simp_rw ← locally_constant.to_fun_eq_coe,
  rw sub_eq_zero,
end

lemma helper_263 : continuous (λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑(x.snd))) :=
by { continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, }

lemma helper_268 (x : ℤ_[p]) (n : ℕ) :
  (@padic_int.to_zmod_pow p _ n x : ℤ_[p]) = (padic_int.appr x n : ℤ_[p]) :=
begin
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  rw ← zmod.nat_cast_val, congr,
  change (x.appr n : zmod (p^n)).val = _,
  rw zmod.val_cast_of_lt, apply padic_int.appr_lt,
end

lemma helper_261 [norm_one_class R] : filter.tendsto (λ (x : ℕ),
  (⟨λ (z : (zmod d)ˣ × ℤ_[p]ˣ), ↑((@padic_int.to_zmod_pow p _ x) ↑(z.snd)),
  continuous.comp continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow p x)
  (continuous.comp units.continuous_coe continuous_snd))⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)))
  filter.at_top (nhds ⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R)
  (padic_int.coe.ring_hom ↑(x.snd)), helper_263 p d R⟩) :=
begin
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨classical.some (padic_int.exists_pow_neg_lt p (half_pos hε)), λ n hn, _⟩, rw dist_eq_norm,
  rw norm_eq_supr_norm,
  simp only [coe_sub, coe_mk, pi.sub_apply],
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  have : (algebra_map ℚ_[p] R) (padic_int.coe.ring_hom ↑((@padic_int.to_zmod_pow p _ n) ↑(y.snd))) =
    ((@padic_int.to_zmod_pow p _ n) (y.snd : ℤ_[p]) : R),
  { change ((algebra_map ℚ_[p] R).comp (@padic_int.coe.ring_hom p _))
      (↑((padic_int.to_zmod_pow n) ↑(y.snd))) = _,
    rw ← zmod.nat_cast_val,
    rw map_nat_cast,
    rw zmod.nat_cast_val, },
  rw ← this,
  simp_rw ← ring_hom.map_sub,
  rw norm_algebra_map',
  rw padic_int.coe.ring_hom, simp only [ring_hom.coe_mk],
  rw padic_int.padic_norm_e_of_padic_int,
  have finally := dist_appr_spec p y.snd n,
  rw dist_eq_norm at finally,
  rw norm_sub_rev,
  have final := classical.some_spec (padic_int.exists_pow_neg_lt p (half_pos hε)),
  apply le_of_lt, apply lt_of_le_of_lt _ final,
  rw helper_268 p _ n, apply le_trans finally _,
  apply zpow_le_of_le,
  { norm_cast, apply le_of_lt (nat.prime.one_lt (fact.out _)), apply_instance, },
  { apply neg_le_neg, norm_cast, apply hn, },
end

-- use norm_le everywhere

lemma helper_267 (n x : ℕ) : @padic_int.to_zmod_pow p _ n (x : ℤ_[p]) = (x : zmod (p^n)) := by { simp, }

lemma helper_262 [norm_one_class R] : filter.tendsto (λ (x : ℕ), dist (⟨λ (z : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑((@padic_int.to_zmod_pow p _ x) ↑(z.snd)), continuous.comp continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow p x)
  (continuous.comp units.continuous_coe continuous_snd))⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)) (⟨λ (y : (zmod d)ˣ × ℤ_[p]ˣ),
  ↑((pls_help p d hd x) y), continuous.comp continuous_of_discrete_topology
  (is_locally_constant.continuous (is_loc_const_pls_help p d hd _))⟩)) filter.at_top (nhds 0) :=
begin
-- use norm_le!
  rw metric.tendsto_at_top, intros ε hε,
  refine ⟨classical.some (padic_int.exists_pow_neg_lt p (half_pos hε)), λ n hn, _⟩,
  rw dist_zero_right, rw dist_eq_norm, rw norm_norm,
  rw norm_eq_supr_norm,
  simp only [coe_sub, coe_mk, pi.sub_apply],
  have calc1  :  ε/2 < ε, by linarith,
  apply lt_of_le_of_lt  _ calc1,
  apply cSup_le (set.range_nonempty _) (λ b hb, _),
  { apply_instance, },
  cases hb with y hy,
  rw ← hy,
  simp only, clear hy,
  rw norm_sub_rev,
  delta pls_help,
  change ∥(((units.map (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm.to_monoid_hom)
  ((mul_equiv.prod_units.symm)
     (((monoid_hom.id (zmod d)ˣ).prod_map (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom)) y)) : zmod (d * p^n)) : R) - _∥ ≤ ε/2,
  rw units.coe_map,
  change ∥(↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).symm)
    ↑((mul_equiv.prod_units.symm) (y.1, (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) y.2)))) - _∥ ≤ ε/2,
  simp_rw ← mul_equiv.inv_fun_eq_symm, delta mul_equiv.prod_units, simp only,
  simp_rw units.coe_mk, simp_rw units.coe_map,
  change ∥↑(((zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun)
    (↑(y.fst), ((padic_int.to_zmod_pow n)) ↑(y.snd))) - _∥ ≤ ε/2,
  have := proj_snd p d n ((y.fst : zmod d), (y.snd : ℤ_[p])) (nat.coprime_pow_spl p d n hd),
  change ↑((zmod.chinese_remainder _).inv_fun (↑(y.fst), (padic_int.to_zmod_pow n) (↑(y.snd)))) =
    (padic_int.to_zmod_pow n) (↑(y.snd)) at this,
  haveI : fact (0 < p^n) := fact_iff.2 (pow_pos (nat.prime.pos (fact.out _)) _),
  conv { congr, congr, congr, rw ← zmod.nat_cast_val,
    rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)), skip,
    rw ← this, rw ← zmod.nat_cast_val, rw ← zmod.nat_cast_val,
    rw ← map_nat_cast ((algebra_map ℚ_[p] R).comp (padic_int.coe.ring_hom)), rw zmod.nat_cast_val, },
-- this entire pricess should be a separate lemma
  rw ← ring_hom.map_sub, rw ring_hom.comp_apply,
  rw norm_algebra_map',
  rw padic_int.coe.ring_hom, simp only [ring_hom.coe_mk],
  rw padic_int.padic_norm_e_of_padic_int, rw ← helper_267, rw helper_268, rw ← dist_eq_norm,
  apply le_trans (dist_appr_spec p _ _) _,
  have final := classical.some_spec (padic_int.exists_pow_neg_lt p (half_pos hε)),
  apply le_of_lt, apply lt_of_le_of_lt _ final,
  apply zpow_le_of_le,
  { norm_cast, apply le_of_lt (nat.prime.one_lt (fact.out _)), apply_instance, },
  { apply neg_le_neg, norm_cast, apply hn, },
end

lemma helper_260 [norm_one_class R] (n : ℕ) : filter.tendsto (λ (x : ℕ), ↑(⟨λ (y : (zmod d)ˣ × ℤ_[p]ˣ),
  ((pls_help p d hd x) y : R) ^ (n - 1), begin apply is_locally_constant.comp₂,
      { apply is_locally_constant.comp _ _, apply is_loc_const_pls_help, },
      { apply is_locally_constant.const, }, end⟩ : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)) filter.at_top
  (nhds ((⟨λ (x : (zmod d)ˣ × ℤ_[p]ˣ), (algebra_map ℚ_[p] R)
  (padic_int.coe.ring_hom ↑(x.snd)), begin continuity, { rw algebra.algebra_map_eq_smul_one',
    exact continuous_id'.smul continuous_const, }, { exact units.continuous_coe, }, end⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^(n - 1))) :=
begin
  change filter.tendsto (λ x : ℕ, (⟨λ y, ((pls_help p d hd x) y : R), begin continuity,
  { simp only, apply continuous_of_discrete_topology, },
  { apply is_locally_constant.continuous (is_loc_const_pls_help p d hd x), }, end⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R))^(n - 1))
    filter.at_top _,
  apply filter.tendsto.pow _ (n - 1),
  { apply_instance, },
  { apply filter.tendsto.congr_dist,
    swap 3, { refine λ x, ⟨λ z, padic_int.to_zmod_pow x (z.snd : ℤ_[p]),
      continuous.comp continuous_bot (continuous.comp (padic_int.continuous_to_zmod_pow p x)
        (continuous.comp units.continuous_coe continuous_snd))⟩, },
    apply helper_261,
    apply helper_262, },
end

lemma helper_269 (n : ℕ) (y : (zmod (d * p^n))ˣ) :
  (zmod.chinese_remainder (nat.coprime_pow_spl p d n hd)).inv_fun
  (↑(((units.chinese_remainder (nat.coprime_pow_spl p d n hd)) y).fst),
  ↑(((units.chinese_remainder (nat.coprime_pow_spl p d n hd)) y).snd)) = (y : zmod (d * p^n)) :=
begin
  delta units.chinese_remainder, delta mul_equiv.prod_units, delta units.map_equiv,
  simp,
end

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
  have h1 := filter.tendsto.add (filter.tendsto.sub (U p d R m χ n) (V p d R m χ c hc' hc n hn))
    (W p d R m χ c n),
  conv at h1 { congr, skip, skip, rw ← helper_254 p d R m χ c hc hc' n (ne_zero_of_lt hn), },
  symmetry, apply helpful_much h1, clear h1,
  swap 3, { apply filter.at_top_ne_bot, },
  convert (tendsto_congr' _).2 (trying p d R hd hc hc' na _
    (λ j : ℕ, ∑ (a : (zmod (d * p^j))ˣ), (((asso_dirichlet_character (χ * (teichmuller_character_mod_p_change_level p d R m)^n) a : R) *
    ((((a : zmod (d * p^j))).val)^(n - 1) : R))) • (locally_constant.char_fn R (is_clopen_units_clopen_from p d j
     ((units.chinese_remainder (nat.coprime_pow_spl p d j hd)) a)))) _),
  { rw eventually_eq_iff_exists_mem,
    set s : set ℕ := {x : ℕ | 1 < x} with hs,
    refine ⟨s, _, _⟩,
    { rw mem_at_top_sets, refine ⟨nat.succ 1, λ b hb, _⟩,
      change 1 < b, apply nat.succ_le_iff.1 hb, },
    rw set.eq_on, rintros x hx, simp only,
    delta U_def, delta V_def, rw linear_map.map_sum, simp_rw linear_map.map_smul,
    rw ← finset.sum_sub_distrib, simp_rw ← smul_sub, rw ← finset.sum_add_distrib, simp_rw ← smul_add,
    apply finset.sum_congr rfl _, rintros y hy, apply congr_arg2 _ rfl _,
    rw bernoulli_measure'_eval_char_fn,
    rw E_c, rw helper_269, simp only, rw ring_hom.map_add, rw ring_hom.map_sub, rw zmod.nat_cast_val,
    rw zmod.nat_cast_val, refl, apply hx, },
  { rw filter.tendsto_congr' (helper_256 p d R m hd χ n hn),
    change filter.tendsto _ filter.at_top (nhds
    ((⟨((units.coe_hom R).comp (pri_dir_char_extend' p d R m hd (χ * teichmuller_character_mod_p_change_level p d R m))),
      units.continuous_coe.comp (pri_dir_char_extend'_continuous p d R m hd _)⟩ : C((zmod d)ˣ × ℤ_[p]ˣ, R)) *
      ⟨((neg_pow' p d R (n - 1)).to_monoid_hom), ((neg_pow' p d R (n - 1))).continuous_to_fun⟩)),
    apply filter.tendsto.mul _ _,
    { exact semi_normed_ring_top_monoid, },
    { apply helper_259 p d R m hd χ n, },
    { change filter.tendsto _ filter.at_top (nhds (neg_pow' p d R (n - 1)).to_continuous_map),
      rw helper_258 p d R m hd n,
      apply filter.tendsto.mul,
      { apply helper_260, },
      { apply tendsto_const_nhds, }, }, },
end
