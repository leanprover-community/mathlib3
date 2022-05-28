import number_theory.weight_space

variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
variables [fact (0 < d)] {c : ℕ}
variables [normed_algebra ℚ R] [norm_one_class R]

local attribute [instance] zmod.topological_space

open_locale big_operators

/-- An eventually constant sequence constructed from a locally constant function. -/
noncomputable def g' (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  {φ : linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R}
  (hφ : ∀ (l : ℕ) (x : zmod (d * p^l)), ∑ (y : zmod (d * p ^ l.succ)) in (λ a : zmod (d * p ^ l),
    set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a)) x, (φ y) = φ x)
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : d.gcd p = 1) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ),
    ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos p d n)), f(a) • (φ a),
  is_eventually_const := ⟨classical.some (factor_F p d R hd' f) + 1,
  begin
  simp, rintros l hl', -- why is the simp needed?
  have hl : classical.some (factor_F p d R hd' f) ≤ l,
  { apply le_trans (nat.le_succ _) hl', },
  set t := λ a : zmod (d * p ^ l), set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a) with ht,
  rw succ_eq_bUnion_equi_class,
  rw @finset.sum_bUnion _ _ _ _ _ _ (zmod' (d*p^l) (mul_prime_pow_pos p d l)) t _,
  { haveI : fact (0 < l),
    { apply fact_iff.2,
      apply lt_of_lt_of_le (nat.zero_lt_succ _) hl', },
    conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class_eq p d R l f x hd' hl x_1 H_1, },
    rw [←finset.mul_sum], rw hφ l x, }, },
  { rintros x hx y hy hxy, contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := inter_nonempty_of_not_disjoint' hxy,
    rw ht at hz, simp at hz, rw mem_equi_class p d l l.succ at hz,
    rw mem_equi_class p d l l.succ at hz, cases hz with h1 h2, rw h1 at h2,
    exact h2, }, end⟩, }

variables {φ : linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R}
  (hφ : ∀ (l : ℕ) (x : zmod (d * p^l)), ∑ (y : zmod (d * p ^ l.succ)) in (λ a : zmod (d * p ^ l),
    set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a)) x, (φ y) = φ x)

lemma g'_def (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : d.gcd p = 1) :
  (g' p d R hc hc' hd hφ f hd').to_seq n =
    ∑ a in (finset.range (d * p^n)),f(a) • (φ a) := sorry

noncomputable def distributions (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) :
  linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R :=
{ to_fun := λ f, sequence_limit (g' p d R hc hc' (by {apply fact_iff.1, convert hd 0,
    rw [pow_zero, mul_one], }) hφ f h'),
  map_add' := begin rintros,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
    set n := (sequence_limit_index' (g' p d R hc hc' hd' hφ (x + y) h')) ⊔ (sequence_limit_index' (g' p d R hc hc' hd' hφ x h'))
      ⊔ (sequence_limit_index' (g' p d R hc hc' hd' hφ y h')) with hn,
    --rw sequence_limit_eq (g p d R hc (x + y)) n _,
    repeat { rw sequence_limit_eq (g' p d R hc hc' hd' hφ _ h') n _, },
    { rw g'_def p d R hφ hc hc' hd' _ n h', rw g'_def p d R hφ hc hc' hd' _ n h', rw g'_def p d R hφ hc hc' hd' _ n h',
      simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add],
      rw ←finset.sum_add_distrib,
      apply finset.sum_congr, refl,
      rintros, rw add_mul, },
    { rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, left, apply le_refl, }, end,
  map_smul' := begin
    rintros m x,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
    set n := (sequence_limit_index' (g' p d R hc hc' hd' hφ x h')) ⊔ (sequence_limit_index' (g' p d R hc hc' hd' hφ (m • x) h'))
      with hn,
    repeat { rw sequence_limit_eq (g' p d R hc hc' hd' hφ _ h') n _, },
    { repeat { rw g'_def p d R hφ hc hc' hd' _ n h', }, simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply], rw finset.mul_sum,
      apply finset.sum_congr, refl,
      rintros, rw mul_assoc, rw ring_hom.id_apply, },
    { rw le_sup_iff, left, apply le_refl, },
    { rw le_sup_iff, right, apply le_refl, },
   end, }


noncomputable def measures_general (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) : measures (units (zmod d) × units ℤ_[p]) R :=
⟨ {
    to_fun := λ f, distributions p d R hφ hc hc' h' (loc_const_ind_fn _ p d f),
    map_add' := begin
      rintros f1 f2,
      convert linear_map.map_add _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add, locally_constant.coe_mk],
      repeat {rw ind_fn, },
      simp only [pi.add_apply, locally_constant.coe_add],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos,
        any_goals { convert dif_pos pos, }, },
      { have : (0 : R) = 0 + 0, rw add_zero,
        convert this,
        any_goals { convert dif_neg pos, }, },
    end,
    map_smul' := begin
      rintros m f,
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, locally_constant.to_fun_eq_coe],
      convert linear_map.map_smul _ _ _,
      ext y,
      repeat { rw loc_const_ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply,
        locally_constant.coe_mk],
      repeat { rw ind_fn, },
      simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply],
      by_cases pos : is_unit y.fst ∧ is_unit y.snd,
      { convert dif_pos pos, convert dif_pos pos, },
      { convert (mul_zero m).symm,
        any_goals { convert dif_neg pos, }, },
      end, }, begin
    --simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    set K := 1 + ∥(c : ℚ)∥ + ∥((c : ℚ) - 1) / 2∥ with hK,
    have Kpos : 0 < K,
    { rw hK, rw add_comm, apply add_pos_of_nonneg_of_pos,
      { apply norm_nonneg, },
      { rw add_comm, apply add_pos_of_nonneg_of_pos,
        { apply norm_nonneg, },
        { apply zero_lt_one, }, }, },
    refine ⟨K, _, λ f, _⟩,
    { apply Kpos, },
    obtain ⟨n, hn⟩ := loc_const_eq_sum_char_fn p d R (loc_const_ind_fn R p d f) h',
    rw hn,
    rw linear_map.map_sum,
    convert le_trans (na (d * p^n) _) _,
    set a := ⨆ (i : zmod (d * p ^ n)),
      ∥distributions p d R hφ hc hc' h' (((loc_const_ind_fn R p d f) ↑(i.val)) •
      locally_constant.char_fn R (is_clopen_clopen_from p d n (i.val)))∥ with ha,
    set s := {i : zmod (d * p^n) | ∥distributions p d R hφ hc hc' h'
      ((loc_const_ind_fn R p d f) ↑(i.val) • locally_constant.char_fn R
      (is_clopen_clopen_from p d n ↑(i.val)))∥ = a } with hs,
    have nons : set.nonempty s,
    { sorry, }, --apply s_nonempty', rw ha, },
    set i := classical.some nons with hi,
    have hi' := classical.some_spec nons,
    rw set.mem_def at hi',
    change ∥distributions p d R hφ hc hc' h' ((loc_const_ind_fn R p d f) ↑(i.val) •
      locally_constant.char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a at hi',
    by_cases is_unit (i : zmod d) ∧ is_unit (i : ℤ_[p]),
    { suffices : a ≤ K * ∥(loc_const_ind_fn R p d f) ↑i∥,
      convert_to a ≤ _,
      apply le_trans this _,
      rw mul_le_mul_left _,
      rw continuous_map.norm_eq_supr_norm,
      apply le_cSup,
      { apply set.finite.bdd_above,
        change (set.range (λ (x : units (zmod d) × units ℤ_[p]), ∥f x∥)).finite,
        refine is_locally_constant.range_finite _,
        change is_locally_constant (norm ∘ f),
        apply is_locally_constant.comp f.is_locally_constant _, },
      { refine ⟨(is_unit.unit h.1, is_unit.unit h.2), _⟩,
        change ∥f.to_fun _ ∥ = _,
        rw ind_fn_eq_fun,
        rw loc_const_ind_fn,
        simp only [function.comp_app, locally_constant.coe_mk, prod.map_mk],
        refine congr_arg _ _, refine congr_arg _ _,
        rw prod.ext_iff,
        simp only [prod.snd_nat_cast, prod.fst_nat_cast, prod.map_mk],
        repeat { rw is_unit.unit_spec, },
        simp only [prod.fst_zmod_cast, prod.snd_zmod_cast, eq_self_iff_true, and_self], },
      { apply Kpos, },
      { rw ←hi',
        rw linear_map.map_smul,
        rw smul_eq_mul,
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm, apply mul_le_mul,
        { apply meas_E_c', },
        { simp only [zmod.nat_cast_val], },
        { apply norm_nonneg, },
        { apply le_of_lt, apply Kpos, }, }, },
    { have zer : (loc_const_ind_fn R p d f) ↑(i.val) = 0,
      { rw loc_const_ind_fn, simp only [locally_constant.coe_mk],
        rw ind_fn, convert dif_neg _, convert h,
        { simp only [prod.fst_zmod_cast, zmod.nat_cast_val], },
        { simp only [prod.snd_zmod_cast, zmod.nat_cast_val], }, },
      rw zer at hi', rw zero_smul at hi',
      simp only [linear_map.map_zero, norm_zero, finset.mem_range] at hi',
      rw hi'.symm at ha, rw ←ha,
      apply mul_nonneg,
      { apply le_of_lt, apply Kpos, },
      apply norm_nonneg, },
--this is the proof to show it is also a measure on zmod _ × ℤ_[p]
   end⟩
