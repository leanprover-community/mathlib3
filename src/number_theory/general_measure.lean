import number_theory.weight_space

--variables (A : Type*) [topological_space A] [mul_one_class A]
variables (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
variables [fact (0 < d)] {c : ℕ}
variables [normed_algebra ℚ R] [norm_one_class R]

local attribute [instance] zmod.topological_space

open_locale big_operators

/-/-- Given a profinite space `X` and a normed commutative ring `A`, a `p-adic measure` is a
  "bounded" linear map from the locally constant functions from `X` to `A` to `A` -/
def measures' :=
  {φ : (locally_constant (units (zmod d) × units ℤ_[p]) R) →ₗ[R] R //
    ∃ K : ℝ, 0 < K ∧ ∀ f : (locally_constant (zmod d × ℤ_[p]) R),
    ∀ (n : ℕ) (a : zmod (d * p^n)),
    ∥ φ (loc_const_ind_fn _ p d (locally_constant.char_fn R (is_clopen_clopen_from p d n a))) ∥ ≤ K }-/

@[to_additive] lemma locally_constant.prod_apply {B C s : Type*} [topological_space B]
  [comm_monoid C] [fintype s] (n : ℕ)
  (f : s → (locally_constant B C)) {x : B} :
  (∏ i : s, (f i)) x =
  ∏ i : s, ((f i) x) :=
begin
  induction n with d hd,
  { simp only [locally_constant.coe_one, finset.range_zero, finset.prod_empty, pi.one_apply], },
  { rw finset.prod_range_succ,
    rw locally_constant.mul_apply, rw hd,
    rw finset.prod_range_succ, },
end

lemma char_fn_eq_sum_char_fn [nontrivial R] (hd' : d.gcd p = 1) (n : ℕ) (a : zmod (d * p^n))
  (x : zmod d × ℤ_[p]) :
  locally_constant.char_fn R (is_clopen_clopen_from p d n a) x =
  ∑ (b : equi_class p d n n.succ (nat.le_succ n) a),
  locally_constant.char_fn R (is_clopen_clopen_from p d n.succ b) x :=
begin
  by_cases x ∈ clopen_from p d n a,
  { rw (locally_constant.char_fn_one _ _ _).1 h,
    { rw finset.sum_eq_single,
      swap 4, { constructor, swap,
      apply (zmod.chinese_remainder _).inv_fun (x.1, padic_int.to_zmod_pow n.succ x.2),
      { rw nat.coprime_pow_right_iff _, assumption,
        apply nat.succ_pos, },
      rw mem_equi_class, rw mem_clopen_from at h, rw h.1, sorry, },
      sorry,
      sorry,
      sorry, },
    { apply_instance, }, },
  sorry,
end

variables {φ : linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R}
  (hφ : ∀ (l : ℕ) (x : zmod (d * p^l)), ∑ (y : zmod (d * p ^ l.succ)) in (λ a : zmod (d * p ^ l),
    set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a)) x, (φ (locally_constant.char_fn R (is_clopen_clopen_from p d l.succ y))) = φ (locally_constant.char_fn R (is_clopen_clopen_from p d l x)))

lemma succ_eq_bUnion_equi_class' {n : ℕ} (hn : m < n) : zmod' (d*p^n) (mul_prime_pow_pos p d n) =
  (zmod' (d*p^m) (mul_prime_pow_pos p d m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m n (le_of_lt hn)) a)) :=
begin
  ext y, simp only [exists_prop, finset.mem_bUnion, set.mem_to_finset], split,
  any_goals { intro h, },
  { refine ⟨(y : zmod (d * p^m)), _, _⟩,
    { rw finset.mem_def, exact finset.mem_univ y, },
    { rw mem_equi_class, }, },
  { rw finset.mem_def, exact finset.mem_univ y, },
end

/-- An eventually constant sequence constructed from a locally constant function. -/
noncomputable def g' (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  {φ : linear_map (ring_hom.id R) (locally_constant ((zmod d) × ℤ_[p]) R) R}
  (hφ : ∀ (l : ℕ) (x : zmod (d * p^l)), ∑ (y : zmod (d * p ^ l.succ)) in (λ a : zmod (d * p ^ l),
    set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a)) x, (φ (locally_constant.char_fn R (is_clopen_clopen_from p d l.succ y))) = φ (locally_constant.char_fn R (is_clopen_clopen_from p d l x)))
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : d.gcd p = 1) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ),
    ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos p d n)), f(a) • (φ (locally_constant.char_fn R (is_clopen_clopen_from p d n a))),
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

/-noncomputable abbreviation distri_bound (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  (hd' : d.gcd p = 1) : ℝ :=
⨆ (a : zmod (d * p^(sequence_limit_index' (g' p d R hc hc' hd hφ 1 hd')))),
  (∥φ (locally_constant.char_fn R (is_clopen_clopen_from p d _ a))∥ : ℝ) -/

lemma g'_def (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : d.gcd p = 1) :
  (g' p d R hc hc' hd hφ f hd').to_seq n =
    ∑ a in (finset.range (d * p^n)),f(a) • (φ (locally_constant.char_fn R (is_clopen_clopen_from p d n a))) :=
begin
  rw g', simp only,
  apply finset.sum_bij,
  swap 5, { rintros, exact a.val, },
  any_goals { rintros, simp, },
  { apply zmod.val_lt, },
  { rintros a b ha hb h, simp only at h, apply zmod.val_injective _ h, },
  { refine ⟨(b : zmod (d * p^n)), _, _⟩,
    { apply finset.mem_univ, },
    { apply (zmod.val_cast_of_lt (finset.mem_range.1 H)).symm, }, },
end

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

/-lemma le_distri_bound {n : ℕ} (a : zmod (d * p^n)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (hd : 0 < d) (h' : d.gcd p = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) :
∥distributions p d R hφ hc hc' h' (locally_constant.char_fn R (is_clopen_clopen_from p d n a))∥ ≤
  distri_bound p d R hφ hc hc' hd h' :=
begin
--  by_cases h1 : sequence_limit_index' (g' p d R hc hc' _ hφ (locally_constant.char_fn R (is_clopen_clopen_from p d n a)) h') ≤ n,

  delta distri_bound,
  rw distributions, simp,
  set m := max (sequence_limit_index' (g' p d R hc hc' (fact.out _) hφ (locally_constant.char_fn R
    (is_clopen_clopen_from p d n a)) h')) (sequence_limit_index' (g' p d R hc hc' (fact.out _) hφ 1 h')),
  rw sequence_limit_eq _ m _,
  --delta g',
  --rw (g' p d R hc hc' _ hφ (locally_constant.char_fn R (is_clopen_clopen_from p d n a)) h').to_seq, simp,
  --simp,
  --rw succ_eq_bUnion_equi_class' _ _ _ h1,
  rw g'_def,
  apply le_trans (na _ _) _,
  apply csupr_le,
  intro x,
  rw smul_eq_mul,
  apply le_trans (norm_mul_le _ _) _,
  have : ∥locally_constant.char_fn R (is_clopen_clopen_from p d n a) (x.val)∥ ≤ 1,
  sorry,
  apply le_trans (mul_le_mul this le_rfl _ _) _,
  sorry,
  sorry,
  rw one_mul,
  apply le_cSup _ _,
  sorry,
  simp,
  refine ⟨x.val, _⟩,
  simp,
  refl,

  induction n with k hk,
  { sorry, },
  { specialize hk a, apply le_trans _ hk,
    rw distributions, simp only [linear_map.coe_mk],
    by_cases h1 : sequence_limit_index' (g' p d R hc hc' _ hφ (locally_constant.char_fn R _) h') ≤ k,
    repeat { rw sequence_limit_eq _ _ h1, rw g'_def, },

    rw sequence_limit_eq _ _ (le_trans h1 (nat.le_succ k)),
    conv { congr, skip, congr, apply_congr, skip, rw ← hφ, rw finset.smul_sum, simp, },

    rw ← hφ k,
    rw distributions, simp only [algebra.id.smul_eq_mul, linear_map.coe_mk],
    delta distri_bound,
    rw ← hφ at hd,
    sorry },
end

lemma distri_bound_pos (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  (hd : 0 < d) (h' : d.gcd p = 1) : 0 < distri_bound p d R hφ hc hc' hd h' := sorry -/

lemma s_nonempty'' (n : ℕ) (f : locally_constant (units (zmod d) × units ℤ_[p]) R) (a : ℝ)
  (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (h' : d.gcd p = 1)
  (ha : a = ⨆ (i : zmod (d * p ^ n)),
      ∥distributions p d R hφ hc hc' h' (((loc_const_ind_fn R p d f) ↑(i.val)) •
      locally_constant.char_fn R (is_clopen_clopen_from p d n (i.val)))∥ ) :
  {i : zmod (d * p^n) | ∥distributions p d R hφ hc hc' h'
      ((loc_const_ind_fn R p d f) ↑(i.val) • locally_constant.char_fn R
      (is_clopen_clopen_from p d n ↑(i.val)))∥ = a }.nonempty :=
sorry
/-begin
  have := set.nonempty.cSup_mem,
  swap 4, { refine set.range (λ (i : zmod (d * p^n)),
    ∥((bernoulli_distribution p d R hc hc' h'))
    (f ↑i • char_fn R (is_clopen_clopen_from p d n i))∥), },
  swap, { apply_instance, },
  specialize this _ _,
  { rw set.range_nonempty_iff_nonempty, apply_instance, },
  { rw ←set.image_univ, apply set.finite.image, exact set.finite_univ, },
  { suffices : a ∈ set.range (λ (i : zmod (d * p^n)),
      ∥(bernoulli_distribution p d R hc hc' h')
      (f ↑i • char_fn R (is_clopen_clopen_from p d n i))∥),
    { cases this with y hy,
      simp only [algebra.id.smul_eq_mul, linear_map.map_smul] at hy,
      use y,
      simp only [zmod.cast_id', algebra.id.smul_eq_mul, id.def, set.mem_set_of_eq,
        finset.mem_range, linear_map.map_smul, zmod.nat_cast_val],
      refine hy, },
    { convert this using 1, rw ha,
      convert_to Sup (set.range (λ (i :zmod (d * p ^ n)),
        ∥(bernoulli_distribution p d R hc hc' h')
      ((f ↑(i.val)) • char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥)) = _,
      refine congr_arg _ _,
      simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end-/

/-abbreviation measure_of_is_bounded (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) (hb : is_bounded φ) : measures (units (zmod d) × units ℤ_[p]) R :=
⟨{ to_fun := λ f, distributions p d R hφ hc hc' h' (loc_const_ind_fn _ p d f),
    map_add' := λ f1 f2, begin
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
        any_goals { convert dif_neg pos, }, }, end,
    map_smul' := λ m f, begin
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
        any_goals { convert dif_neg pos, }, }, end, }, sorry⟩
#exit-/

variable (φ)

def is_bounded (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (a : zmod (d * p^n)),
--∥ φ (locally_constant.char_fn R (is_clopen_clopen_from p d n a)) ∥ < K
∥(distributions p d R hφ hc hc' h') (locally_constant.char_fn R (is_clopen_clopen_from p d n a))∥ ≤ K

noncomputable def measures_general (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (hb : is_bounded p d R φ hφ hc hc' h') (na : ∀ (n : ℕ) (f : ℕ → R),
  ∥∑ i in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f (i.val)∥ ) : measures (units (zmod d) × units ℤ_[p]) R :=
  ⟨{ to_fun := λ f, distributions p d R hφ hc hc' h' (loc_const_ind_fn _ p d f),
    map_add' := λ f1 f2, begin
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
        any_goals { convert dif_neg pos, }, }, end,
    map_smul' := λ m f, begin
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
        any_goals { convert dif_neg pos, }, }, end, },
  begin
    simp only [linear_map.coe_mk, locally_constant.to_fun_eq_coe],
    have d_pos : 0 < d, { convert fact_iff.1 (hd 0), rw [pow_zero, mul_one], },
    set K' := classical.some hb,
    set hK' := classical.some_spec hb,
    refine ⟨K', hK'.1, λ f, _⟩,
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
    { apply s_nonempty'', rw ha, },
    set i := classical.some nons with hi,
    have hi' := classical.some_spec nons,
    rw set.mem_def at hi',
    change ∥distributions p d R hφ hc hc' h' ((loc_const_ind_fn R p d f) ↑(i.val) •
      locally_constant.char_fn R (is_clopen_clopen_from p d n ↑(i.val)))∥ = a at hi',
    by_cases is_unit (i : zmod d) ∧ is_unit (i : ℤ_[p]),
    { suffices : a ≤ K' * ∥(loc_const_ind_fn R p d f) ↑i∥,
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
      { apply hK'.1, },
      { rw ←hi',
        rw linear_map.map_smul,
        rw smul_eq_mul,
        apply le_trans (norm_mul_le _ _) _,
        rw mul_comm, apply mul_le_mul,
        { apply hK'.2, },
        { simp only [zmod.nat_cast_val], },
        { apply norm_nonneg, },
        { apply le_of_lt, apply hK'.1, }, }, },
    { have zer : (loc_const_ind_fn R p d f) ↑(i.val) = 0,
      { rw loc_const_ind_fn, simp only [locally_constant.coe_mk],
        rw ind_fn, convert dif_neg _, convert h,
        { simp only [prod.fst_zmod_cast, zmod.nat_cast_val], },
        { simp only [prod.snd_zmod_cast, zmod.nat_cast_val], }, },
      rw zer at hi', rw zero_smul at hi',
      simp only [linear_map.map_zero, norm_zero, finset.mem_range] at hi',
      rw hi'.symm at ha, rw ←ha,
      apply mul_nonneg,
      { apply le_of_lt, apply hK'.1, },
      apply norm_nonneg, },
    end⟩
