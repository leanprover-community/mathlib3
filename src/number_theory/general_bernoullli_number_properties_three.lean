import number_theory.general_bernoullli_number_properties_two

variables {p d : nat} (m : nat) [fact (0 < d)] [fact (nat.prime p)]
  {R : Type*} [normed_comm_ring R] (χ : dirichlet_character R (d * p^m))

open_locale big_operators
open dirichlet_character

lemma lim_even_character_aux1 [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {x : ℕ} (ε : ℝ) (hε : 0 < ε)
  (hx : @N1 p d m _ _ R _ χ _ _ _ k hk (ε/2) (half_pos hε) ≤ x)
  (h'x : @N2 p d m _ _ R _ χ _ _ _ _ k hk (ε / 2) (half_pos hε) ≤ x) :
  ∥∑ (x : ℕ) in finset.range (d * p ^ x), (asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) ↑(x.succ) * ↑(x + 1) ^ (k - 1)∥ < ε :=
begin
  have pos : 0 < k - 1, { rw lt_tsub_iff_left, rw add_zero, apply hk, },
  have poss : 0 < d * p^x := fact.out _,
  convert_to ∥∑ (x : ℕ) in finset.range (d * p ^ x), (asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑x * ↑x ^ (k - 1) +
    (((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(1 + (d * p^x).pred : ℕ)) * (((1 + (d * p^x).pred : ℕ) : R) ^ (k - 1)))∥ < ε,
  { apply congr_arg,
    conv_rhs { rw finset.range_eq_Ico, rw finset.sum_eq_sum_Ico_succ_bot poss,
      rw ← nat.succ_pred_eq_of_pos poss, rw nat.succ_eq_add_one,
      rw ← finset.sum_Ico_add, rw nat.cast_zero, rw nat.cast_zero, rw zero_pow pos,
      { rw mul_zero, rw zero_add, rw ← add_sub_cancel (∑ (l : ℕ) in finset.Ico 0 (d * p ^ x).pred,
    (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(1 + l : ℕ) *
      ((1 + l : ℕ) : R) ^ (k - 1)) (((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑(1 + (d * p^x).pred : ℕ)) * (((1 + (d * p^x).pred : ℕ) : R) ^ (k - 1))),  --rw ← this,
      rw ← finset.sum_Ico_succ_top (nat.zero_le _),
      rw ← nat.succ_eq_add_one (d * p^x).pred, rw ← finset.range_eq_Ico,
      rw nat.succ_pred_eq_of_pos poss, rw sub_add_cancel, apply_congr, skip,
      rw add_comm (1 : ℕ) _, }, }, },
  { apply lt_of_le_of_lt (norm_add_le _ _) _,
    apply lt_of_le_of_lt (add_le_add (le_of_lt (N1_spec m na hk hχ hp (ε/2) (half_pos hε) x hx))
      (norm_mul_le _ _)) _,
    apply lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul (le_of_lt
      (dirichlet_character.lt_bound _ _)) le_rfl (norm_nonneg _) (le_of_lt
      (dirichlet_character.bound_pos _)) )) _,
    conv { congr, congr, skip, congr, skip, congr, rw add_comm 1 _, rw ← nat.succ_eq_add_one,
      rw nat.succ_pred_eq_of_pos poss, rw ← nat.succ_pred_eq_of_pos pos,
      rw pow_succ, },
    apply lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul le_rfl (norm_mul_le _ _) _
      (le_of_lt (dirichlet_character.bound_pos _)))) _,
    { apply norm_nonneg _, },
    rw ← mul_assoc,
    rw ← nat.cast_pow,
    apply lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul le_rfl (norm_le_one _) _ _)) _,
    { exact p, },
    { apply_instance, },
    { apply_instance, },
    { apply_instance, },
    { apply norm_nonneg _, },
    { apply mul_nonneg (le_of_lt (dirichlet_character.bound_pos _)) (norm_nonneg _), },
    rw mul_one, rw mul_comm,
    conv { congr, skip, rw ← add_halves ε, },
    rw add_lt_add_iff_left,
    apply N2_spec m na hk hχ hp (ε/2) (half_pos hε) x h'x, },
end

lemma aux_three {k : ℕ} (x : ℕ) [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] (hk : 1 < k) :
  0 ≤ (⨆ (x_1 : zmod k.pred), ∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
  ↑(k.pred.succ.choose x_1.val) * (↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥) *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound :=
begin
  haveI pred_pos : fact (0 < k.pred), { apply fact_iff.2 (nat.lt_pred_iff.2 hk), },
  apply mul_nonneg _ (le_of_lt (dirichlet_character.bound_pos _)),
  apply le_csupr_of_le,
  { apply set.finite.bdd_above _,
    { apply_instance, },
    exact set.finite_range (λ (x_1 : zmod (nat.pred k)), ∥(algebra_map ℚ R)
      (bernoulli ((nat.pred k).succ - x_1.val) * ↑((nat.pred k).succ.choose x_1.val) *
        (↑(d * p ^ x) ^ (nat.pred k - 1) / ↑(d * p ^ x) ^ x_1.val))∥), },
  { apply norm_nonneg _, },
  { exact 0, },
end

lemma norm_coe_nat_le_one [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R] (n : ℕ) : ∥(algebra_map ℚ R) n∥ ≤ 1 :=
begin
  rw [map_nat_cast, norm_coe_nat_eq_norm_ring_hom_map p],
  apply padic_int.norm_le_one,
end

noncomputable abbreviation N5 [normed_algebra ℚ_[p] R] [algebra ℚ R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) (ε : ℝ) (hε : 0 < ε) :=
  Inf { n : ℕ | ∀ (x : ℕ) (hx : n ≤ x), ∥((d * p ^ x : ℕ) : R)∥ * ((⨆ (x_1 : zmod k.pred),
  ∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) * ↑(k.pred.succ.choose x_1.val))∥) *
 -- (↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥) *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε}

lemma N5_spec [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N5 m χ hk ε hε ≤ x) :
  ∥((d * p ^ x : ℕ) : R)∥ * ((⨆ (x_1 : zmod k.pred),
  ∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) * ↑(k.pred.succ.choose x_1.val))∥ ) *
  --(↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥) *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε :=
begin
  have div_four_pos : 0 < ε/6, { linarith, },
  haveI pred_pos : fact (0 < k.pred), { apply fact_iff.2 (nat.lt_pred_iff.2 hk), },
  have nn : 0 ≤ (⨆ (x_1 : zmod k.pred), ∥(algebra_map ℚ R)
  (bernoulli (k.pred.succ - x_1.val) * ↑(k.pred.succ.choose x_1.val))∥) *
--  (↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥) *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
  { apply mul_nonneg _ (le_of_lt (dirichlet_character.bound_pos _)),
    apply le_csupr_of_le,
    { apply set.finite.bdd_above _,
      { apply_instance, },
      exact set.finite_range (λ (x_1 : zmod (nat.pred k)), ∥(algebra_map ℚ R)
        (bernoulli ((nat.pred k).succ - x_1.val) * ↑((nat.pred k).succ.choose x_1.val))∥), },
--          (↑(d * p ^ x) ^ (nat.pred k - 1) / ↑(d * p ^ x) ^ x_1.val))∥), },
    { apply norm_nonneg _, },
    { exact 0, }, },
  apply nat_spec _ _ x hx,
  refine ⟨classical.some (norm_lim_eq_zero' hε nn), λ y hy, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  exact d,
  exact p,
  any_goals { apply_instance, },
  apply classical.some_spec (norm_lim_eq_zero' hε nn) y hy,
end

lemma aux_four {k : ℕ} (ε : ℝ) (x : ℕ) [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (hε : ε > 0)
  (hx : x ≥ N5 m χ hk (ε/6) (by linarith)) :
  -- (hx : x ≥ classical.some (@norm_lim_eq_zero' d p _ _ R _ _ _
  -- (show 0 < ε / 4, by linarith) _ (aux_three d p m χ x na hk))) :
--  (ne_zero : ↑(d * p ^ x) ≠ 0) (coe_sub : ↑k - 1 = ↑(k - 1)) :
  ∥∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred, (1 / ((d * p ^ x : ℕ) : ℚ)) •
  ((asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)))
    ↑(x_1.succ) * (↑(d * p ^ x) * (∑ (z : ℕ) in finset.range k.pred,
  (algebra_map ℚ R) (bernoulli (k.pred.succ - z) * ↑(k.pred.succ.choose z) *
  (((x_1 + 1 : ℕ) : ℚ) ^ z / ↑(d * p ^ x) ^ z) * ↑(d * p ^ x) ^ k.pred))))∥ < ε / 3 :=
begin
  have div_four_pos : 0 < ε/6, { linarith, },
  have div_four_lt_div_two : ε/6 < ε/3, { linarith, },
  haveI pred_pos : fact (0 < k.pred), { apply fact_iff.2 (nat.lt_pred_iff.2 hk), },
  apply lt_of_le_of_lt _ div_four_lt_div_two,
  apply le_trans (na _ _) _,
  apply csupr_le (λ y, _),
  { apply_instance, },
  haveI : fact (0 < d * p^x) := infer_instance,
  conv { congr, congr, rw mul_comm ((asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑((zmod.val y).succ)) _,
    rw ← smul_mul_assoc, rw ← smul_mul_assoc, rw ← inv_eq_one_div,
    rw inv_smul_self (@nat.ne_zero_of_lt' 0 (d * p^x) _), rw one_mul, },
  apply le_trans (norm_mul_le _ _) _,
  apply le_trans (mul_le_mul (aux_two m na hk hχ hp _ _)
    (le_of_lt (dirichlet_character.lt_bound _ _)) _ _) _,
  { apply norm_nonneg _, },
  { apply mul_nonneg (norm_nonneg _) _,
    apply le_csupr_of_le,
    { apply set.finite.bdd_above _,
      { apply_instance, },
      exact set.finite_range (λ (x_1 : zmod (nat.pred k)), ∥(algebra_map ℚ R)
         (bernoulli ((nat.pred k).succ - x_1.val) * ↑((nat.pred k).succ.choose x_1.val) *
            (↑(d * p ^ x) ^ (nat.pred k - 1) / ↑(d * p ^ x) ^ x_1.val))∥), },
    { apply norm_nonneg _, },
    { exact 0, }, },
  { rw mul_assoc, apply le_of_lt_or_eq, left,
    have : (⨆ (x_1 : zmod k.pred), (∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
      ↑(k.pred.succ.choose x_1.val) * (↑(d * p ^ x) ^ (k.pred - 1) / ↑(d * p ^ x) ^ x_1.val))∥)) ≤
      ⨆ (x_1 : zmod k.pred), ∥(algebra_map ℚ R) (bernoulli (k.pred.succ - x_1.val) *
      ↑(k.pred.succ.choose x_1.val))∥,
    { apply csupr_le (λ y, _),
      { apply_instance, },
      apply le_csupr_of_le _ _,
      rw (algebra_map ℚ R).map_mul,
      rw div_eq_mul_inv,
      rw ← pow_sub₀ ((d * p^x : ℕ) : ℚ) _ _,
      rw ← nat.cast_pow,
      apply le_trans (norm_mul_le _ _) _,
      rw map_nat_cast,
      apply le_trans (mul_le_mul le_rfl (norm_le_one _) _ _) _,
      any_goals { apply_instance, },
      any_goals { apply norm_nonneg _, },
      { exact p, },
      any_goals { apply_instance, },
      { rw mul_one, },
      { exact nonzero_of_invertible ↑(d * p ^ x), },
      { apply nat.le_pred_of_lt,
        apply zmod.val_lt, },
      { apply set.finite.bdd_above _,
        exact nonempty.intro ε,
        exact set.finite_range (λ (x_1 : zmod (nat.pred k)), ∥(algebra_map ℚ R)
        (bernoulli ((nat.pred k).succ - x_1.val) * ↑((nat.pred k).succ.choose x_1.val))∥), }, },
    rw mul_comm, rw mul_assoc,
    apply lt_of_le_of_lt (mul_le_mul this le_rfl _ _) _,
    { apply mul_nonneg (le_of_lt (dirichlet_character.bound_pos _)) (norm_nonneg _), },
    { apply real.Sup_nonneg _ (λ x hx, _), cases hx with y hy, rw ← hy, apply norm_nonneg _, },
    rw mul_comm _ (∥↑(d * p ^ x)∥),
    rw mul_comm, rw mul_assoc,
    rw mul_comm ((χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) _,
    apply N5_spec m χ na hk hχ hp (ε/6) div_four_pos x hx, },
end
--set_option pp.implicit true

lemma mul_eq_asso_pri_char {n : ℕ} (χ : dirichlet_character R n) :
 χ.asso_primitive_character.conductor = χ.conductor :=
 (is_primitive_def χ.asso_primitive_character).1 (asso_primitive_character_is_primitive χ)

lemma lev_mul_eq_conductor {n : ℕ} (χ ψ : dirichlet_character R n) :
  lev (χ.mul ψ) = (χ.mul ψ).conductor :=
by { rw [mul, mul_eq_asso_pri_char], }

lemma nat.pred_add_one_eq_self {n : ℕ} (hn : 0 < n) : n.pred + 1 = n := nat.succ_pred_eq_of_pos hn

lemma aux_five_aux [algebra ℚ R] [normed_algebra ℚ_[p] R] [fact (0 < m)] (k : ℕ) {ε : ℝ}
  (hε : 0 < ε) :
  0 ≤ ∥(algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.pred.succ.succ))∥ * (χ.mul
  (teichmuller_character_mod_p' p R ^ k.pred.pred.succ.succ)).asso_primitive_character.bound ∧ 0 < ε/3 :=
begin
  split,
  { apply mul_nonneg (norm_nonneg _) (le_of_lt (dirichlet_character.bound_pos _)), },
  { linarith, },
end

noncomputable abbreviation N3 [normed_algebra ℚ_[p] R] [algebra ℚ R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) (ε : ℝ) (hε : 0 < ε) :=
  Inf { n : ℕ | ∀ (x : ℕ) (hx : n ≤ x), ∥((d * p ^ x : ℕ) : R)∥ * (∥(algebra_map ℚ R) (polynomial.eval 1
    (polynomial.bernoulli k.pred.pred.succ.succ))∥ * (χ.mul
  (teichmuller_character_mod_p' p R ^ k.pred.pred.succ.succ)).asso_primitive_character.bound) < ε}

lemma N3_spec [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N3 m χ hk ε hε ≤ x) :
  ∥((d * p ^ x : ℕ) : R)∥ * (∥(algebra_map ℚ R) (polynomial.eval 1 (polynomial.bernoulli k.pred.pred.succ.succ))∥ *
  (χ.mul (teichmuller_character_mod_p' p R ^ k.pred.pred.succ.succ)).asso_primitive_character.bound) < ε :=
begin
  apply nat_spec _ _ x hx,
  refine ⟨classical.some (norm_lim_eq_zero' hε (aux_five_aux m χ k hε).1), λ x hx, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  { exact d, },
  { exact p, },
  any_goals { apply_instance, },
  apply classical.some_spec (norm_lim_eq_zero' hε (aux_five_aux m χ k hε).1) x hx,
end

lemma aux_five [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R]  [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
-- (n : ℕ) --[fact (0 < n)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N3 m χ hk (ε / 3) (by linarith) ≤ x) :
  ∥(1 / ((d * p ^ x : ℕ) : ℚ)) • ((asso_dirichlet_character
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character)
  ↑(d * p ^ x) * ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
  (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k))))∥ < ε/3 :=
begin
  rw [mul_comm _ ((algebra_map ℚ R) (↑(d * p ^ x) ^ k) *
    (algebra_map ℚ R) (polynomial.eval (↑(d * p ^ x) / ↑(d * p ^ x)) (polynomial.bernoulli k))),
    mul_assoc, ← smul_mul_assoc, ← nat.succ_pred_eq_of_pos (pos_of_gt hk), pow_succ,
   (algebra_map ℚ R).map_mul, ← smul_mul_assoc, ← inv_eq_one_div, map_nat_cast,
   inv_smul_self (nat.ne_zero_of_lt' 0), one_mul, div_self _],
  { have pred_pos : 0 < k.pred := nat.lt_pred_iff.2 hk,
    rw [← nat.succ_pred_eq_of_pos pred_pos, pow_succ, (algebra_map ℚ R).map_mul, mul_assoc],
    apply lt_of_le_of_lt (norm_mul_le _ _) _,
    apply lt_of_le_of_lt (mul_le_mul le_rfl (norm_mul_le _ _) _ (norm_nonneg _)) _,
    { apply norm_nonneg _, },
    { rw ← nat.cast_pow,
      apply lt_of_le_of_lt (mul_le_mul le_rfl (mul_le_mul (norm_coe_nat_le_one _) le_rfl _ _) _ _) _,
      { exact p, },
      any_goals { apply_instance, },
      { apply norm_nonneg _, },
      { norm_num, },
      { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
      { apply norm_nonneg _, },
      { rw one_mul,
        apply lt_of_le_of_lt (mul_le_mul le_rfl (norm_mul_le _ _) _ (norm_nonneg _)) _,
        { apply norm_nonneg _, },
        { rw ← mul_assoc,
          apply lt_of_le_of_lt (mul_le_mul le_rfl (le_of_lt (dirichlet_character.lt_bound _ _))
            _ _) _,
          { apply norm_nonneg _, },
          { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
          { rw [mul_assoc, map_nat_cast],
            apply N3_spec m χ na hk hχ hp (ε/3) (by linarith) x hx, }, }, }, }, },
  { norm_cast, refine (nat.ne_zero_of_lt' 0), },
  { apply_instance, },
end

lemma aux_6_one [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  {k : ℕ} (hk : 1 < k) {ε : ℝ} (hε : 0 < ε) :
  0 < ε / (6 * ∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥) :=
begin
  apply div_pos hε _,
  apply mul_pos _ _,
  { linarith, },
  rw norm_pos_iff,
  rw algebra.algebra_map_eq_smul_one,
  simp only [bernoulli_one, div_eq_zero_iff, false_or, smul_eq_zero, or_false, ne.def,
    nat.cast_eq_zero, bit0_eq_zero, neg_eq_zero, one_ne_zero, mul_eq_zero],
  apply ne_zero_of_lt hk,
end

noncomputable abbreviation N4 [normed_algebra ℚ_[p] R] [algebra ℚ R]  [norm_one_class R] [fact (0 < m)]
  {k : ℕ} (hk : 1 < k) (ε : ℝ) (hε : 0 < ε) :=
  Inf { n : ℕ | ∀ (x : ℕ) (hx : n ≤ x), ∥((d * p ^ x : ℕ) : R)∥ * (∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥ *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε}

lemma N4_spec [nontrivial R] [no_zero_divisors R] [normed_algebra ℚ_[p] R] [algebra ℚ R] [norm_one_class R] [fact (0 < m)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) (ε : ℝ) (hε : 0 < ε) (x : ℕ)
  (hx : N4 m χ hk ε hε ≤ x) :
  ∥((d * p ^ x : ℕ) : R)∥ * (∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥ *
  (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound) < ε :=
begin
  have nz : (algebra_map ℚ R) (bernoulli 1 * ↑k) ≠ 0,
  { rw algebra.algebra_map_eq_smul_one,
    simp only [bernoulli_one, div_eq_zero_iff, false_or, smul_eq_zero, or_false, ne.def,
      nat.cast_eq_zero, bit0_eq_zero, neg_eq_zero, one_ne_zero, mul_eq_zero],
    apply ne_zero_of_lt hk, },
  have pos : 0 < ∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥ *
    (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
  { apply mul_pos (norm_pos_iff.2 nz) (dirichlet_character.bound_pos _), },
  apply nat_spec _ _ x hx,
  refine ⟨classical.some (norm_lim_eq_zero' hε (le_of_lt pos)), λ x hx, _⟩,
  { exact R, },
  any_goals { apply_instance, },
  { exact d, },
  { exact p, },
  any_goals { apply_instance, },
  apply classical.some_spec (norm_lim_eq_zero' hε (le_of_lt pos)) x hx,
end

lemma aux_6 [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R]  [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
-- (n : ℕ) --[fact (0 < n)]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) {ε : ℝ} (hε : 0 < ε) (x : ℕ)
  -- (h1x : classical.some (metric.tendsto_at_top.1 (sum_even_character d p m χ na hk hχ hp) _
  --   (@aux_6_one p _ R _ _ _ _ _ _ k hk ε hε)) ≤ x)
  (h1x : x ≥ @N1 p d m _ _ R _ χ _ _ _ k hk _ (half_pos (@aux_6_one p _ R  _ _ _ _ _ _ _ k hk ε hε)))
  (h2x : x ≥ @N2 p d m _ _ R _ χ _ _ _ _ k hk _ (half_pos (@aux_6_one p _ R _ _ _ _ _ _ _ k hk ε hε)))
  (h4x : x ≥ N4 m χ hk (ε / 6) (by linarith)) :
  -- (h2x : x ≥ classical.some (metric.tendsto_at_top.1
  --        (norm_lim_eq_zero d p (((d * p ^ x : ℕ) : R) ^ (k - 1).pred))
  --        (ε/(4 * ((χ.mul (teichmuller_character_mod_p' p R ^ k)).bound))) (div_pos hε (mul_pos zero_lt_four (dirichlet_character.bound_pos _))) )) :
  ∥(1 / ((d * p ^ x : ℕ) : ℚ)) •
      ∑ (x_1 : ℕ) in finset.range (d * p ^ x).pred, (asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ) *
    ((algebra_map ℚ R) (bernoulli 1 * ↑k) * ↑(d * p ^ x) * ↑(1 + x_1) ^ (k - 1))∥ < ε / 3 :=
begin
  have six_pos : 0 < ε/6, { apply div_pos hε _, linarith, },
  have nz : (algebra_map ℚ R) (bernoulli 1 * ↑k) ≠ 0,
  { rw algebra.algebra_map_eq_smul_one,
    simp only [bernoulli_one, div_eq_zero_iff, false_or, smul_eq_zero, or_false, ne.def,
      nat.cast_eq_zero, bit0_eq_zero, neg_eq_zero, one_ne_zero, mul_eq_zero],
    apply ne_zero_of_lt hk, },
  have nnz : ∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥ ≠ 0,
  { simp only [bernoulli_one, div_eq_zero_iff, false_or, norm_eq_zero, ring_hom.map_eq_zero,
      ne.def, nat.cast_eq_zero, bit0_eq_zero, neg_eq_zero, one_ne_zero, mul_eq_zero],
    apply ne_zero_of_lt hk, },
  conv { congr, congr, conv { congr, skip,
  conv { apply_congr, skip, rw ← mul_assoc,
  rw mul_comm ((asso_dirichlet_character (χ.mul
    (teichmuller_character_mod_p' p R ^ k))) ↑(x_1.succ)) _,
  rw mul_assoc, rw mul_comm _ (↑(d * p ^ x)), rw add_comm 1 x_1, },
  rw ← finset.mul_sum, },
  rw ← smul_mul_assoc, rw ← smul_mul_assoc,
  rw one_div_smul_self R (@nat.ne_zero_of_lt' 0 (d * p^x) _), rw one_mul, },
  have poss : 0 < d * p^x := fact.out _,
  conv { congr, congr, conv { congr, skip,
  conv { rw ← add_sub_cancel (∑ (x : ℕ) in finset.range (d * p ^ x).pred,
  (asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)))
  ↑(x.succ) * ↑(x + 1) ^ (k - 1)) ((asso_dirichlet_character (χ.mul
  (teichmuller_character_mod_p' p R ^ k))) ↑((d * p^x).pred.succ) *
  ↑((d * p^x).pred + 1) ^ (k - 1)),
  rw ← finset.sum_range_succ,
  rw nat.pred_add_one_eq_self poss,
  congr, skip, rw ← nat.pred_eq_sub_one k,
  rw ← nat.succ_pred_eq_of_pos (nat.lt_pred_iff.2 hk),
  rw pow_succ', rw ← mul_assoc, rw mul_comm, }, }, rw mul_sub, },
  apply lt_of_le_of_lt (norm_sub_le _ _) _,
  apply lt_of_le_of_lt (add_le_add (norm_mul_le _ _) le_rfl) _,
  apply lt_of_le_of_lt (add_le_add (mul_le_mul le_rfl (le_of_lt (lim_even_character_aux1
    m χ na hk hχ hp (ε/(6 * ∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥)) _ h1x h2x)) _ _) le_rfl) _,
  { apply norm_nonneg _, },
  { apply norm_nonneg _, },
  { conv { congr, congr,
      rw mul_comm (6 : ℝ) _,
      rw ← mul_div_assoc,
      rw mul_div_mul_left _ _ nnz, skip,
      rw ← mul_assoc _ ↑(d * p^x) _, },
    apply lt_of_le_of_lt (add_le_add le_rfl (norm_mul_le _ _)) _,
    have nlt : ∥(asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k))) ↑((d * p ^ x).pred.succ) * ↑(d * p ^ x) ^ k.pred.pred∥ <
      dirichlet_character.bound (χ.mul (teichmuller_character_mod_p' p R ^ k)),
    { apply lt_of_le_of_lt (norm_mul_le _ _) _,
      rw ← mul_one (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
      apply mul_lt_mul (dirichlet_character.lt_bound _ _) _ _
        (le_of_lt (dirichlet_character.bound_pos _)),
      { rw ← nat.cast_pow, rw norm_coe_nat_eq_norm_ring_hom_map p, apply padic_int.norm_le_one, },
      { rw norm_pos_iff, rw ← nat.cast_pow, --norm_cast,
        haveI : algebra ℚ_[p] R := infer_instance,
        refine nat.cast_ne_zero.2 (pow_ne_zero _ (ne_zero_of_lt poss)), }, },
    apply lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul le_rfl (le_of_lt nlt) _ (norm_nonneg _))) _,
    { apply norm_nonneg _, },
    { apply lt_of_le_of_lt (add_le_add le_rfl (mul_le_mul (norm_mul_le _ _) le_rfl
        (le_of_lt (dirichlet_character.bound_pos _)) _)) _,
      { apply mul_nonneg (norm_nonneg _) (norm_nonneg _), },
      rw mul_comm _ (∥↑(d * p ^ x)∥),
      rw mul_assoc,
      have add_six : ε/6 + ε/6 = ε/3, linarith,
      have pos : 0 < ∥(algebra_map ℚ R) (bernoulli 1 * ↑k)∥ *
        (χ.mul (teichmuller_character_mod_p' p R ^ k)).bound,
      { apply mul_pos (norm_pos_iff.2 nz) (dirichlet_character.bound_pos _), },
      rw ← add_six,
      rw add_lt_add_iff_left,
      apply N4_spec m χ na hk hχ hp (ε/6) (by linarith) _ h4x, }, },
end

lemma asso_dirichlet_character_equiv {S : Type*} [comm_monoid_with_zero S]
  (ψ : dirichlet_character S m) (h : is_primitive ψ) (a : ℕ) :
  asso_dirichlet_character ψ.asso_primitive_character a = asso_dirichlet_character ψ a :=
begin
  by_cases h' : is_unit (a : zmod m),
  { conv_rhs { rw factors_through_spec ψ (factors_through_conductor ψ), },
    rw change_level_asso_dirichlet_character_eq' _ _ h',
    apply congr,
    { congr, },
    { rw zmod.cast_nat_cast _,
      swap, { refine zmod.char_p _, },
      { apply conductor_dvd _, }, }, },
  { repeat { rw asso_dirichlet_character_eq_zero, },
    { assumption, },
    rw (is_primitive_def _).1 h, apply h', },
end
.
lemma lim_even_character [nontrivial R] [no_zero_divisors R] [algebra ℚ R]
  [normed_algebra ℚ_[p] R] [norm_one_class R] [is_scalar_tower ℚ ℚ_[p] R]
  (na : ∀ (n : ℕ) (f : ℕ → R), ∥ ∑ (i : ℕ) in finset.range n, f i∥ ≤ ⨆ (i : zmod n), ∥f i.val∥)
  [fact (0 < m)] {k : ℕ} (hk : 1 < k) (hχ : χ.is_even) (hp : 2 < p) :
  filter.tendsto (λ n, (1/((d * p^n : ℕ) : ℚ)) • ∑ i in finset.range (d * p^n), ((asso_dirichlet_character
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R ^ k)))
  i * i^k) ) (@filter.at_top ℕ _) (nhds (general_bernoulli_number
  (dirichlet_character.mul χ (teichmuller_character_mod_p' p R ^ k)) k)) :=
begin
  rw metric.tendsto_at_top,
  intros ε hε,
  have six_pos : 0 < ε/6, linarith,
  have three_pos : 0 < ε/3, linarith,
  obtain ⟨N, hN⟩ := metric.tendsto_at_top'.1 (sum_even_character m hk hχ hp na) ε hε,
  set s : set ℕ := {N, m, @N1 p d m _ _ R _ χ _ _ _ k hk _ (half_pos (@aux_6_one p _ R _ _ _ _ _ _ _ k hk ε hε)),
    @N2 p d m _ _ R _ χ _ _ _ _ k hk _ (half_pos (@aux_6_one p _ R _ _ _ _ _ _ _ k hk ε hε)),
    N3 m χ hk (ε / 3) three_pos, N4 m χ hk (ε / 6) six_pos,
    N5 m χ hk (ε / 6) six_pos} with hs,
  set l : ℕ := Sup s with hl,
  refine ⟨l, λ x hx, _⟩,
  have hx' : ∀ y ∈ s, y ≤ x,
  { intros y hy, apply le_trans _ hx,
    apply le_cSup _ hy,
    { apply set.finite.bdd_above,
      simp only [set.finite_singleton, set.finite.insert], }, },
  rw dist_eq_norm,
  rw general_bernoulli_number.eq_sum_bernoulli_of_conductor_dvd _ k _,
  swap 2, { exact (d * p^x), },
  swap 2, { apply_instance, },
  swap, { --rw ← lev_mul_eq_conductor,
    apply dvd_trans (conductor_dvd _) (dvd_trans (conductor_dvd _) _),
    rw helper_4 m,
--    apply dvd_trans (dirichlet_character.lev_mul_dvd' _ _) _,
    rw nat.mul_dvd_mul_iff_left (fact.out _), apply pow_dvd_pow _ (hx' _ _),
    { simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true], },
    any_goals { apply_instance, }, }, -- is it better to give an explicit hypo or use apply_instance?
  have ne_zero : ((d * p^x : ℕ) : ℚ) ≠ 0,
  { norm_cast,
    refine nat.ne_zero_of_lt' 0, },
  have poss : 0 < d * p^x := fact.out _,
  have coe_sub : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ),
  { change int.of_nat k - 1 = int.of_nat (k - 1),
    rw int.of_nat_sub (le_of_lt hk),
    rw int.of_nat_one, },
  conv { congr, congr,
    conv { congr, skip, rw coe_sub, rw zpow_coe_nat,
    rw [← one_mul ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ (k - 1)))],
    rw ← (algebra_map ℚ R).map_one, rw ← one_div_mul_cancel ne_zero, rw (algebra_map ℚ R).map_mul,
    rw mul_assoc _ _ ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ (k - 1))),
    rw ← (algebra_map ℚ R).map_mul, rw ← pow_succ, rw nat.sub_add_cancel (le_of_lt hk),
    rw mul_assoc, rw algebra.algebra_map_eq_smul_one, rw smul_mul_assoc, rw one_mul,
    rw finset.mul_sum, congr, skip, apply_congr, skip,
    rw mul_comm ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k)) _,
    rw mul_assoc,
    rw mul_comm _ ((algebra_map ℚ R) (((d * p ^ x : ℕ) : ℚ) ^ k)), }, rw ← smul_sub,
    rw finset.range_eq_Ico,
    conv { rw finset.sum_eq_sum_Ico_succ_bot poss,
      rw nat.cast_zero, rw nat.cast_zero, rw zero_pow (pos_of_gt hk), rw mul_zero, rw zero_add,
      rw ← nat.sub_add_cancel (nat.succ_le_iff.2 poss),
      rw ← finset.sum_Ico_add, rw finset.sum_Ico_succ_top (nat.zero_le _) _,
      rw ← finset.range_eq_Ico, rw ← nat.pred_eq_sub_one,
      rw nat.succ_pred_eq_of_pos poss, }, rw ← sub_sub, rw smul_sub, },
  have : ∀ x : ℕ, asso_dirichlet_character (χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character x = asso_dirichlet_character (χ.mul
      (teichmuller_character_mod_p' p R ^ k)) x,
  { apply asso_dirichlet_character_equiv,
    apply is_primitive_mul, },
  have f1 : ((χ.mul (teichmuller_character_mod_p' p R ^ k)).asso_primitive_character).conductor = ((χ.mul
      (teichmuller_character_mod_p' p R ^ k))).conductor,
  { rw mul_eq_asso_pri_char, },
  conv { congr, congr, congr, conv { congr, skip, congr, skip, conv { apply_congr, skip,
    rw nat.pred_add_one_eq_self poss,
    rw aux_one m na hk hχ hp x _,
    rw add_assoc,
    rw mul_add, rw this _,
    rw add_comm _ 1,
    conv { congr, congr, rw nat.succ_eq_add_one, rw add_comm x_1 1, }, }, }, },
    rw finset.sum_add_distrib, rw ← sub_sub, rw sub_self,
    rw smul_sub, rw sub_sub, rw smul_zero,
    rw zero_sub,
  rw norm_neg,
  rw nat.pred_add_one_eq_self poss,
  conv { congr, congr, congr, congr, skip, conv { apply_congr, skip, rw mul_add, },
    rw finset.sum_add_distrib, },
  rw smul_add,
  simp_rw [nat.pred_eq_sub_one k],
  apply lt_of_le_of_lt (norm_add_le _ _) _,
  apply lt_of_le_of_lt (add_le_add (norm_add_le _ _) le_rfl) _,
  have add_third : ε/3 + ε/3 + ε/3 = ε, linarith,
  have three_pos : 0 < ε/3, { apply div_pos hε _, linarith, },
  have six_pos : 0 < ε/6, { apply div_pos hε _, linarith, },
  apply lt_of_lt_of_le _ (le_of_eq add_third),
  apply add_lt_add _ _,
  { exact covariant_add_lt_of_contravariant_add_le ℝ, },
  { exact covariant_swap_add_le_of_covariant_add_le ℝ, },
  { apply add_lt_add _ _,
    { exact covariant_add_lt_of_contravariant_add_le ℝ, },
    { exact covariant_swap_add_le_of_covariant_add_le ℝ, },
    { apply aux_6 m χ na hk hχ hp hε,
      any_goals { apply hx' _ _,
      simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true], }, },
    { rw finset.smul_sum,
      convert aux_four m χ ε x na hk hχ hp hε _,
      simp_rw [add_comm 1 _], refl,
      { apply hx' _ _,
        simp, }, }, },
  { apply aux_five m χ na hk hχ hp ε hε,
    { apply hx' _ _,
      simp only [set.mem_insert_iff, true_or, eq_self_iff_true, or_true], }, },
end
-- don't think χ.mul ω⁻¹ is needed, any character whose conductor divides d * p^m should work
