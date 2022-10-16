
/-
Copyright (c) 2022 Georgi Kocharyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgi Kocharyan
-/
import .geodesic_space
import .marked_group

/-!
# The Švarc-Milnor theorem

## References

The proof is taken from *Geometric group theory: An introduction*, Clara Löh.
-/

open classical geometric_group_theory metric set
open_locale big_operators pointwise

variables {α β : Type*} [group α] {c b L : ℝ} [quasigeodesic_space β c b] [iso_mul_action α β]
  {s : set β} {g h : α} {x y : β}
include c b

/-- if `x` and `y` in the metric space are close together, the translates of `s` they are in only
differ by an element of the generating set. -/
lemma intS (hx : x ∈ g • s) (hy : y ∈ h • s) (hd : dist x y ≤ 2 * b) :
  ∃ t ∈ proper_action_set α (set_closed_ball s (2*b)), g * t = h :=
begin
  refine ⟨g⁻¹ * h, _, by simp⟩,
  have hy' : y ∈ set_closed_ball (g • s) (2*b) := ⟨x, hx, by rwa dist_comm⟩,
  rw ←isom_of_set_closed_ball at hy',
  have hy'' : y ∈ h • (set_closed_ball s (2*b)),
  { obtain ⟨w, ws, rfl⟩ := hy,
    refine ⟨w, _, rfl⟩,
    apply self_set_closed_ball,
    exact dist_nonneg.trans hd,
    exact ws },
  refine ⟨g⁻¹ • y, by rwa ←mem_smul_set_iff_inv_smul_mem, _⟩,
  rwa [←mem_smul_set_iff_inv_smul_mem, mul_smul, smul_inv_smul],
end

/-- The map `g` to `g • x` has quasi-dense image. -/
lemma svarcmilnor_qdense (hs : translates_cover α s) (finitediam : metric.bounded s) (xs : x ∈ s) :
  has_quasidense_image (λ g : α, g • x) :=
begin
  obtain ⟨k, hk⟩ := finitediam,
  have knonneg : 0 ≤ k := dist_nonneg.trans (hk x xs x xs),
  refine ⟨k + 1, by positivity, λ y, _⟩,
  obtain ⟨g, z, hz, rfl⟩ := hs y,
  refine ⟨g, _⟩,
  rw dist_smul_smul,
  exact (hk x xs z hz).trans (le_add_of_nonneg_right zero_le_one),
end

variables (cpos : 0 < c) (bpos : 0 < b)
omit c b
include bpos cpos

lemma sm_aux (hs : translates_cover α s) (f : ℝ → β) (x : β) (xs : x ∈ s) (n : ℕ) :
   ∀ (g : α) (L : ℝ) (Lnonneg : 0 ≤ L) (hL' : L ≤ (n : ℝ)*(b/c)),
    (∃ y ∈ g • s, quasigeodesic L f x y c b) →
      g ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2*b))) :=
begin
  induction n with n hn,
  { rintro g L Lnonneg hL ⟨y, hy, qg⟩,
    norm_cast at hL,
    rw zero_mul at hL,
    -- if the quasigeodesic has length 0, the end points differ by an element of S
    have Lzero : L = 0, by apply le_antisymm hL Lnonneg,
    obtain rfl : x = y := degenerate_quasigeodesic f x y c b (by rwa ←Lzero),
    apply subgroup.subset_closure,
    rw ←one_smul α s at xs,
    obtain ⟨t, ht, rfl⟩ := intS xs hy (by { rw dist_self, positivity }),
    rwa one_mul },
  -- truncate quasigeodesic to length where we can apply induction hypothesis
  set L' : ℝ := n * (b / c) with hL',
  have L'nonneg : 0 ≤ L', by { rw hL', positivity },
  rintro g L Lnonneg hL ⟨y, hy, qg⟩,
  obtain hL' | hL' := le_total L L',
  { exact hn g L Lnonneg hL' ⟨y, hy, qg⟩ },
  simp only [exists_prop, forall_exists_index, and_imp] at hn,
  rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one] at hL,
  -- endpoint of new quasigeodesic is covered
  obtain ⟨g', hg'⟩ := hs (f L'),
  have g'_mem_closure : g' ∈ subgroup.closure (proper_action_set α (set_closed_ball s (2 * b))),
    from hn g' L' L'nonneg le_rfl (f L') hg' (qg.mono f hL'),
  have smalldistdom : |L' - L| ≤ b/c,
  { rw [abs_sub_comm, abs_of_nonneg, sub_le_iff_le_add', ←one_mul (b/c), ←add_mul],
    rwa add_comm,
    linarith },
  have smalldistimg : dist (f L') (f L) ≤ 2 * b,
    calc
      dist (f L') (f L) ≤ c * |L' - L| + b : (qg.2.2 ⟨L'nonneg, hL'⟩ ⟨Lnonneg, le_rfl⟩).2
      ...               ≤ c * (b/c) + b
                        : add_le_add_right (mul_le_mul_of_nonneg_left smalldistdom cpos.le) _
      ...               = 2 * b : by rw [mul_div_cancel' _ cpos.ne', two_mul],
  apply closure_mul g' (proper_action_set α (set_closed_ball s (2 * b))) g'_mem_closure g,
  refine intS hg' _ smalldistimg,
  rwa qg.2.1,
end

omit bpos cpos

variables [hβ : nonempty β]
include bpos cpos hβ

/-- Švarc-Milnor part 1: `S` generates `G` -/
theorem metric_svarcmilnor1 (s : set β) (hs : translates_cover α s) :
  subgroup.closure (proper_action_set α (set_closed_ball s (2*b))) = ⊤ :=
begin
  rw subgroup.eq_top_iff',
  intro g,

-- construct an element of s called t
  obtain ⟨t, ts⟩ := hs.nonempty,

-- connect t and g • t via a quasigeodesic and then apply sm_aux to get that g is generated
  obtain ⟨L, Lnonneg, f, qif⟩ : conn_by_quasigeodesic' t (g • t) c b :=
    quasigeodesic_space.quasigeodesics t (g • t),
  obtain ⟨n, hn⟩ := archimedean.arch L (div_pos bpos cpos),
  rw [nsmul_eq_mul] at hn,
  apply sm_aux cpos bpos hs f t ts n g L Lnonneg hn,
  exact ⟨g • t, smul_mem_smul_set ts, qif⟩,
end

/-- The marking corresponding to the setting of Švarc-Milnor. -/
def sm_marking (hs : translates_cover α s) :
  marking α $ proper_action_set α (set_closed_ball s (2 * b)) :=
{ to_fun_surjective := begin
    apply top_closure_to_surj_hom,
    rw subtype.range_coe,
    exact metric_svarcmilnor1 cpos bpos s hs,
  end,
  ..free_group.lift coe }

omit bpos cpos hβ

/-! ### Auxiliary lemmas about word metric -/

open classical geometric_group_theory

include bpos cpos hβ

/-- Generalisation of `sm_aux`: `g` is not only in the closure, but the word length is bounded by an
expression involving the length of the quasi-geodesic. -/
-- proof is very similar to `sm_aux` - can we do both in one?
lemma wm_aux (hs : translates_cover α s) (f : ℝ → β) (xs : x ∈ s) (n : ℕ) :
  ∀ (g : marked (sm_marking cpos bpos hs)) (L : ℝ) (Lnonneg : 0 ≤ L)
    (hL' : L ≤ (n : ℝ)*(b/c)),
      (∃ y ∈ g • s, quasigeodesic L f x y c b) → ∥g∥ ≤ n+1 :=
begin
  let m := marked (sm_marking cpos bpos hs),
  induction n with n hn,
  { rintro g L Lnonneg hL ⟨y, hy, qg⟩,
    simp only [algebra_map.coe_zero, zero_add, zero_mul] at ⊢ hL,
    obtain rfl : L = 0, from antisymm hL Lnonneg,
    obtain rfl : x = y := degenerate_quasigeodesic f x y c b ⟨qg.1, qg.2.1, by simp [bpos.le]⟩,
    refine gen_norm_le_one_sub ⟨x, _, _⟩; rw isom_of_set_closed_ball <|> skip;
    { apply self_set_closed_ball,
      positivity,
      assumption } },
  set L' : ℝ := n * (b / c) with hL',
  have L'nonneg : 0 ≤ L' := by { rw hL', positivity },
  rintro g L Lnonneg hL ⟨y, hy, qg⟩,
  obtain hL' | hL' := le_total L L',
  { have ng := hn g L Lnonneg hL' ⟨y, hy, qg⟩,
    rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one],
    linarith },
  have := qg.mono f hL',
  simp only [exists_prop, forall_exists_index, and_imp] at hn,
  rw [nat.succ_eq_one_add, nat.cast_add, nat.cast_one] at hL,
  obtain ⟨g', hg'⟩ : ∃ g' : m, _ := hs (f L'),
  have g'norm : ∥g'∥ ≤ n + 1 := hn g' L' L'nonneg le_rfl (f L') hg' this,
  have smalldistdom : |L' - L| ≤ b/c,
  { rwa [abs_sub_comm, abs_of_nonneg, sub_le_iff_le_add', ←one_mul (b/c), ←add_mul, add_comm],
    exact sub_nonneg_of_le ‹_› },
  have smalldistimg : dist (f L') (f L) ≤ 2*b,
  calc
    dist (f L') (f L) ≤ c * |L' - L| + b : (qg.2.2 ⟨L'nonneg, hL'⟩ ⟨Lnonneg, le_rfl⟩).2
    ...               ≤ c * (b/c) + b
                      : add_le_add_right (mul_le_mul_of_nonneg_left smalldistdom cpos.le) _
      ...               = 2 * b : by rw [mul_div_cancel' _ cpos.ne', two_mul],
  obtain ⟨k, hk, rfl⟩ : ∃ k ∈ proper_action_set α (set_closed_ball s (2 * b)), g' * k = g :=
    intS hg' (by rwa qg.2.1) smalldistimg,
  refine gen_set_mul_right'_sub hk _ _,
  rwa nat.cast_succ,
end

/-- Easier to apply version of `wm_aux`. -/
lemma word_metric_bound_of_quasigeodesic (Lnonneg : 0 ≤ L) {f : ℝ → β} (xs : x ∈ s)
  {hs : translates_cover α s} {g : marked (sm_marking cpos bpos hs)}
  (hf : quasigeodesic L f x (g • x) c b) {n : ℕ} (hL : L ≤ ↑n * (b / c)) :
  ∥g∥ ≤ n + 1 :=
wm_aux cpos bpos hs f xs n g L Lnonneg hL ⟨g • x, smul_mem_smul_set xs, hf⟩

/-- Generalisation of `proper_action_set_bound`: for a general group element, the expression is
bounded by the word length up to a constant. -/
lemma gen_bound (xs : x ∈ s) (hs : translates_cover α s) (finitediam : bounded s) :
  ∃ k, 0 < k ∧ ∀ g : marked (sm_marking cpos bpos hs), dist x (g • x) ≤ k * ∥g∥ :=
begin
  let m := marked (sm_marking cpos bpos hs),
  obtain ⟨k, kpos, hk⟩ := proper_action_set_bound α bpos.le finitediam xs,
  refine ⟨k, kpos, λ g, _⟩,
  obtain ⟨n, hn⟩ := exists_nat_ge (∥g∥),
  induction n with n ih generalizing g,
  { norm_cast at hn,
    have gd : ∥g∥ = 0, from hn.antisymm (norm_nonneg' _),
    rw [norm_eq_zero''] at gd,
    rw gd, simp },
  obtain rfl | gn := eq_or_ne g 1,
  { simp },

  -- construct a shorter word that is related to original word
  obtain ⟨y, ⟨t, ht1, rfl⟩, hy⟩ :
    ∃ y : m, (∃ t ∈ proper_action_set α (set_closed_ball s (2*b)), t * y = g) ∧ ∥y∥ = ∥g∥ - 1,
  { obtain ⟨y, hyor, hynorm⟩ := gen_div_left_sub g gn,
    refine ⟨y, _, hynorm⟩,
    obtain hyor | ⟨t, ht, ht'⟩ := hyor,
    { exact hyor },
    { exact ⟨t⁻¹, inv_mem_proper_action_set.2 ht, ht'⟩ } },

  -- apply induction hypothesis to this shorter word and get bound for original word
  refine (dist_triangle _ (t • x) _).trans _,
  rw [mul_smul, dist_smul_smul],
  have h : dist x (t • x) ≤ k := hk t ht1,
  rw [nat.cast_succ, ←sub_le_iff_le_add] at hn,
  have h2 : dist x (y • x) ≤ k * (∥t * y∥ - 1) := by { rw ←hy, exact ih y (hy.trans_le hn) },
  linarith,
end

theorem metric_svarcmilnor2 (xs : x ∈ s) (hs : translates_cover α s) (finitediam : bounded s) :
  is_QI (λ g : marked (sm_marking cpos bpos hs), g • x) :=
begin
  let m := marked (sm_marking cpos bpos hs),

  -- we know that quasi-isometry is equivalent to quasidense image and quasi-isometric embedding
  apply QIE_with_quasidense_image_is_QI,
  obtain ⟨k, kpos, hk⟩ := gen_bound cpos bpos xs hs finitediam,

  -- we set up relevant constants that will show up in calculations later
  refine QIE_from_different_constants _ k 1 (c ^ 2 / b) (b + 2 * (b / c ^ 2)) kpos zero_lt_one
    (by positivity) (by positivity) (λ g h, _) _,
  dsimp,
  rw [←dist_inv_smul_right, smul_smul],

  -- upper bound: follows from `gen_bound`
  calc
    dist x ((g⁻¹ * h) • x) ≤ k * ∥g⁻¹ * h∥ : hk (g⁻¹*h)
                       ... = k * dist g h : by rw dist_eq_norm_inv_mul
                       ... ≤ k * dist g h + 1 : by linarith,
  intros g h,
  simp only [one_div_div],
  obtain ⟨L, Lnonneg, f, f0, fL, hf⟩ : conn_by_quasigeodesic' x ((g⁻¹ * h) • x) c b,
    by apply quasigeodesic_space.quasigeodesics x (of_marked(g⁻¹ * h) • x),
  obtain ⟨n, L1, L2⟩ := arch'' (div_pos bpos cpos) Lnonneg,
  rw [←dist_inv_smul_right, smul_smul, inv_div],

  -- lower bound: follows from `word_metric_bound_of_quasigeodesic`
  calc
    dist x ((g⁻¹ * h) • x)
        = dist (f 0) (f L) : by rw [f0, fL]
    ... ≥ c⁻¹ * |0 - L| - b : (hf ⟨le_rfl, Lnonneg⟩ ⟨Lnonneg, le_rfl⟩).1
    ... = c⁻¹ * L - b : by rw [zero_sub, abs_neg, abs_of_nonneg Lnonneg]
    ... ≥ c⁻¹ * ((n - 1) * (b / c)) - b
        : sub_le_sub_right (mul_le_mul_of_nonneg_left L1 $ inv_nonneg.2 cpos.le) _
    ... = b / c ^ 2 * (n + 1) - (b + 2 * (b / c ^ 2)) : by { field_simp, ring_nf }
    ... ≥ b / c ^ 2 * ∥g⁻¹ * h∥ - (b + 2 * (b / c ^ 2))
      : sub_le_sub_right (mul_le_mul_of_nonneg_left (word_metric_bound_of_quasigeodesic
          cpos bpos Lnonneg xs ⟨f0, fL, hf⟩ L2.le) $ by positivity) _
    ... = b / c ^ 2 * dist g h - (b + 2 * (b / c ^ 2)) : by rw dist_eq_norm_inv_mul,
  exact svarcmilnor_qdense hs finitediam xs,
end

omit hβ bpos cpos

-- in the following we try and compute a specific example, namely that Z is quasi-isometric to R.

-- R is quasigeodesic (1,1), need both positive for theorem to apply

instance real.quasigeodesic_space : quasigeodesic_space ℝ 1 1 :=
{ quasigeodesics := begin
    suffices : ∀ x y : ℝ, x ≤ y → conn_by_quasigeodesic' x y 1 1,
    { rintro x y,
      obtain h | h := le_total x y,
      { exact this _ _ h },
      { exact (this _ _ h).symm } },
    refine λ x y h, ⟨y - x, sub_nonneg.2 h, (+) x, add_zero _, _⟩,
    simp only [add_sub_cancel'_right, eq_self_iff_true, mem_Icc, inv_one, one_mul, dist_add_left,
      tsub_le_iff_right, and_imp, true_and],
    intros m hm1 hm2 n hn1 hn2,
    split;
    { rw add_comm,
      apply le_add_of_nonneg_left,
      exact one_pos.le }
  end }

/-- Švarc-Milnor allows conclusion of quasi-isometry given a 'nice' action of the group.
   Here we have the translation action of `ℤ` on `ℝ`. -/
instance translation_action : iso_mul_action (multiplicative ℤ) ℝ :=
{ iso_smul := λ b x y, congr_arg coe $ by simp [←to_add_vadd] }

/-- One of the conditions of Švarc-Milnor for `s = [0,1]`. -/
theorem translates_cover_interval : translates_cover (multiplicative ℤ) (set.Icc (0 : ℝ) 1) :=
begin
  refine λ x, ⟨multiplicative.of_add ⌊x⌋, _⟩,
  sorry
end

def mult_Z_marking := sm_marking (zero_lt_one' ℝ) one_pos translates_cover_interval

/-- There exists a quasi-isometry from a (marking of) `ℤ` to `ℝ`, namely the inclusion. -/
theorem Z_qI_to_R : ∃ f : marked (mult_Z_marking) → ℝ, is_QI f :=
⟨λ n, n • 0, metric_svarcmilnor2 one_pos one_pos (left_mem_Icc.2 zero_le_one) _ $ bounded_Icc _ _⟩
