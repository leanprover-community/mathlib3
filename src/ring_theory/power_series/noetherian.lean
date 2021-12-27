import ring_theory.power_series.basic
import ring_theory.polynomial.basic
import topology.algebra.ordered.basic
import topology.algebra.valuation
import topology.algebra.nonarchimedean.adic_topology
import topology.metric_space.algebra
import topology.metric_space.hausdorff_distance
import linear_algebra.adic_completion
import data.real.nnreal


section power_series_coeff_lemmas
-- duplicate the api of data/polynomial/coeff.lean
open power_series finset
noncomputable theory

namespace power_series
variables {R : Type*} [ring R]
lemma coeff_C_mul_X (x : R) (k n : ℕ) :
  coeff R n (C R x * X ^ k : power_series R) = if n = k then x else 0 :=
by simp [X_pow_eq, coeff_monomial]

@[simp]
theorem coeff_mul_X_pow (p : power_series R) (n d : ℕ) :
  coeff R (d + n) (p * X ^ n) = coeff R d p :=
begin
  rw [coeff_mul, sum_eq_single (d,n), coeff_X_pow, if_pos rfl, mul_one],
  { rintros ⟨i,j⟩ h1 h2, rw [coeff_X_pow, if_neg, mul_zero], rintro rfl, apply h2,
    rw [nat.mem_antidiagonal, add_right_cancel_iff] at h1, subst h1 },
  { exact λ h1, (h1 (nat.mem_antidiagonal.2 rfl)).elim }
end

@[simp]
theorem coeff_X_pow_mul (p : power_series R) (n d : ℕ) :
  coeff R (d + n) (X ^ n * p) = coeff R d p :=
begin
  rw [coeff_mul, sum_eq_single (n,d), coeff_X_pow, if_pos rfl, one_mul],
  { rintros ⟨i,j⟩ h1 h2, rw [coeff_X_pow, if_neg, zero_mul], rintro rfl, apply h2,
    rw [nat.mem_antidiagonal, add_comm, add_right_cancel_iff] at h1, subst h1 },
  { rw add_comm,
    exact λ h1, (h1 (nat.mem_antidiagonal.2 rfl)).elim }
end

lemma coeff_mul_X_pow' (p : power_series R) (n d : ℕ) :
  coeff R d (p * X ^ n) = ite (n ≤ d) (coeff R (d - n) p) 0 :=
begin
  split_ifs,
  { rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right] },
  { refine (coeff_mul _ _ _).trans (finset.sum_eq_zero (λ x hx, _)),
    rw [coeff_X_pow, if_neg, mul_zero],
    exact ne_of_lt (lt_of_le_of_lt (nat.le_of_add_le_right
      (le_of_eq (finset.nat.mem_antidiagonal.mp hx))) (not_le.mp h)) },
end

lemma coeff_X_pow_mul' (p : power_series R) (n d : ℕ) :
  coeff R d (X ^ n * p) = ite (n ≤ d) (coeff R (d - n) p) 0 :=
begin
  split_ifs,
  { rw [← tsub_add_cancel_of_le h, coeff_X_pow_mul], simp, },
  { refine (coeff_mul _ _ _).trans (finset.sum_eq_zero (λ x hx, _)),
    rw [coeff_X_pow, if_neg, zero_mul],
    have := finset.nat.mem_antidiagonal.mp hx,
    rw add_comm at this,
    exact ne_of_lt (lt_of_le_of_lt (nat.le_of_add_le_right
      (le_of_eq this)) (not_le.mp h)) },
end

@[simp] theorem coeff_mul_X (p : power_series R) (n : ℕ) :
  coeff R (n + 1) (p * X) = coeff R n p :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp] theorem coeff_X_mul (p : power_series R) (n : ℕ) :
  coeff R (n + 1) (X * p) = coeff R n p :=
by simpa only [pow_one] using coeff_X_pow_mul p 1 n

end power_series
end power_series_coeff_lemmas
section adic_metric

namespace submodule
open submodule
open_locale pointwise
variables {R M : Type*} [comm_semiring R] [add_comm_group M] [module R M] (I : ideal R)

lemma mem_span_singleton_smul {y : R} {x : M} (N : submodule R M) :
  x ∈ ideal.span ({y} : set R) • N ↔ ∃ (n : M) (hn : n ∈ N), y • n = x :=
⟨λ hx, smul_induction_on hx
  (λ r hri n hnm,
    let ⟨s, hs⟩ := mem_span_singleton.1 hri in
 ⟨s • n, smul_mem N s hnm, by simp [← hs, mul_smul]; exact smul_comm _ _ _⟩)
  ⟨0, by simp, smul_zero _⟩
  (λ m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩,
    ⟨y1 + y2, add_mem N hyi1 hyi2, by rw [smul_add, hy1, hy2]⟩)
  (λ c r ⟨y, hyi, hy⟩, ⟨c • y, smul_mem N c hyi, by simp [← hy, mul_smul]; exact smul_comm _ _ _⟩),
λ ⟨y, hyi, hy⟩, hy ▸ smul_mem_smul (ideal.mem_span_singleton'.mpr ⟨1, by simp⟩) hyi⟩

end submodule
variables (R : Type*) [comm_ring R] (J : ideal (power_series R))
open power_series
-- TODO is there some generalization, ideals over Hausdorff rings are all haus etc
-- TODO restore original version for R
instance power_series.ideal.is_Hausdorff :
  is_Hausdorff (ideal.span ({X} : set (power_series R))) J :=
{ haus' := begin
  intros x h,
  ext n,
  specialize h (n + 1),
  rw [ideal.span_singleton_pow, smodeq.sub_mem] at h,
  simp at h,
  rw submodule.mem_span_singleton_smul at h,
  rcases h with ⟨⟨h_w_val, h_w_property⟩, ⟨⟩, rfl⟩,
  -- dsimp,
      -- ideal.mem_span_singleton, power_series.X_pow_dvd_iff, sub_zero] at h,
  simp,
  rw add_comm,
  rw coeff_X_pow_mul',
  simp,
end }
instance : is_precomplete (ideal.span ({X} : set (power_series R))) J :=
{ prec' := begin
  intros f h,
  use power_series.mk (λ n, coeff R n (f (n + 1))),
  intro n,
  rw [algebra.id.smul_eq_mul, ideal.mul_top, ideal.span_singleton_pow, smodeq.sub_mem,
    ideal.mem_span_singleton, power_series.X_pow_dvd_iff],
  simp only [coeff_mk, map_sub],
  intros m hmn,
  specialize h hmn,
  rw [algebra.id.smul_eq_mul, ideal.mul_top, ideal.span_singleton_pow, smodeq.sub_mem,
    ideal.mem_span_singleton, power_series.X_pow_dvd_iff] at h,
  specialize h m (nat.lt_succ_self _),
  rw [map_sub] at h,
  rw sub_eq_zero at h ⊢,
  symmetry,
  assumption,
end }
instance : is_adic_complete (ideal.span ({X} : set (power_series R))) (power_series R) :=
{ ..power_series.is_Hausdorff R,
  ..power_series.is_precomplete R }
variables {R} (I : ideal R)
noncomputable theory
def adic_valuation (x : R) : ℕ := Sup {n : ℕ | x ∈ I ^ n}
@[simp]
lemma adic_valuation_neg (x : R) : adic_valuation I (-x) = adic_valuation I x := by simp [adic_valuation]
open_locale classical

theorem Sup_of_not_bdd_above {s : set ℕ} (hs : ¬ bdd_above s) : Sup s = 0 := -- these are copied from lemmas about real should be generalized
dif_neg $ assume h, hs h
theorem nat.Sup_univ : Sup (@set.univ ℕ) = 0 :=
Sup_of_not_bdd_above $ λ ⟨x, h⟩, not_le_of_lt (lt_add_one _) $ h (set.mem_univ _)
@[simp]
lemma adic_valuation_zero : adic_valuation I 0 = 0 := by simp [adic_valuation]; exact nat.Sup_univ
@[simp]
lemma adic_valuation_one : adic_valuation I 1 = 0 := by simp [adic_valuation]; sorry --need I ≠ ⊤
@[simp]
lemma adic_valuation_mul (x y : R) : adic_valuation I (x * y) = adic_valuation I x + adic_valuation I y := sorry --needs some serious assumptions
lemma adic_valuation_add (x y : R) : adic_valuation I (x + y) ≤ adic_valuation I x + adic_valuation I y :=
sorry
-- instance : has_pow ℝ enat := ⟨λ r e, if h : e = ⊤ then 0 else r ^ (e.get (by {cases e, simp at *, }))⟩
open_locale nnreal
def adic_norm (x : R) : ℝ≥0 := if ∀ n : ℕ, x ∈ I ^ n then 0 else (1 / 2) ^ adic_valuation I x
@[simp]
lemma adic_norm_neg (x : R) : adic_norm I (-x) = adic_norm I x := by simp [adic_norm]
@[simp]
lemma adic_norm_zero : adic_norm I 0 = 0 := by simp [adic_norm]
@[simp]
lemma adic_norm_one (h : I ≠ ⊤) : adic_norm I 1 = 1 :=
begin
  simp only [adic_norm, adic_valuation_one, ite_eq_right_iff, zero_ne_one, pow_zero],
  intro hh,
  simpa [← ideal.eq_top_iff_one] using hh 1,
end
lemma adic_norm_add (x y : R) : adic_norm I (x + y) ≤ max (adic_norm I x) (adic_norm I y) :=
sorry
@[simp]
lemma adic_norm_mul (hI : I.is_prime) (x y : R) : adic_norm I (x * y) = adic_norm I x * adic_norm I y :=
begin
  simp [adic_norm, adic_valuation_mul, pow_add],
  -- simp_rw [hI.mul_mem_iff_mem_or_mem],
  by_cases hx : ∀ (n : ℕ), x ∈ I ^ n,
  { rw [if_pos (λ n, ideal.mul_mem_right _ _ (hx n)), if_pos hx], },
  rw if_neg hx,
  by_cases hy : ∀ (n : ℕ), y ∈ I ^ n,
  { rw [if_pos (λ n, ideal.mul_mem_left _ _ (hy n)), if_pos hy], },
  rw if_neg hy,
  rw if_neg,
  intro hh,
  specialize hh 1,
  simp [hI.mul_mem_iff_mem_or_mem] at hh,
  classical,
  simp at *,
  cases hh,
  { obtain ⟨n, hn⟩ := hx, },
  obtain ⟨m, hm⟩ := hy,
  -- split_ifs; simp [*] at *,
end
def adic.valuation [is_domain R] (hI : I.is_prime) : valuation R ℝ≥0 :=
{ to_fun := adic_norm I,
  map_zero' := adic_norm_zero I,
  map_one' := adic_norm_one I hI.ne_top,
  map_mul' := adic_norm_mul I hI,
  map_add' := adic_norm_add I }
--   synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
--   conditionally_complete_linear_order.to_linear_order ℝ≥0
-- inferred
--   linear_ordered_comm_monoid.to_linear_order ℝ≥0
-- state:
-- TODO krull intersection
/--
Being an actual metric space means Krull's intersection theorem holds?
-/
def valuation_metric (v : valuation R ℝ≥0) : pseudo_metric_space R :=
{ dist := λ x y, v (x - y),
  dist_self := λ x, by simp,
  dist_comm := λ x y, by simp [← neg_sub x y, -neg_sub],
  dist_triangle := λ x y z, begin
    dsimp,
    rw (by abel : x - z = x - y + (y - z)),
    refine le_trans (v.map_add (x - y) (y - z)) _,
    dsimp,
    norm_cast,
    convert max_le_add_of_nonneg _ _,
    apply_instance,
    apply_instance,
    exact zero_le (v (x - y)),
    exact zero_le (v (y - z)),
  end,
  -- TODO make the uniform space structure agree with existing
  -- eq_of_dist_eq_zero := λ x y, by simp,
  -- uniformity_dist := sorry,
  -- ..valued.uniform_space
  }
-- lemma adic_basis (I : ideal R) : submodules_ring_basis (λ n : ℕ, (I^n • ⊤ : ideal R)) :=
-- (adic_basis I).topology

end adic_metric
variables {R : Type*} [comm_ring R]
#check ideal.leading_coeff_nth

#check power_series.le_order

#check ideal.degree_le
open power_series
def of_power_series (I : ideal (power_series R)) : submodule R (power_series R) :=
{ carrier := I.carrier,
  zero_mem' := I.zero_mem,
  add_mem' := λ _ _, I.add_mem,
  smul_mem' := λ c x H, by { simp [set_like.mem_coe, submodule.mem_carrier],
  exact submodule.smul_of_tower_mem I c H, } }

noncomputable theory
open_locale classical
namespace power_series
/-- The `R`-submodule of `R[[X]]` consisting of power series of order ≥ `n`. -/
def submodule_le_order (R : Type*) [comm_ring R] (n : with_bot ℕ) : submodule R (power_series R) :=
⨅ k : ℕ, ⨅ h : ↑k < n, (coeff R k).ker

def order_coeff (p : power_series R) : R := coeff R ((order p).get_or_else 0) p
lemma order_coeff_mul_X_pow (p : power_series R) (n : ℕ) :
  order_coeff (p * X ^ n) = order_coeff p := by sorry; simp [order_coeff]
end power_series
namespace ideal
open power_series

variables (I : ideal (power_series R))
/-- Given an ideal `I` of `R[[X]]`, make the `R`-submodule of `I`
consisting of power series of order ≥ `n`. -/
def le_order (n : with_bot ℕ) :
  submodule R (power_series R) :=
submodule_le_order R n ⊓ of_power_series I

/-- Given an ideal `I` of `R[[X]]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with order ≥ `n`. -/
def order_coeff_nth (n : ℕ) : ideal R :=
(I.le_order n).map $ coeff R n

theorem mem_le_order {n : with_bot ℕ} {f : power_series R} :
  f ∈ submodule_le_order R n ↔ ↑(n.get_or_else 0) ≤ order f :=
begin
  cases n,
  { simp [submodule_le_order, with_bot.not_lt_none], },
  simp [submodule_le_order, nat_le_order],
  split; intro h,
  apply nat_le_order,
  intros,
  apply h,
  exact with_bot.coe_lt_coe.mpr H,
  intros m hm,
  -- erw with_bot.coe_lt_coe at hm,
  apply coeff_of_lt_order,
  apply lt_of_lt_of_le _ h,
  erw with_bot.coe_lt_coe at hm,
  rw enat.coe_lt_coe,
  exact hm,
end

theorem mem_order_coeff_nth (n : ℕ) (x) :
  x ∈ I.order_coeff_nth n ↔ ∃ p ∈ I, ↑n ≤ order p ∧ order_coeff p = x :=
begin
  simp [order_coeff_nth, le_order, submodule.mem_map, submodule.mem_inf,
    mem_le_order, order_zero],
  split,
  { rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    cases lt_or_eq_of_le hpdeg with hpdeg hpdeg,
    sorry;{ refine ⟨0, I.zero_mem, bot_le, _⟩,
      rw [leading_coeff_zero, eq_comm],
      exact coeff_eq_zero_of_degree_lt hpdeg },
    { refine ⟨p, hpI, le_of_eq hpdeg, _⟩,
      rw [order_coeff], simp [hpdeg], congr, rw ← hpdeg, sorry, } },
      sorry,
  -- { rintro ⟨p, hpI, hpdeg, rfl⟩,
    -- have : order p + (↑n - order p) = n,
    -- { exact add_tsub_cancel_of_le (nat_degree_le_of_degree_le hpdeg) },
    -- refine ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right _ hpI⟩, _⟩,
    -- { apply le_trans (degree_mul_le _ _) _,
    --   apply le_trans (add_le_add (degree_le_nat_degree) (degree_X_pow_le _)) _,
    --   rw [← with_bot.coe_add, this],
    --   exact le_refl _ },
    -- { rw [leading_coeff, ← coeff_mul_X_pow p (n - nat_degree p), this] } }
end

theorem order_coeff_nth_mono {m n : ℕ} (H : m ≤ n) :
  I.order_coeff_nth m ≤ I.order_coeff_nth n :=
begin
  nontriviality R,
  intros r hr,
  simp only [set_like.mem_coe, mem_order_coeff_nth] at hr ⊢,
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩,
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, _, order_coeff_mul_X_pow _ _⟩,
  refine le_trans _ (order_mul_ge _ _),
  rw order_X_pow,
  norm_cast,
  sorry,
  -- rw order_mul_ge,
  -- refine le_trans (order_mul _ _) _,
  -- refine le_trans (add_le_add hpdeg (degree_X_pow_le _)) _,
  -- rw [← with_bot.coe_add, add_tsub_cancel_of_le H],
  -- exact le_refl _
end

end ideal

namespace power_series
open_locale big_operators

#check metric_space
#check emetric.mem_iff_inf_edist_zero_of_closed
#check ideal.adic_topology

/-- Hilbert basis theoremish: a power series ring over a noetherian ring is a noetherian ring. -/
protected theorem power_series.is_noetherian_ring [is_noetherian_ring R] :
  is_noetherian_ring (power_series R) :=
is_noetherian_ring_iff.2 ⟨assume I : ideal (power_series R),
let M := well_founded.min (is_noetherian_iff_well_founded.1 (by apply_instance))
  (set.range I.order_coeff_nth) ⟨_, ⟨0, rfl⟩⟩ in
have hm : M ∈ set.range I.order_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm in
-- λ k, or.cases_on (le_or_lt k N)
-- or.cases_on (le_or_lt k N)
--   (λ h, HN ▸ I.leading_coeff_nth_mono h)
--   (λ h x hx, classical.by_contradiction $ λ hxm,
--     have ¬M < I.leading_coeff_nth k, by refine well_founded.not_lt_min
--       (well_founded_submodule_gt _ _) _ _ _; exact ⟨k, rfl⟩,
--     this ⟨HN ▸ I.leading_coeff_nth_mono (le_of_lt h), λ H, hxm (H hx)⟩),
-- have hs2 : ∀ {x}, x ∈ I.degree_le N → x ∈ ideal.span (↑s : set (polynomial R)),
-- from hs ▸ λ x hx, submodule.span_induction hx (λ _ hx, ideal.subset_span hx) (ideal.zero_mem _)
--   (λ _ _, ideal.add_mem _) (λ c f hf, f.C_mul' c ▸ ideal.mul_mem_left _ _ hf),
-- ⟨s, le_antisymm
--   (ideal.span_le.2 $ λ x hx, have x ∈ I.degree_le N, from hs ▸ submodule.subset_span hx, this.2) $
begin
  have : ∀ t, (I.order_coeff_nth t).fg :=
    λ t, (is_noetherian_ring_iff_ideal_fg R).mp ‹_› (I.order_coeff_nth t),
  let s' : ℕ → finset R := λ d, classical.some (this d),
  have : ∀ (d) (a : s' d), ∃ fa : power_series R, fa ∈ I.le_order ↑d ∧ coeff R d fa = a,
  { rintros d ⟨a, ha⟩,
    simp only [s'] at ha,
    generalize_proofs hh at ha,
    have : a ∈ I.order_coeff_nth d,
    { rw ← classical.some_spec hh,
      exact ideal.subset_span (finset.mem_coe.mpr ha), },
    rw [ideal.order_coeff_nth, submodule.mem_map] at this,
    simpa, },
  let s'' : Π d (a : s' d), power_series R := λ d a, classical.some (this d a),
  let s := (finset.range N).bUnion (λ d, (s' d).attach.image (s'' d)),
  refine ⟨s, le_antisymm _ _⟩,
  { erw ideal.span_le,
    simp only [s'', set.image_subset_iff, finset.coe_bUnion, set.Union_subset_iff,
      finset.mem_range, finset.mem_coe, finset.coe_image],
    intros i hi x hx,
    simp only [set.mem_preimage, set_like.mem_coe],
    generalize_proofs hh,
    have := classical.some_spec hh,
    simp only [ideal.le_order, of_power_series, submodule.mem_inf, set_like.mem_coe,
      submodule.mem_mk, submodule.mem_carrier] at this,
    convert this.1.2, },
  have : submodule.span (power_series R) ↑s = ideal.span ↑s, by refl,
  rw this,
  intros p hp,
  have : ∀ (g : I), ∃ (t : power_series R)
    (ht : t ∈ ideal.span (↑s : set (power_series R))),
    t.order_coeff = g.val.order_coeff ∧ t.order = g.val.order,
  sorry,
  let f₀ : I := 0,
  -- recursively define the element of I
  let f : ℕ → I := λ n, @nat.rec_on
    (λ _, I) n f₀
    (λ d fd, ⟨classical.some (this fd), _⟩),

  -- take the limit
  obtain ⟨(L : power_series R), hL⟩ :=
    (infer_instance : is_precomplete (ideal.span ({X} : set (power_series R))) _).prec _,
  -- letI := valuation_metric (adic.valuation I),
  -- rw emetric.mem_iff_inf_edist_zero_of_closed,
  -- by_contra hf,
  -- let T := {n | ∃ f ∈ ideal.span (↑s : set (power_series R)), p - f ∈ I ∧ order (p - f) = n},
  -- have : T.nonempty,
  -- { simp only [T, set.nonempty, exists_prop, finset.coe_bUnion,
  --     set.mem_set_of_eq, finset.mem_range, finset.mem_coe, finset.coe_image],
  --   refine ⟨_, 0, by simp, by simp [hp], rfl⟩, },

  -- have Sup_mem : Sup T ∈ T,
  -- { letI : topological_space enat := preorder.topology _,
  --   -- haveI : discrete_topology enat := ⟨rfl⟩,
  --   haveI : order_topology enat := ⟨rfl⟩,
  --   have := cSup_mem_closure this ⟨⊤, λ a ha, le_top⟩,
  --   rwa closure_eq_iff_is_closed.mpr _ at this,
  --   haveI : discrete_topology enat := singletons_open_iff_discrete.mp (λ a, _),
  --   -- TODO I-adic topology as a metric?
  --    },
  -- have sup_top : Sup T = ⊤,
  -- { apply (eq_top_or_lt_top (Sup T)).resolve_right,
  --   intro htt,
  --   have := enat.ne_top_of_lt htt,
  --   rw enat.ne_top_iff at this,
  --   rcases this with ⟨this_w, this_h⟩,
  --   simp only [exists_prop, finset.coe_bUnion, set.mem_set_of_eq,
  --     finset.mem_range, finset.mem_coe, finset.coe_image],
  --   intros b hb,
  --   rw [lt_top_iff_ne_top, enat.ne_top_iff] at hb,
  --   rcases hb with ⟨n, rfl⟩,
  --   sorry, },
  rw [sup_top, set.mem_def] at this,
  rcases this with ⟨f, hps, hpf, opf⟩,
  simp only [sub_eq_zero, order_eq_top] at opf,
  rw opf at hf,
  contradiction,
end⟩

attribute [instance] power_series.is_noetherian_ring
end power_series

#lint
