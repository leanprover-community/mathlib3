
import measure_theory.measure.measure_space
import analysis.asymptotics.asymptotics
import data.complex.exponential
import data.finset.basic
import data.nat.prime
import data.zmod.basic
import taoziegler.tomathlib.indicator
import taoziegler.tomathlib.multiset
import taoziegler.tomathlib.infinite_prod_real

open_locale topology ennreal measure_theory
open filter asymptotics
open_locale topology

open measure_theory

def distinct_residue_classes (p : ℕ) (d : finset ℕ) : ℕ :=
  finset.card (d.image (λ n : ℕ, (n : zmod p)))

notation `ν ` := distinct_residue_classes

-- Gallagher Theorem 1

/-- $P_k(h, N)$, the number of integers `n ≤ N` for which the interval $(n, n + h)$ contains
exactly `k` primes. -/
def card_intervals_of_card_eq (h N : ℕ) : ℕ := finset.card
  (((finset.range (N + 1)).image (λ n, finset.Ioc n (n + h))).filter (λ s, ∀ x ∈ s, nat.prime x))


-- Proof of (3)

variables (p : ℕ) (d : finset ℕ)

def prod_differences : ℕ :=
  finset.prod ((finset.image (λ pq : ℕ × ℕ, pq.2 - pq.1) (finset.product d d)).filter (≠ 0)) id

lemma distinct_residue_classes_pos (hd : d.nonempty) : 0 < ν p d :=
by rwa [distinct_residue_classes, finset.card_pos, finset.nonempty.image_iff]

lemma distinct_residue_classes_le_card : ν p d ≤ d.card := finset.card_image_le

lemma distinct_residue_classes_le_base (hp : p ≠ 0) : ν p d ≤ p :=
begin
  haveI : fintype (zmod p) := @zmod.fintype p ⟨hp⟩,
  rw distinct_residue_classes,
  nth_rewrite_rhs 0 ←zmod.card p,
  exact finset.card_le_univ _
end

lemma distinct_residue_classes_eq_card (h : ¬ p ∣ prod_differences d) :
  ν p d = d.card :=
begin
  rw [distinct_residue_classes],
  rcases (nat.zero_le p).eq_or_lt with rfl|hp,
  { refine finset.card_image_of_inj_on _,
    refine function.injective.inj_on _ _,
    exact nat.cast_injective },
  contrapose! h,
  replace h := lt_of_le_of_ne finset.card_image_le h,
  obtain ⟨x, hx, y, hy, hne, hxy⟩ : ∃ (x ∈ d) (y ∈ d), x ≠ y ∧ (x : zmod p) = y,
  { exact finset.exists_ne_map_eq_of_card_lt_of_maps_to h (λ _, finset.mem_image_of_mem _) },
  rw prod_differences,
  wlog hlt : x < y := hne.lt_or_lt using [x y, y x],
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, y = x + n * p,
  { refine ⟨(y - x) / p, _⟩,
    rw zmod.nat_coe_eq_nat_coe_iff' at hxy,
    rw [nat.div_mul_cancel, nat.add_sub_of_le hlt.le],
    refine nat.dvd_of_mod_eq_zero _,
    exact nat.sub_mod_eq_zero_of_mod_eq hxy.symm },
  have npos : 0 < n,
  { contrapose! hlt,
    rw [le_zero_iff] at hlt,
    simp [hlt] },
  refine (dvd_mul_left p n).trans (finset.dvd_prod_of_mem _ _),
  simp only [ne.def, finset.mem_filter, finset.mem_image, finset.mem_product, exists_prop,
             prod.exists, nat.mul_eq_zero, not_or_distrib],
  exact ⟨⟨x, _, ⟨hx, hy⟩, nat.add_sub_cancel_left _ _⟩, npos.ne', hp.ne'⟩
end

-- Reference for name is https://kskedlaya.org/18.785/k-tuples.pdf
noncomputable def singular_series : ℝ := ∏' p : {p : ℕ | nat.prime p},
 (λ p : ℕ, (p : ℝ) ^ (d.card - 1 : ℤ) * (p - ν p d) / (p - 1) ^ d.card) p

lemma proddable_singular_series : proddable (λ p : {p : ℕ | nat.prime p},
 (λ p : ℕ, (p : ℝ) ^ (d.card - 1 : ℤ) * (p - ν p d) / (p - 1) ^ d.card) p) :=
begin
  by_cases hp : ∃ p : {p : ℕ | p.prime}, ν p d = p,
  { obtain ⟨p, hp⟩ := hp,
    have pnonneg : (p : ℝ) ≠ 0 := sorry,
    refine proddable_of_zero _ ⟨p, _⟩,
    simp [hp, pnonneg] },
  have : (λ p : {p : ℕ | nat.prime p},
      (λ p : ℕ, (p : ℝ) ^ (d.card - 1 : ℤ) * (p - ν p d) / (p - 1) ^ d.card) p) =
    λ p : {p : ℕ | nat.prime p}, (λ p : ℕ, (1 : ℝ) + (p ^ d.card - ν p d *
      p ^ (d.card - 1 : ℤ) - (p - 1) ^ d.card) / (p - 1) ^ d.card) p,
  sorry { ext p,
    have : ((p : ℝ) - 1) ^ d.card ≠ 0,
    { cases d.card.zero_le.eq_or_lt with hd hd,
      { simp [hd.symm] },
      { rw [pow_ne_zero_iff hd],
        { simp [sub_eq_zero, p.prop.one_lt.ne'] },
        { apply_instance } } },
    have ppos : (0 : ℝ) < (p : ℕ) := sorry,
    field_simp [this, mul_sub, ←zpow_add_one₀ ppos.ne', mul_comm (ν p d : ℝ)] },
  rw this, clear this,
  refine proddable_one_add_of_summable _ _ _,
  sorry { }, -- this is currently unprovable, shouldn't need such strict constraint
  { sorry },
end
#exit
-- lemma proddable_singular_series : proddable (set.mul_indicator {p : ℕ | p.prime}
--   (λ p : ℕ, (p : ℝ) ^ (d.card - 1 : ℤ) * (p - ν p d) / (p - 1) ^ d.card)) :=
-- begin
--   by_cases hp : ∃ p ∈ {p : ℕ | p.prime}, ν p d = p,
--   sorry { obtain ⟨p', hp, hp'⟩ := hp,
--     simp only [set.mem_set_of_eq] at hp,
--     have pnonneg : (p' : ℝ) ≠ 0 := sorry,
--     refine proddable_of_zero _ ⟨p', _⟩,
--     simp [set.mul_indicator_apply, hp, hp', pnonneg] },
--   -- can't use proddable_one_add_of_summable yet because we still can hit zero in the indicator
--   push_neg at hp,
--   replace hp : ∀ p ∈ {p : ℕ | p.prime}, ν p d < p := λ p H,
--     lt_of_le_of_ne (distinct_residue_classes_le_base _ _ H.ne_zero) (hp p H),
--   refine proddable_of_summable_log _ _ _,
--   sorry { intro p',
--     simp only [set.mul_indicator_apply, one_div, zpow_neg, zpow_coe_nat, set.mem_set_of_eq],
--     split_ifs,
--     { have ppos : 0 < (p' : ℝ) := sorry,
--       refine mul_pos _ _,
--       { simp [sub_pos, div_lt_iff ppos, hp p' h] },
--       { suffices : 0 < 1 - (p' : ℝ)⁻¹,
--         { positivity },
--         rw [sub_pos, inv_lt ppos zero_lt_one],
--         simp [nat.prime.one_lt h] } },
--     { exact zero_lt_one } },
--   { have : set.mul_indicator {p : ℕ | nat.prime p}
--       (λ p : ℕ, (p : ℝ) ^ (d.card - 1 : ℤ) * (p - ν p d) / (p - 1) ^ d.card) =
--       set.mul_indicator {p : ℕ | nat.prime p} (λ p : ℕ,
--         1 + (p ^ d.card - ν p d * p ^ (d.card - 1 : ℤ) - (p - 1) ^ d.card) / (p - 1) ^ d.card),
--     { ext p,
--       simp_rw [set.mul_indicator_apply],
--       split_ifs with h,
--       sorry { have ppos : 0 < (p : ℝ) := sorry,
--         have : ((p : ℝ) - 1) ^ d.card ≠ 0,
--         { cases d.card.zero_le.eq_or_lt with hd hd,
--           { simp [hd.symm] },
--           { rw [pow_ne_zero_iff hd],
--             { simp [sub_eq_zero, h.one_lt.ne'] },
--             { apply_instance } } },
--         field_simp [this, mul_sub, ←zpow_add_one₀ ppos.ne', mul_comm (ν p d : ℝ)] },
--       { refl } },
--     rw this, clear this,
--     have: ∀ (f : ℕ → ℝ) (s : set ℕ), real.log ∘ set.mul_indicator s f =
--       set.indicator s (real.log ∘ f),
--     sorry { intros,
--       ext,
--       classical,
--       simp only [set.mul_indicator_apply, set.indicator_apply, function.comp_app],
--       split_ifs;
--       simp },
--     rw this, clear this,
--     refine summable.indicator _ _,
--     have : (real.log ∘ λ (p : ℕ), (1 : ℝ) + (↑p ^ d.card - ↑(ν p d) *
--         ↑p ^ (↑(d.card) - 1 : ℤ) - (↑p - 1) ^ d.card) / (↑p - 1) ^ d.card) =
--       λ (p : ℕ), real.log (1 + (λ p : ℕ, ((↑p : ℝ) ^ d.card - ↑(ν p d) *
--         ↑p ^ (↑(d.card) - 1 : ℤ) - (↑p - 1) ^ d.card) / (↑p - 1) ^ d.card) p),
--     { ext, simp, },
--     rw this, clear this,
--     refine summable_log_one_add_of_summable _ _ _,
--     { intro i,
--       simp only,
--       rcases i with _|_|i,
--       simp,
--       simp,
--       -- simp only,
--       -- simp,
--       -- simp only [one_div, sub_nonneg],
--       -- rw le_div_iff,
--     },
--       },
-- end
