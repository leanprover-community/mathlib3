/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import analysis.bounded_variation
import topology.path_connected
/-!

# Arclength

The `arclength` of `f` between `a` and `b` is the `evariation_on` of `f` on `Icc a b`.
Various forms of continuity of `arclength` (for either `a` or `b` fixed) are proven.

-/

open_locale ennreal big_operators
noncomputable theory

variables {α E : Type*} [linear_order α] [pseudo_emetric_space E] (f : α → E) {a b c : α}

/--
The length of the arc of the curve `f : α → E` between two points `a` and `b`, defined as
the variation of `f` on the closed interval `[a, b]`. Equals zero when `b ≤ a`.
-/
def arclength (a b : α) : ℝ≥0∞ := evariation_on f (set.Icc a b)

/--
`arclength f a b` is the supremum of finite sums of `edist (f $ u i) (f $ u $ i+1)` for `u`
satisfying the same conditions as for `evariation_on` with the addition of:

* `u 0` is `a`.
* `u 1` is **not** `a`.

-/
lemma arclength_eq_supr (hab : a ≤ b) : arclength f a b =
  ⨆ (p : ℕ × {u : ℕ → α // monotone u ∧ (∀ i, u i ∈ set.Icc a b) ∧ u 0 = a ∧ a < u 1}),
    ∑ i in finset.range p.1.succ, edist (f $ p.2.1 (i+1)) (f $ p.2.1 i) :=
    /- using coercion `p.2 : ℕ → α` makes things a lot slower, strangely -/
begin
  refine le_antisymm (supr_le _)
    (supr_le $ λ p, le_supr_of_le ⟨p.1.succ, p.2.1, p.2.2.1, p.2.2.2.1⟩ le_rfl),
  rintro ⟨n, u, hu, huab⟩,
  by_cases h : ∀ m ≤ n, u m = a,
  { convert zero_le _, refine finset.sum_eq_zero (λ m hm, _),
    rw finset.mem_range at hm,
    simp only [subtype.coe_mk, h _ hm.le, h _ hm, edist_self] },
  push_neg at h,
  obtain ⟨m, ⟨hmn, hma⟩, hmin⟩ := nat.well_founded_lt.wf.has_min _ h,
  cases m,
  { refine le_supr_of_le ⟨n, _, monotone_nat_of_le_succ $ λ k, _, λ k, _, _⟩ _,
    { apply nat.rec, exacts [a, λ k _, u k] },
    { cases k, exacts [(huab 0).1, hu k.le_succ] },
    { cases k, exacts [set.left_mem_Icc.2 hab, huab k] },
    { exact ⟨rfl, (huab 0).1.lt_of_ne' hma⟩ },
    { rw [finset.sum_range_succ'], exact self_le_add_right _ _ } },
  have : ∀ k ≤ m, u k = a,
  { intros k hk, contrapose! hmin,
    exact ⟨_, ⟨hk.trans (m.le_succ.trans hmn), hmin⟩, hk.trans_lt m.lt_succ_self⟩ },
  refine le_supr_of_le ⟨(n - m).pred, λ k, u (m + k), hu.comp $ λ _ _ h, add_le_add_left h _,
    λ k, huab _, this m le_rfl, (huab _).1.lt_of_ne' hma⟩ _,
  dsimp only [subtype.coe_mk],
  conv_lhs { rw [← nat.sub_add_cancel (m.le_succ.trans hmn), add_comm, finset.sum_range_add] },
  simp_rw [add_assoc, nat.succ_pred_eq_of_pos (nat.sub_pos_of_lt hmn)],
  convert (zero_add _).le,
  refine finset.sum_eq_zero (λ k hk, _),
  rw finset.mem_range at hk,
  rw [this _ hk.le, this _ hk, edist_self],
end

lemma edist_le_arclength (hab : a ≤ b) : edist (f a) (f b) ≤ arclength f a b :=
evariation_on.edist_le f (set.left_mem_Icc.2 hab) (set.right_mem_Icc.2 hab)

lemma arclength_eq_zero (hab : b ≤ a) : arclength f a b = 0 :=
evariation_on.subsingleton f $
  λ x hx y hy, (hx.2.trans $ hab.trans hy.1).antisymm (hy.2.trans $ hab.trans hx.1)

lemma arclength_self (a : α) : arclength f a a = 0 := arclength_eq_zero f le_rfl

lemma arclength_anti (c : α) : antitone (λ x, arclength f x c) :=
λ a b hab, evariation_on.mono f $ λ x h, ⟨hab.trans h.1, h.2⟩

lemma arclength_mono (a : α) : monotone (arclength f a) :=
λ b c hbc, evariation_on.mono f $ λ x h, ⟨h.1, h.2.trans hbc⟩

lemma arclength_add (hab : a ≤ b) (hbc : b ≤ c) :
  arclength f a b + arclength f b c = arclength f a c :=
begin
  simp_rw arclength,
  convert evariation_on.Icc_add_Icc f hab hbc (set.mem_univ _); rw set.univ_inter,
end

lemma arclength_sum {n : ℕ} {u : ℕ → α} (hu : monotone u) :
  (finset.range n).sum (λ i, arclength f (u i) (u (i + 1))) = arclength f (u 0) (u n) :=
begin
  induction n with n ih,
  { rw [finset.sum_range_zero, arclength_self] },
  { rw [finset.sum_range_succ, ih, arclength_add f (hu $ zero_le n) (hu n.le_succ)] },
end

lemma arclength_sub₀ (hba : b ≤ a) : arclength f a b = arclength f a c - arclength f b c :=
by { rw [arclength_eq_zero f hba, eq_comm], exact tsub_eq_zero_of_le (arclength_anti f c hba) }

lemma arclength_sub' (hbc : b ≤ c) (hac : arclength f b c ≠ ⊤) :
  arclength f a b = arclength f a c - arclength f b c :=
(le_total a b).elim
  (λ hab, ennreal.eq_sub_of_add_eq hac $ arclength_add f hab hbc)
  (arclength_sub₀ f)

lemma arclength_sub (hbc : b ≤ c) (hac : arclength f a c ≠ ⊤) :
  arclength f a b = arclength f a c - arclength f b c :=
(le_total a b).elim
  (λ hab, arclength_sub' f hbc $ ne_top_of_le_ne_top hac $ arclength_anti f c hab)
  (arclength_sub₀ f)

open order_dual

lemma arclength_comp_of_dual (a b : α) :
   arclength (f ∘ of_dual) (to_dual b) (to_dual a) = arclength f a b :=
begin
  rw arclength,
  convert evariation_on.comp_of_dual f (set.Icc a b) using 2,
  ext, apply and_comm,
end

lemma arclength'_eq (b : α) :
  (λ x, arclength f x b) = arclength (f ∘ of_dual) (to_dual b) ∘ to_dual :=
funext $ λ a, (arclength_comp_of_dual f a b).symm

lemma arclength_Icc_extend (h : a ≤ b) (f : set.Icc a b → E) :
  arclength (set.Icc_extend h f) a b = evariation_on f set.univ :=
evariation_on.comp_eq_of_monotone_on _ _
  ((set.monotone_proj_Icc _).monotone_on _) (set.maps_to_univ _ _) (set.proj_Icc_surj_on h)

section
/-!
### Continuity (in various forms) "around" a point.
-/

variables [topological_space α]

lemma continuous_on_Iic_arclength_of_ge (h : b ≤ a) :
  continuous_on (arclength f a) (set.Iic b) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans hx h)

lemma continuous_on_Ici_arclength'_of_ge (h : b ≤ a) :
  continuous_on (λ x, arclength f x b) (set.Ici a) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans h hx)

variables [order_topology α]

lemma continuous_at_arclength_of_gt (h : b < a) : continuous_at (arclength f a) b :=
continuous_at_const.congr $ set.eq_on.eventually_eq_of_mem
  (λ x hx, (arclength_eq_zero f (set.mem_Iio.1 hx).le).symm) $ Iio_mem_nhds h

lemma continuous_at_arclength'_of_gt (h : b < a) : continuous_at (λ x, arclength f x b) a :=
continuous_at_const.congr $ set.eq_on.eventually_eq_of_mem
  (λ x hx, (arclength_eq_zero f (set.mem_Ioi.1 hx).le).symm) $ Ioi_mem_nhds h

variables (hab : a < b) (hrect : arclength f a b ≠ ⊤) /- f is rectifiable on [a,b] -/
include hab hrect

theorem continuous_right_self_arclength
  (hcont : continuous_within_at f (set.Ico a b) a) /- f is right continuous at a -/ :
  continuous_within_at (arclength f a) (set.Ici a) a :=
begin
  replace hcont := hcont.mono_of_mem (mem_nhds_within.2 ⟨_, is_open_Iio, hab, λ x, and.symm⟩),
  rw [continuous_within_at, arclength_self, ennreal.tendsto_nhds_zero],
  intros ε hε,
  by_cases hlab : arclength f a b = 0,
  { rw eventually_nhds_within_iff,
    refine filter.eventually_of_mem (Iio_mem_nhds hab) (λ x hb ha, _),
    exact ((arclength_mono f a $ le_of_lt hb).trans_eq hlab).trans (zero_le ε) },
  have hε2 : 0 < ε / 2 := ennreal.half_pos (ne_of_gt hε),
  rw arclength_eq_supr f hab.le at hrect hlab,
  obtain ⟨⟨n, u, hu, hmem, hea, hal⟩, hl⟩ := lt_supr_iff.1 (ennreal.sub_lt_self hrect hlab hε2.ne'),
  simp_rw [← arclength_eq_supr f hab.le, edist_comm] at hl,
  obtain ⟨c, hc, hcb⟩ := (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hab).1
    ((emetric.nhds_basis_eball.tendsto_right_iff).1 hcont _ hε2),
  apply (mem_nhds_within_Ici_iff_exists_mem_Ioc_Ico_subset hab).2,
  by_cases ∀ x, ¬ x ∈ set.Ioo a c,
  { refine ⟨c, hc, λ x hx, _⟩,
    obtain rfl | hxa := eq_or_ne a x,
    exacts [(arclength_self f a).trans_le (zero_le ε), (h x ⟨hx.1.lt_of_ne hxa, hx.2⟩).elim] },
  push_neg at h, obtain ⟨d, hd⟩ := h,
  let e := min (u 1) d,
  have hae : a < e := lt_min hal hd.1,
  have hec : e < c := (min_le_right _ d).trans_lt hd.2,
  refine ⟨e, ⟨hae, hec.le.trans hc.2⟩, λ x hx, (arclength_mono f a hx.2.le).trans _⟩,
  obtain rfl | hε := eq_or_ne ε ⊤, { exact le_top },
  have : ε / 2 ≠ ⊤ := λ h, (ennreal.div_eq_top.1 h).elim (λ h, two_ne_zero h.2) (λ h, hε h.1),
  /- extract div_ne_top ? -/
  by_contra' hac, apply (eq.refl $ arclength f a b).not_lt,
  calc  arclength f a b
      ≤ arclength f a b - ε/2 + ε/2 : tsub_le_iff_right.1 le_rfl
  ... < (∑ i in finset.range (n + 1), edist (f $ u i) (f $ u $ i+1)) + ε/2 :
        by { rw ennreal.add_lt_add_iff_right this, exact hl }
  ... ≤ (∑ i in finset.range n, edist (f $ u $ i+1) (f $ u $ i+1+1)) +
          (edist (f e) (f a) + edist (f e) (f $ u 1)) + ε/2 :
        add_le_add_right (by { rw [finset.sum_range_succ', hea],
          apply add_le_add_left (edist_triangle_left _ _ _) }) _
  ... ≤ (∑ i in finset.range n, arclength f (u $ i+1) (u $ i+1+1)) +
          (ε/2 + arclength f e (u 1)) + ε/2 :
        add_le_add_right
          (add_le_add (finset.sum_le_sum $ λ i _, edist_le_arclength f $ hu (i+1).le_succ) $
            add_le_add (le_of_lt $ hcb ⟨hae.le, hec⟩) $ edist_le_arclength f $ min_le_left _ d) _
  ... = _ + (ε + arclength f e (u 1)) : by rw [add_assoc, add_right_comm, ennreal.add_halves]
  ... ≤ _ + arclength f (u 0) (u 1) : by { rw [hea, ← arclength_add f hae.le $ min_le_left _ d],
          exact add_le_add_left (add_le_add_right hac.le _) _ }
  ... = ∑ i in finset.range (n + 1), arclength f (u i) (u $ i+1) : by rw finset.sum_range_succ'
  ... = arclength f (u 0) (u $ n+1) : arclength_sum f hu
  ... ≤ arclength f a b : by { rw hea, exact arclength_mono f a (hmem _).2 },
end

theorem continuous_right_arclength
  (hcont : continuous_within_at f (set.Ico a b) a) /- f is right continuous at a -/ :
  continuous_within_at (arclength f c) (set.Ici a) a :=
if hca : c ≤ a then
((continuous_add_left _).continuous_at.comp_continuous_within_at $ continuous_right_self_arclength
  f hab hrect hcont).congr (λ x hx, (arclength_add f hca hx).symm) (arclength_add f hca le_rfl).symm
else (filter.eventually_eq_of_mem (is_open_Iio.mem_nhds $ lt_of_not_le hca) $
  λ x hx, by apply arclength_eq_zero f (le_of_lt hx)).continuous_at.continuous_within_at

theorem continuous_left_arclength'
  (hcont : continuous_within_at f (set.Ioc a b) b) /- f is left continuous at b -/ :
  continuous_within_at (λ x, arclength f x c) (set.Iic b) b :=
begin
  rw ← arclength_comp_of_dual at hrect, rw arclength'_eq,
  refine (continuous_right_arclength (f ∘ of_dual) hab.dual hrect _).comp
    continuous_to_dual.continuous_within_at (λ x, id),
  convert hcont using 1, ext1, apply and_comm,
end

omit hab

theorem continuous_left_arclength
  (hcont : continuous_within_at f (set.Ioc a b) b) /- f is left continuous at b -/ :
  continuous_within_at (arclength f a) (set.Iic b) b :=
begin
  obtain hba | hab := le_or_lt b a,
  { apply continuous_const.continuous_within_at.congr (λ x hx, _),
    exacts [arclength_eq_zero f hba, arclength_eq_zero f $ trans hx hba] },
  refine (((ennreal.continuous_on_sub_left _).continuous_at _).comp_continuous_within_at $
    continuous_left_arclength' f hab hrect hcont).congr
    (λ x hx, arclength_sub f hx hrect) (arclength_sub f le_rfl hrect),
  rw arclength_self, exact is_open_ne.mem_nhds ennreal.top_ne_zero.symm,
end

theorem continuous_right_arclength'
  (hcont : continuous_within_at f (set.Ico a b) a) /- f is right continuous at a -/ :
  continuous_within_at (λ x, arclength f x b) (set.Ici a) a :=
begin
  rw ← arclength_comp_of_dual at hrect, rw arclength'_eq,
  refine (continuous_left_arclength (f ∘ of_dual) hrect _).comp
    continuous_to_dual.continuous_within_at (λ x, id),
  convert hcont using 1, ext1, apply and_comm,
end

theorem continuous_on_Iic_arclength (hcont : continuous_on f (set.Icc a b)) :
  continuous_on (arclength f a) (set.Iic b) :=
λ x hx, begin
  obtain hba | hab := le_or_lt b a,
  { exact continuous_on_Iic_arclength_of_ge _ hba _ hx },
  obtain rfl | hxb := eq_or_lt_of_le hx,
  { exact continuous_left_arclength f hrect ((hcont x ⟨hab.le, hx⟩).mono $ λ y h, ⟨h.1.le, h.2⟩) },
  refine (lt_or_le x a).elim (λ hxa, ((continuous_on_Iic_arclength_of_ge
      f le_rfl).continuous_at $ Iic_mem_nhds hxa).continuous_within_at)
    (λ hax, (continuous_at_iff_continuous_left_right.2 ⟨_, _⟩).continuous_within_at),
  { apply continuous_left_arclength f (ne_top_of_le_ne_top hrect $ arclength_mono f a hx),
    exact (hcont x ⟨hax, hx⟩).mono (λ y hy, ⟨hy.1.le, hy.2.trans hx⟩) },
  { apply continuous_right_arclength f hxb (ne_top_of_le_ne_top hrect $ arclength_anti f b hax),
    exact (hcont x ⟨hax, hx⟩).mono (λ y hy, ⟨hax.trans hy.1, hy.2.le⟩) },
end

theorem continuous_on_Ici_arclength' (hcont : continuous_on f (set.Icc a b)) :
  continuous_on (λ x, arclength f x b) (set.Ici a) :=
begin
  rw ← arclength_comp_of_dual at hrect, rw arclength'_eq,
  refine (continuous_on_Iic_arclength _ hrect _).comp continuous_to_dual.continuous_on (λ x, id),
  convert hcont using 1, ext1, apply and_comm,
end

end

section
/-!
### Continuity lemmas with respect to a given order-connected set.
-/

variables {s : set α} (hconn : s.ord_connected)
include hconn

lemma has_locally_bounded_variation_on_iff_arclength_ne_top :
  has_locally_bounded_variation_on f s ↔ ∀ ⦃a b⦄, a ∈ s → b ∈ s → arclength f a b ≠ ⊤ :=
forall₄_congr $ λ a b ha hb, by { rw set.inter_eq_right_iff_subset.2 (hconn.out ha hb), refl }

alias has_locally_bounded_variation_on_iff_arclength_ne_top ↔
  has_locally_bounded_variation_on.arclength_ne_top _

variables [topological_space α] [order_topology α]
          (hbdd : has_locally_bounded_variation_on f s)
          (hcont : continuous_on f s)
include hbdd hcont

lemma continuous_on_arclength_of_mem (ha : a ∈ s) : continuous_on (arclength f a) s :=
begin
  by_cases ∃ x ∈ s, ∀ y ∈ s, y ≤ x,
  { obtain ⟨x, hxs, hx⟩ := h,
    exact (continuous_on_Iic_arclength f
      (hbdd.arclength_ne_top f hconn ha hxs) $ hcont.mono $ hconn.out ha hxs).mono hx },
  push_neg at h,
  intros x hx, obtain ⟨y, hy, hxy⟩ := h x hx,
  exact ((continuous_on_Iic_arclength f (hbdd.arclength_ne_top f hconn ha hy) $
    hcont.mono $ hconn.out ha hy).continuous_at $ Iic_mem_nhds hxy).continuous_within_at,
end

variables (a b)

lemma continuous_on_arclength : continuous_on (arclength f a) s :=
λ x hxs, begin
  obtain hxa | hax := lt_or_le x a,
  { exact (continuous_at_arclength_of_gt f hxa).continuous_within_at },
  by_cases ∀ y ∈ s, x ≤ y,
  { exact ((continuous_add_left _).comp_continuous_on $ continuous_on_arclength_of_mem
      f hconn hbdd hcont hxs).congr (λ y hy, (arclength_add f hax $ h y hy).symm) x hxs },
  push_neg at h, obtain ⟨y, hys, hyx⟩ := h,
  obtain hay | hya := le_total a y,
  { apply ((continuous_add_left _).continuous_at.comp_continuous_within_at $
      continuous_on_arclength_of_mem f hconn hbdd hcont hys x hxs).congr_of_eventually_eq
      (set.eq_on.eventually_eq_of_mem _ $ inter_mem_nhds_within s $ Ici_mem_nhds hyx),
    exacts [(arclength_add f hay hyx.le).symm, λ z hz, (arclength_add f hay hz.2).symm] },
  { exact continuous_on_arclength_of_mem f hconn hbdd hcont (hconn.out hys hxs ⟨hya, hax⟩) x hxs },
end

lemma continuous_on_arclength' : continuous_on (λ x, arclength f x b) s :=
begin
  rw arclength'_eq,
  apply continuous_on_arclength _ _ hconn.dual _ hcont,
  exact hbdd.comp_of_dual,
end

end

section
/-!
### Continuity
-/

variables [topological_space α] [order_topology α]
          (a b)
          (hbdd : has_locally_bounded_variation_on f set.univ)
          (hcont : continuous f)
include hbdd hcont

theorem continuous_arclength  : continuous (arclength f a) :=
begin
  rw [continuous_iff_continuous_on_univ] at hcont ⊢,
  exact continuous_on_arclength f _ set.ord_connected_univ hbdd hcont,
end

theorem continuous_arclength' : continuous (λ x, arclength f x b) :=
begin
  rw [continuous_iff_continuous_on_univ] at hcont ⊢,
  exact continuous_on_arclength' f _ set.ord_connected_univ hbdd hcont,
end

end
