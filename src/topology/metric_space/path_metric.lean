import analysis.bounded_variation
import topology.path_connected
/- Authors: Rémi Bottinelli, Junyan Xu -/

open_locale ennreal big_operators
noncomputable theory

section arclength

variables {α E : Type*} [linear_order α] [pseudo_emetric_space E] (f : α → E) {a b c : α}

def arclength (a b : α) : ℝ≥0∞ := evariation_on f (set.Icc a b)

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

lemma arclength_sub' {a b c : α} (hbc : b ≤ c) (hac : arclength f b c ≠ ⊤) :
  arclength f a b = arclength f a c - arclength f b c :=
(le_total a b).elim
  (λ hab, ennreal.eq_sub_of_add_eq hac $ arclength_add f hab hbc)
  (arclength_sub₀ f)

lemma arclength_sub {a b c : α} (hbc : b ≤ c) (hac : arclength f a c ≠ ⊤) :
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

/- lemma arclength_comp (f : ℝ → E) (g : ℝ → ℝ) (hm : monotone g) (hc : continuous g) {a b : ℝ} :
  arclength f (g a) (g b) = arclength (f ∘ g) a b :=
  (use intermediate value theorem: `continuous_on.surj_on_Icc`)
  monotone => Icc maps to Icc -/

/- lemma arclength_Icc_extend' {a b : α} (h : a ≤ b) :
  arclength (set.Icc_extend h (f ∘ coe)) a b = arclength f a b :=
evariation_on.eq_of_eq_on $ λ x, set.Icc_extend_of_mem h _

lemma arclength_bot_top [order_bot α] [order_top α] :
  arclength f ⊥ ⊤ = evariation_on f set.univ :=
by { rw [arclength, ← set.eq_univ_iff_forall.2], exact λ _, ⟨bot_le, le_top⟩ } -/

lemma arclength_Icc_extend {a b : α} (h : a ≤ b) (f : set.Icc a b → E) :
  arclength (set.Icc_extend h f) a b = evariation_on f set.univ :=
evariation_on.comp_eq_of_monotone_on _ _
  ((set.monotone_proj_Icc _).monotone_on _) (set.maps_to_univ _ _) (set.proj_Icc_surj_on h)

variables [topological_space α] [order_topology α] (hab : a < b)
  (hrect : arclength f a b ≠ ⊤) /- f is rectifiable on [a,b] -/

lemma continuous_on_Iic_arclength_of_ge (h : b ≤ a) :
  continuous_on (arclength f a) (set.Iic b) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans hx h)

lemma continuous_on_Ici_arclength'_of_ge (h : b ≤ a) :
  continuous_on (λ x, arclength f x b) (set.Ici a) :=
continuous_on_const.congr $ λ x hx, arclength_eq_zero f (trans h hx)

lemma continuous_at_arclength_of_gt (h : b < a) : continuous_at (arclength f a) b :=
continuous_at_const.congr $ set.eq_on.eventually_eq_of_mem
  (λ x hx, (arclength_eq_zero f (set.mem_Iio.1 hx).le).symm) $ Iio_mem_nhds h

lemma continuous_at_arclength'_of_gt (h : b < a) : continuous_at (λ x, arclength f x b) a :=
continuous_at_const.congr $ set.eq_on.eventually_eq_of_mem
  (λ x hx, (arclength_eq_zero f (set.mem_Ioi.1 hx).le).symm) $ Ioi_mem_nhds h

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

omit hrect

variables {a b} {s : set α} (hconn : s.ord_connected) (hbdd : has_locally_bounded_variation_on f s)

include hconn
lemma has_locally_bounded_variation_on_iff_arclength_ne_top :
  has_locally_bounded_variation_on f s ↔ ∀ a b, a ∈ s → b ∈ s → arclength f a b ≠ ⊤ :=
forall₄_congr $ λ a b ha hb, by { rw set.inter_eq_right_iff_subset.2 (hconn.out ha hb), refl }

lemma has_locally_bounded_variation_on.arclength_ne_top
  (ha : a ∈ s) (hb : b ∈ s) : arclength f a b ≠ ⊤ :=
(has_locally_bounded_variation_on_iff_arclength_ne_top f hconn).1 hbdd a b ha hb

variable (hcont : continuous_on f s)
include hbdd hcont

lemma continuous_on_arclength_aux (ha : a ∈ s) : continuous_on (arclength f a) s :=
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
  { exact ((continuous_add_left _).comp_continuous_on $ continuous_on_arclength_aux
      f hconn hbdd hcont hxs).congr (λ y hy, (arclength_add f hax $ h y hy).symm) x hxs },
  push_neg at h, obtain ⟨y, hys, hyx⟩ := h,
  obtain hay | hya := le_total a y,
  { apply ((continuous_add_left _).continuous_at.comp_continuous_within_at $
      continuous_on_arclength_aux f hconn hbdd hcont hys x hxs).congr_of_eventually_eq
      (set.eq_on.eventually_eq_of_mem _ $ inter_mem_nhds_within s $ Ici_mem_nhds hyx),
    exacts [(arclength_add f hay hyx.le).symm, λ z hz, (arclength_add f hay hz.2).symm] },
  { exact continuous_on_arclength_aux f hconn hbdd hcont (hconn.out hys hxs ⟨hya, hax⟩) x hxs },
end

lemma continuous_on_arclength' : continuous_on (λ x, arclength f x b) s :=
begin
  rw arclength'_eq,
  apply continuous_on_arclength _ _ hconn.dual _ hcont,
  /- TODO: extract has_locally_bounded_variation_on (f ∘ of_dual) (of_dual ⁻¹' s) -/
  refine λ a b ha hb hT, hbdd b a hb ha _,
  rw [← evariation_on.comp_of_dual, set.preimage_inter],
  convert hT, ext, apply and_comm,
end

variable (hbdd' : has_locally_bounded_variation_on f set.univ)
omit hconn hbdd hcont
include hbdd'

theorem continuous_arclength (hcont : continuous f) : continuous (arclength f a) :=
begin
  rw [continuous_iff_continuous_on_univ] at hcont ⊢,
  exact continuous_on_arclength f _ set.ord_connected_univ hbdd' hcont,
end

theorem continuous_arclength' (hcont : continuous f) : continuous (λ x, arclength f x b) :=
begin
  rw [continuous_iff_continuous_on_univ] at hcont ⊢,
  exact continuous_on_arclength' f _ set.ord_connected_univ hbdd' hcont,
end

end arclength

local notation `𝕀` := unit_interval

namespace unit_interval

lemma antitone_symm : antitone symm := λ x y h, sub_le_sub_left h _

lemma bijective_symm : function.bijective symm :=
function.bijective_iff_has_inverse.2 $ ⟨_, symm_symm, symm_symm⟩

def div_two (t : 𝕀) : 𝕀 := ⟨(t/2 : ℝ), div_mem t.2.1 zero_le_two $ t.2.2.trans one_le_two⟩

lemma two_mul_div_two (t : 𝕀) : (2 * div_two t : ℝ) = t := mul_div_cancel' _ two_ne_zero

lemma div_two_mem_Iic (t : 𝕀) : div_two t ∈ set.Iic (div_two 1) :=
div_le_div_of_le_of_nonneg t.2.2 zero_le_two

lemma half_le_symm_iff (t : 𝕀) : 1 / 2 ≤ (symm t : ℝ) ↔ (t : ℝ) ≤ 1 / 2 :=
by rw [coe_symm_eq, le_sub_iff_add_le, add_comm, ←le_sub_iff_add_le, sub_half]

lemma symm_mem_Ici_iff (t : 𝕀) : symm t ∈ set.Ici (div_two 1) ↔ t ∈ set.Iic (div_two 1) :=
half_le_symm_iff t

/- lemma symm_le_half_iff (t : 𝕀) : (symm t : ℝ) ≤ 1 / 2 ↔ 1 / 2 ≤ (t : ℝ) :=
by rw [coe_symm_eq, sub_le_iff_le_add, add_comm, ←sub_le_iff_le_add, sub_half]

lemma symm_mem_Iic_iff (t : 𝕀) : symm t ∈ set.Iic (div_two 1) ↔ t ∈ set.Ici (div_two 1) :=
symm_le_half_iff t -/

end unit_interval

lemma monotone_affine_map_of_le {s t : ℝ} (hst : s ≤ t) : monotone (λ u, s + (t - s) * u) :=
λ x y h, add_le_add_left (mul_le_mul_of_nonneg_left h $ sub_nonneg.2 hst) _

lemma monotone.Icc_maps_to_Icc {α β} [preorder α] [preorder β] {f : α → β} (hf : monotone f)
  (a b : α) : (set.Icc a b).maps_to f (set.Icc (f a) (f b)) := λ x hx, ⟨hf hx.1, hf hx.2⟩

lemma affine_map_mem_Icc {s t u : ℝ} (hst : s ≤ t)
  (hu : u ∈ set.Icc (0 : ℝ) 1) : s + (t - s) * u ∈ set.Icc s t :=
begin
  convert (monotone_affine_map_of_le hst).Icc_maps_to_Icc 0 1 hu;
  simp only [mul_zero, mul_one, add_zero, add_sub_cancel'_right],
end

lemma affine_map_surj_on {s t : ℝ} (hst : s ≤ t) :
  (set.Icc (0 : ℝ) 1).surj_on (λ u, s + (t - s) * u) (set.Icc s t) :=
begin
  convert intermediate_value_Icc zero_le_one (continuous.continuous_on _) using 1,
  { simp only [mul_zero, mul_one, add_zero, add_sub_cancel'_right] },
  any_goals { apply_instance },
  continuity,
end

/- lemma affine_map_mem_Icc_iff (s t u : ℝ) (hs : s < t) :
  s + (t - s) * u ∈ set.Icc s t ↔ u ∈ set.Icc (0 : ℝ) 1 :=
begin
  simp_rw [set.add_mem_Icc_iff_right, sub_self, set.mem_Icc], sorry,
end -/


alias evariation_on.eq_of_eq_on ← set.eq_on.evariation_on_eq

namespace path
variables {E : Type*} [pseudo_emetric_space E] {x y z : E} (p : path x y) (q : path y z)

def length (p : path x y) : ℝ≥0∞ := evariation_on p set.univ --arclength p 0 1

lemma edist_le_length (p : path x y) : edist x y ≤ p.length :=
by { simp_rw [length, ← p.source, ← p.target], exact evariation_on.edist_le _ trivial trivial }

lemma length_refl (x : E) : (path.refl x).length = 0 :=
evariation_on.constant_on $ by { rintro _ ⟨_, _, rfl⟩ _ ⟨_, _, rfl⟩, refl }
-- TODO: extract subsingleton_image_const

lemma length_symm (p : path x y) : p.symm.length = p.length :=
evariation_on.comp_eq_of_antitone_on _ _ (unit_interval.antitone_symm.antitone_on _)
  (set.maps_to_univ _ _) $
  set.surjective_iff_surj_on_univ.1 $ unit_interval.bijective_symm.surjective

--instance : zero_le_one_class 𝕀 := ⟨(zero_le_one : (0 : ℝ) ≤ 1)⟩

open unit_interval

lemma trans_eq_on_left :
  (set.Iic $ div_two 1).eq_on (p.trans q) (p ∘ λ t, set.proj_Icc 0 1 zero_le_one (2 * t)) :=
λ t ht, if_pos ht

lemma trans_eq_on_right :
  (set.Ici $ div_two 1).eq_on (p.trans q) (q ∘ λ t, set.proj_Icc 0 1 zero_le_one (2 * t - 1)) :=
λ t ht, begin
  by_cases (t : ℝ) ≤ 1/2,
  { apply (if_pos h).trans,
    rw [function.comp_app, h.antisymm ht, mul_one_div_cancel, sub_self, set.proj_Icc_left],
    exacts [p.extend_one.trans q.source.symm, two_ne_zero] },
  { exact if_neg h },
end

lemma length_trans (p : path x y) (q : path y z) : (p.trans q).length = p.length + q.length :=
begin
  rw [length, evariation_on.split_univ _ (div_two 1),
    (p.trans_eq_on_left q).evariation_on_eq, (p.trans_eq_on_right q).evariation_on_eq],
  congr' 1; apply evariation_on.comp_eq_of_monotone_on _ _ _ (set.maps_to_univ _ _),
  { refine λ t ht, ⟨div_two t, div_two_mem_Iic t, _⟩,
    dsimp only, rw [two_mul_div_two, set.proj_Icc_of_mem _ t.prop],
    ext, refl },
  work_on_goal 2 { refine λ t ht, ⟨unit_interval.symm
      (div_two $ unit_interval.symm t), (symm_mem_Ici_iff _).2 (div_two_mem_Iic _), _⟩,
    dsimp only, rw [coe_symm_eq, mul_sub, mul_one, two_mul_div_two, sub_right_comm,
      (_ : (2 - 1 : ℝ) = 1), ← coe_symm_eq, unit_interval.symm_symm, set.proj_Icc_of_mem _ t.prop],
    { ext, refl }, norm_num },
  all_goals { apply ((set.monotone_proj_Icc _).comp $ λ x y h, _).monotone_on },
  { exact mul_le_mul_of_nonneg_left h zero_le_two },
  { exact sub_le_sub_right (mul_le_mul_of_nonneg_left h zero_le_two) _ },
end

/- Two definitions agree. -/
lemma evariation_on_extend_unit_interval_eq_length (p : path x y) :
  evariation_on p.extend 𝕀 = p.length := arclength_Icc_extend zero_le_one p

section
variables {X : Type*} {f : ℝ → X} {s t : ℝ} (hst : s ≤ t)
include hst

def of_continuous_on [topological_space X]
  (hf : continuous_on f (set.Icc s t)) : path (f s) (f t) :=
begin
  refine ⟨⟨f ∘ λ u, s + (t - s) * u, hf.comp_continuous (by continuity) _⟩, _, _⟩,
  { exact λ u, affine_map_mem_Icc hst u.2 },
  all_goals { simp only [function.comp_app,
    set.Icc.coe_zero, set.Icc.coe_one, mul_zero, add_zero, mul_one, add_sub_cancel'_right] },
end

lemma length_of_continuous_on [pseudo_emetric_space X] (hf : continuous_on f (set.Icc s t)) :
  (of_continuous_on hst hf).length = arclength f s t :=
begin
  apply evariation_on.comp_eq_of_monotone_on _ _ (monotone.monotone_on _ _) _ (λ x hx, _),
  { exact (monotone_affine_map_of_le hst).comp (λ _ _, id) },
  { exact λ x hx, affine_map_mem_Icc hst x.2 },
  { obtain ⟨y, hy, h'⟩ := affine_map_surj_on hst hx, exact ⟨⟨y, hy⟩, trivial, h'⟩ },
end

end

end path

section path_emetric

def path_emetric (E : Type*) [pseudo_emetric_space E] := E

variables {E : Type*} [pseudo_emetric_space E]

def to_path_emetric : E ≃ path_emetric E := equiv.refl _
def from_path_emetric : path_emetric E ≃ E := equiv.refl _

lemma from_to_path_emetric (x : E) : from_path_emetric (to_path_emetric x) = x := rfl
lemma to_from_path_emetric (x : path_emetric E) : to_path_emetric (from_path_emetric x) = x := rfl

local notation `of` := to_path_emetric
local notation `fo` := from_path_emetric

instance : pseudo_emetric_space (path_emetric E) :=
{ edist := λ x y, ⨅ p : path (fo x) (fo y), p.length,
  edist_self := λ x, le_antisymm (infi_le_of_le _ $ (path.length_refl _).le) zero_le',
  edist_comm := λ x y, by apply le_antisymm;
    exact le_infi (λ p, (infi_le _ _).trans_eq p.length_symm),
  edist_triangle := λ x y z, begin
    simp_rw [ennreal.infi_add, ennreal.add_infi],
    exact le_infi₂ (λ p q, (infi_le _ _).trans_eq $ p.length_trans q),
  end }

class length_space (E) [pseudo_emetric_space E] : Prop :=
(isom : isometry (of : E → path_emetric E))

lemma edist_le_edist_of (x y : E) : edist x y ≤ edist (of x) (of y) :=
le_infi $ λ p, p.edist_le_length

lemma from_length_emetric_nonexpanding :
  lipschitz_with 1 (from_path_emetric : path_emetric E → E) :=
λ x y, by { rw [ennreal.coe_one, one_mul], exact edist_le_edist_of x y }

lemma path_emetric.edist_le_arclength {f : ℝ → E} {s t : ℝ} (hst : s ≤ t)
  (hf : continuous_on f (set.Icc s t)) : edist (of $ f s) (of $ f t) ≤ arclength f s t :=
(infi_le _ $ path.of_continuous_on hst hf).trans_eq $ path.length_of_continuous_on _ _

lemma path_emetric.edist_le_max {f : ℝ → E} (s t : ℝ) (hf : continuous_on f (set.uIcc s t)) :
  edist (of $ f s) (of $ f t) ≤ max (arclength f s t) (arclength f t s) :=
begin
  obtain hst | hts := le_total s t,
  { rw max_eq_left ((arclength_eq_zero f hst).trans_le $ zero_le _),
    exact path_emetric.edist_le_arclength hst (hf.mono set.Icc_subset_uIcc) },
  { rw [max_eq_right ((arclength_eq_zero f hts).trans_le $ zero_le _), edist_comm],
    exact path_emetric.edist_le_arclength hts (hf.mono set.Icc_subset_uIcc') },
end

lemma path_emetric.continuous_of_locally_bounded_variation
  {f : ℝ → E} {s : set ℝ} (hconn : s.ord_connected)
  (hcont : continuous_on f s) (fbdd : has_locally_bounded_variation_on f s) :
  continuous_on (of ∘ f) s :=
λ x hx, begin
  rw [continuous_within_at, emetric.tendsto_nhds],
  have := (continuous_on_arclength f x hconn fbdd hcont x hx).max
    (continuous_on_arclength' f x hconn fbdd hcont x hx),
  dsimp only at this, rw [arclength_self, max_self] at this,
  refine λ ε hε, (ennreal.nhds_zero_basis.tendsto_right_iff.1 this ε hε).mp _,
  apply filter.eventually_inf_principal.2,
  refine filter.eventually_of_forall (λ y hy h, _),
  rw edist_comm,
  exact (path_emetric.edist_le_max x y $ hcont.mono $ hconn.uIcc_subset hx hy).trans_lt h,
end

@[simps] lemma path.of_length_ne_top {x y : E} (p : path x y)
  (hp : p.length ≠ ⊤) : path (of x) (of y) :=
begin
  refine ⟨⟨of ∘ p, _⟩, p.source, p.target⟩,
  convert continuous_on_iff_continuous_restrict.1
    (path_emetric.continuous_of_locally_bounded_variation
      set.ord_connected_Icc p.continuous_extend.continuous_on $
      has_bounded_variation_on.has_locally_bounded_variation_on _),
  { ext, rw p.extend_extends' },
  { rwa ← p.evariation_on_extend_unit_interval_eq_length at hp },
end

/-- Every continuous curve, rectifiable or not, has the same length in the path metric. -/
lemma path_emetric.evariation_of_eq_evariation {f : ℝ → E}
  {s : set ℝ} (hconn : s.ord_connected) (hcont : continuous_on f s) :
  evariation_on (of ∘ f) s = evariation_on f s :=
begin
  refine (supr_le _).antisymm (supr_le _),
  { rintro ⟨n, u, um, us⟩,
    refine (finset.sum_le_sum $ λ i hi, _).trans _,
    { exact λ i, arclength f (u i) (u $ i+1) },
    { rw edist_comm, exact path_emetric.edist_le_arclength
        (um $ i.le_succ) (hcont.mono $ hconn.out (us i) (us _)) },
    { rw arclength_sum f um, apply evariation_on.mono f (hconn.out (us 0) (us n)) } },
  { refine λ u, trans _ (le_supr _ u),
    refine finset.sum_le_sum (λ i hi, _),
    convert from_length_emetric_nonexpanding.edist_le_mul _ _,
    rw [ennreal.coe_one, one_mul], refl },
end

lemma path.length_of_length_ne_top {x y : E} (p : path x y) (hp : p.length ≠ ⊤) :
  (p.of_length_ne_top hp).length = p.length :=
begin
  simp_rw [← path.evariation_on_extend_unit_interval_eq_length,
    ← path_emetric.evariation_of_eq_evariation
      set.ord_connected_Icc p.continuous_extend.continuous_on],
  congr' 1, ext, /- very strange that `refl` doesn't work here ... -/
  simp only [path.extend, set.Icc_extend, function.comp_app, path.of_length_ne_top_apply],
end

instance (E) [pseudo_emetric_space E] : length_space (path_emetric E) :=
⟨λ x y, begin
  refine (le_infi $ λ p, _).antisymm (edist_le_edist_of x y),
  by_cases p.length = ⊤, { rw h, exact le_top },
  rw ← p.length_of_length_ne_top h,
  exact infi_le _ _,
end⟩

end path_emetric
