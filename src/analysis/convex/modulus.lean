/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.normed_space.ordered

/-!
# Modulus and characteristic of convexity
-/

namespace set
variables {ι : Sort*} {α : Type*} {s : set α} {a : α}

protected lemma subsingleton.bdd_above [preorder α] [nonempty α] (h : s.subsingleton) :
  bdd_above s :=
h.eq_empty_or_singleton.elim (λ h, h.substr bdd_above_empty) $
  by { rintro ⟨a, rfl⟩, exact bdd_above_singleton }

protected lemma subsingleton.bdd_below [preorder α] [nonempty α] (h : s.subsingleton) :
  bdd_below s :=
h.eq_empty_or_singleton.elim (λ h, h.substr bdd_below_empty) $
  by { rintro ⟨a, rfl⟩, exact bdd_below_singleton }

lemma range_const_subsingleton (a : α) : (set.range (λ i : ι, a)).subsingleton :=
set.subsingleton_of_subset_singleton set.range_const_subset

end set

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] {a : α}

lemma half_neg (h : a < 0) : a / 2 < 0 := div_neg_of_neg_of_pos h zero_lt_two

lemma lt_half (h : a < 0) :  a < a / 2 :=
by { rw [lt_div_iff (@zero_lt_two α _ _), mul_two], exact add_lt_of_neg_of_le h le_rfl }

lemma le_half (h : a ≤ 0) : a ≤ a / 2 :=
begin
  obtain rfl | h := h.eq_or_lt,
  { rw zero_div },
  { exact (lt_half h).le }
end

end linear_ordered_field

section has_Sup
variables {ι : Sort*} {α : Type*} [has_Sup α] {f g : ι → α} {p q : ι → Prop}
  {s : set α} {r : ℝ} {a b : α}

open set

lemma supr_congr_subtype (f : ι → α) (hpq : ∀ i, p i ↔ q i) :
  (⨆ i : subtype p, f i) = ⨆ i : subtype q, f i :=
begin
  unfold supr,
  congr' 1,
  ext,
  simp_rw [mem_range, subtype.exists, subtype.coe_mk, exists_prop, hpq],
end

end has_Sup

section conditionally_complete_lattice
variables {ι : Sort*} {α : Type*} [conditionally_complete_lattice α] {f g : ι → α} {p q : ι → Prop}
  {s : set α} {r : ℝ} {a b : α}

lemma bcsupr_mono_right (hg : bdd_above (set.range g)) (hfg : ∀ i, p i → f i ≤ g i) :
  (⨆ (i : ι) (hi : p i), f i) ≤ ⨆ (i : ι) (hi : p i), g i :=
csupr_le_csupr begin
  obtain ⟨x, hx⟩ := hg,
  refine ⟨Sup ∅ ⊔ x, _⟩,
  rintro _ ⟨i, rfl⟩,
  casesI is_empty_or_nonempty (p i),
  { convert le_sup_left,
    exact (set.range_eq_empty _).symm },
  { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans le_sup_right }
end $ λ a, csupr_le_csupr (set.range_const_subsingleton _).bdd_above $ hfg _

-- lemma le_bcsupr {f : ι → α} (hf : bdd_above (set.range f)) (i : ι) (hi : p i) :
--   f i ≤ ⨆ (i : ι) (hi : p i), f i :=
-- le_csupr_of_le begin
--   obtain ⟨x, hx⟩ := hf,
--   refine ⟨Sup ∅ ⊔ x, _⟩,
--   rintro _ ⟨i, rfl⟩,
--   casesI is_empty_or_nonempty (p i),
--   { convert le_sup_left,
--     exact (set.range_eq_empty _).symm },
--   { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans le_sup_right }
-- end i $ le_csupr hf hi

-- lemma le_bcsupr_of_le {f : Π i, p i → α} (i : ι) (hi : p i) (ha : a ≤ f i hi) :
--   a ≤ ⨆ (i : ι) (hi : p i), f i hi :=
-- begin
--   sorry
-- end

end conditionally_complete_lattice

section conditionally_complete_linear_order_bot
open set
variables {ι : Sort*} {κ : ι → Sort*} {α : Type*} [conditionally_complete_linear_order_bot α]
  {f g : ι → α} {p q : ι → Prop} {a b : α}

lemma bcsupr_mono_left (f : ι → α) (hf : bdd_above (set.range $ λ x : subtype q, f x))
  (hfg : ∀ i, p i → q i) :
  (⨆ i : subtype p, f i) ≤ ⨆ i : subtype q, f i :=
begin
  casesI is_empty_or_nonempty (subtype p),
  { exact (csupr_of_empty _).trans_le bot_le },
  { exact csupr_le (λ x, le_csupr_of_le hf ⟨x, hfg _ x.2⟩ le_rfl) }
end

/-- The indexed infimum of a function is bounded above by the value taken at one point. -/
lemma cinfi_le' {f : ι → α} (i : ι) : infi f ≤ f i := cinfi_le (order_bot.bdd_below _) _

lemma cInf_le_of_le' {s : set α} (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
cInf_le_of_le (order_bot.bdd_below _) hb h

lemma cinfi_le_of_le' {f : ι → α} (i : ι) (h : f i ≤ a) : infi f ≤ a :=
cinfi_le_of_le (order_bot.bdd_below _) _ h

lemma cSup_le_of_forall_le {s : set α} (h : ∀ b ∈ s, b ≤ a) : Sup s ≤ a :=
begin
  obtain rfl | ⟨i, hi⟩ := s.eq_empty_or_nonempty,
  { exact cSup_empty.trans_le bot_le },
  {
    sorry
    -- exact cSup_le'' hi,
  }
end

lemma cinfi_le_cinfi' {f g : ι → α} (h : ∀ i, f i ≤ g i) : infi f ≤ infi g :=
cinfi_le_cinfi (order_bot.bdd_below _) h

lemma cinfi₂_le_cinfi₂' {f g : Π i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
  (⨅ i j, f i j) ≤ ⨅ i j, g i j :=
cinfi_le_cinfi' $ λ i, cinfi_le_cinfi' $ h i

end conditionally_complete_linear_order_bot

namespace real
variables {ι : Sort*} {κ : ι → Sort*} {f g : ι → ℝ} {p q : ι → Prop} {S : set ℝ} {r : ℝ} {i : ι}
  {j : κ i}

lemma supr_zero (h : ∀ i, f i = 0) : (⨆ i, f i) = 0 := by rw [funext h, csupr_const_zero]

lemma supr₂_zero {f : Π i, κ i → ℝ} (h : ∀ i j, f i j = 0) : (⨆ i j, f i j) = 0 :=
supr_zero $ λ i, supr_zero $ h i

lemma Sup_nonneg' (h : r ∈ S) (hr : 0 ≤ r) : 0 ≤ Sup S :=
begin
  by_cases hs : bdd_above S,
  { exact le_cSup_of_le hs h hr },
  { exact (Sup_of_not_bdd_above hs).ge }
end

lemma Sup_nonneg'' (h : ∀ ε : ℝ, ε < 0 → ∃ x ∈ S, ε ≤ x) : 0 ≤ Sup S :=
begin
  obtain rfl | hs := S.eq_empty_or_nonempty,
  { exact Sup_empty.ge },
  by_cases hs' : bdd_above S,
  { refine (le_Sup_iff hs' hs).2 (λ ε hε, _),
    obtain ⟨x, hx, hεx⟩ := h _ (half_neg hε),
    refine ⟨x, hx, _⟩,
    rw zero_add,
    exact (lt_half hε).trans_le hεx },
  { exact (Sup_of_not_bdd_above hs').ge }
end

lemma Inf_nonpos'' (h : ∀ ε : ℝ, 0 < ε → ∃ x ∈ S, x ≤ ε) : Inf S ≤ 0 :=
begin
  obtain rfl | hs := S.eq_empty_or_nonempty,
  { exact Inf_empty.le },
  by_cases hs' : bdd_below S,
  { refine (Inf_le_iff hs' hs).2 (λ ε hε, _),
    obtain ⟨x, hx, hxε⟩ := h _ (half_pos hε),
    refine ⟨x, hx, _⟩,
    rw zero_add,
    exact hxε.trans_lt (half_lt_self hε) },
  { exact (Inf_of_not_bdd_below hs').le }
end

lemma supr_nonneg' (ha : 0 ≤ f i) : 0 ≤ ⨆ i, f i := Sup_nonneg' (set.mem_range_self _) ha

lemma supr_nonneg (hf : ∀ a, 0 ≤ f a) : 0 ≤ ⨆ a, f a :=
begin
  refine real.Sup_nonneg _ _,
  rintro _ ⟨a, _, rfl⟩,
  exact hf a,
end

lemma supr₂_nonneg' {f : Π i, κ i → ℝ} (h : 0 ≤ f i j) : 0 ≤ ⨆ i j, f i j :=
supr_nonneg' $ supr_nonneg' h

lemma supr₂_nonneg {f : Π i, κ i → ℝ} (h : ∀ i j, 0 ≤ f i j) : 0 ≤ ⨆ i j, f i j :=
supr_nonneg $ λ i, supr_nonneg $ h i

lemma Sup_le_of_nonneg {s : set ℝ} (hr : 0 ≤ r) (h : ∀ a ∈ s, a ≤ r) : Sup s ≤ r :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { rwa Sup_empty },
  { exact cSup_le hs h }
end

lemma supr_le_of_nonneg (hr : 0 ≤ r) (hf : ∀ a, f a ≤ r) : (⨆ a, f a) ≤ r :=
begin
  casesI is_empty_or_nonempty ι,
  { rwa csupr_empty },
  { exact csupr_le hf }
end

lemma supr₂_le_of_nonneg {f : Π i, κ i → ℝ} (hr : 0 ≤ r) (hf : ∀ i j, f i j ≤ r) :
  (⨆ i j, f i j) ≤ r :=
supr_le_of_nonneg hr $ λ i, supr_le_of_nonneg hr $ hf i

lemma bsupr_mono (hg : bdd_above (set.range g)) (hg' : ∀ a, q a → 0 ≤ g a) (hfg : ∀ a, f a ≤ g a)
  (hpq : ∀ i, p i → q i) :
  (⨆ i (hi : p i), f i) ≤ ⨆ i (hi : q i), g i :=
csupr_le_csupr begin
  obtain ⟨x, hx⟩ := hg,
  refine ⟨max 0 x, _⟩,
  rintro _ ⟨a, rfl⟩,
  casesI is_empty_or_nonempty (q a),
  { dsimp,
    rw csupr_empty,
    exact le_max_left _ _ },
  { exact (csupr_le $ λ _, hx $ set.mem_range_self _).trans (le_max_right _ _) }
end $ λ a, begin
  casesI is_empty_or_nonempty (p a),
  { rw csupr_empty,
    exact supr_nonneg (hg' _) },
  casesI is_empty_or_nonempty (q a),
  { haveI := function.is_empty (hpq a),
    rwa [csupr_empty, csupr_empty] },
  { exact csupr_le (λ ha, (hfg _).trans csupr_const.ge) }
end

lemma Inf_le_of_nonneg {s : set ℝ} {a : ℝ} (ha : a ∈ s) (h : 0 ≤ a) : Inf s ≤ a :=
begin
  by_cases hs : bdd_below s,
  { exact cInf_le hs ha },
  { rwa Inf_of_not_bdd_below hs }
end

lemma Inf_le_of_le_of_nonneg {s : set ℝ} {a b : ℝ} (hb : b ∈ s) (ha : 0 ≤ a) (h : b ≤ a) :
  Inf s ≤ a :=
begin
  by_cases hs : bdd_below s,
  { exact cInf_le_of_le hs hb h },
  { rwa Inf_of_not_bdd_below hs }
end

end real

open real

open_locale nnreal

namespace nnreal
variables {ι : Sort*} {κ : ι → Sort*} {p q : ι → Prop} {f g : ι → ℝ≥0} {a : ℝ≥0}

open set

lemma coe_infi (f : ι → ℝ≥0) : (↑(infi f) : ℝ) = ⨅ i, f i :=
by { rw [infi, coe_Inf, ←range_comp], refl }

lemma coe_infi₂ (f : Π i, κ i → ℝ≥0) : (↑(⨅ i j, f i j) : ℝ) = ⨅ i j, f i j := by simp_rw coe_infi

protected lemma Inf_empty : Inf (∅ : set ℝ≥0) = 0 :=
nnreal.coe_injective $ by rw [coe_Inf, nnreal.coe_zero, image_empty, real.Inf_empty]

protected lemma infi_of_empty [is_empty ι] (f : ι → ℝ≥0) : infi f = 0 :=
by rw [infi_of_empty', nnreal.Inf_empty]

protected lemma supr_of_empty [is_empty ι] (f : ι → ℝ≥0) : supr f = 0 :=
by rw [supr_of_empty', cSup_empty, bot_eq_zero]

lemma binfi_mono_left (hf : bdd_above $ set.range $ f ∘ (coe : subtype q → ι))
  (hfg : ∀ i, q i → p i) :
  (⨅ i : subtype p, f i) ≤ ⨅ i : subtype q, f i :=
begin
  sorry
  -- casesI is_empty_or_nonempty (subtype q),
  -- { exact (nnreal.infi_of_empty _).trans_le bot_le },
  -- { haveI : nonempty (subtype q) :=
  --     nonempty.map (λ x : subtype p, ⟨x.1, hfg _ x.2⟩) ‹nonempty (subtype p)›,

  --   refine le_cinfi (λ x, cinfi_le_of_le' _ _), }
end

lemma Inf_le_of_forall_le {s : set ℝ≥0} (h : ∀ b ∈ s, b ≤ a) : Inf s ≤ a :=
begin
  obtain rfl | ⟨i, hi⟩ := s.eq_empty_or_nonempty,
  { exact nnreal.Inf_empty.trans_le bot_le },
  { exact cInf_le_of_le' hi (h _ hi) }
end

lemma infi_le_of_forall_le {f : ι → ℝ≥0} (h : ∀ i, f i ≤ a) : infi f ≤ a :=
begin
  sorry
  -- obtain rfl | ⟨i, hi⟩ := s.eq_empty_or_nonempty,
  -- { exact nnreal.Inf_empty.trans_le bot_le },
  -- { exact cInf_le_of_le' hi (h _ hi) }
end

lemma infi₂_le_of_forall_le {f : Π i, κ i → ℝ≥0} (h : ∀ i j, f i j ≤ a) : (⨅ i j, f i j) ≤ a :=
infi_le_of_forall_le $ λ i, infi_le_of_forall_le $ h i

-- lemma Inf_le_of_forall_le :

@[simp] lemma supr_const_zero : (⨆ i : ι, (0 : ℝ≥0)) = 0 :=
begin
  casesI is_empty_or_nonempty ι,
  { exact nnreal.supr_of_empty _ },
  { exact csupr_const }
end

lemma supr_zero (hf : ∀ i, f i = 0) : (⨆ i, f i) = 0 := by rw [funext hf, supr_const_zero]

lemma supr₂_zero {f : Π i, κ i → ℝ≥0} (hf : ∀ i j, f i j = 0) : (⨆ i j, f i j) = 0 :=
supr_zero $ λ i, supr_zero $ hf i

end nnreal

open nnreal

variables {E : Type*} {ε : ℝ}

section semi_normed_group
variables (E ε) [semi_normed_group E]

/-- Modulus of convexity. -/
noncomputable def convex_mod (ε : ℝ) : ℝ≥0 :=
1 - (⨆ xy : {xy : E × E // ∥xy.1∥ ≤ 1 ∧ ∥xy.2∥ ≤ 1 ∧ ε ≤ dist xy.1 xy.2},
  ∥(xy : E × E).1 + (xy : E × E).2∥₊) / 2

/-- Characteristic of convexity. -/
noncomputable def convex_char : ℝ := Sup {ε | convex_mod E ε = 0}

lemma convex_mod_le_one : convex_mod E ε ≤ 1 := tsub_le_self

lemma convex_mod_set_bdd_above (ε : ℝ) :
  bdd_above (set.range $
    λ xy : {xy : E × E // ∥xy.fst∥ ≤ 1 ∧ ∥xy.snd∥ ≤ 1 ∧ ε ≤ dist xy.fst xy.snd},
      ∥(xy : E × E).1 + (xy : E × E).2∥₊) :=
⟨2, set.forall_range_iff.2 $ λ xy, (norm_add_le _ _).trans $ add_le_add xy.2.1 xy.2.2.1⟩

lemma convex_mod_mono : monotone (convex_mod E) :=
begin
  rintro a b hab,
  unfold convex_mod,
  refine tsub_le_tsub_left ((div_le_div_right₀ _).2 _) _,
  { exact zero_lt_two.ne' },
  { exact bcsupr_mono_left (λ xy : E × E, ∥(xy : E × E).1 + (xy : E × E).2∥₊)
      (convex_mod_set_bdd_above _ _) (λ xy, and.imp_right (and.imp_right hab.trans)) }
end

lemma convex_mod_of_two_lt {ε : ℝ} (hε : 2 < ε) : convex_mod E ε = 1 :=
begin
  unfold convex_mod,
  rw [nnreal.supr_zero (λ x, _), zero_div, tsub_zero],
  refine (hε.not_le $ x.2.2.2.trans $ (dist_le_norm_add_norm _ _).trans $
    add_le_add x.2.1 x.2.2.1).elim,
end

variables {ε}

lemma convex_mod_of_nonpos'' (hε : ε ≤ 0) : convex_mod E ε = convex_mod E 0 :=
begin
  unfold convex_mod,
  congr' 2,
  refine supr_congr_subtype (λ xy : E × E, ∥(xy : E × E).1 + (xy : E × E).2∥₊) (λ xy, _),
  rw [and_iff_left dist_nonneg, and_iff_left (hε.trans dist_nonneg)],
end

lemma convex_char_nonneg : 0 ≤ convex_char E :=
begin
  obtain h | h := (zero_le $ convex_mod E 0).eq_or_lt,
  { exact Sup_nonneg' h.symm le_rfl },
  { exact Sup_nonneg _ (λ ε H, le_of_not_lt $ λ hε, h.ne' $
    (convex_mod_of_nonpos'' _ hε.le).symm.trans H) }
end

lemma convex_char_eq_Inf : convex_char E = Inf {ε | 0 < convex_mod E ε} :=
begin
  sorry
end

variables (E)

lemma convex_char_le_two : convex_char E ≤ 2 :=
Sup_le_of_nonneg zero_le_two $ λ ε hε, le_of_not_lt $ λ h,
  zero_ne_one $ hε.symm.trans $ convex_mod_of_two_lt E h

variables {E} [normed_space ℝ E]

lemma convex_mod_of_nonpos' {x : E} (hx : ∥x∥ = 1) (hε : ε ≤ 0) : convex_mod E ε = 0 :=
begin
  refine tsub_eq_zero_of_le _,
  refine (nnreal.le_div_iff zero_lt_two.ne').2 _,
  refine le_csupr_of_le (convex_mod_set_bdd_above _ _)
    ⟨(x, x), hx.le, hx.le, hε.trans dist_nonneg⟩ (le_of_eq $ nnreal.coe_injective _),
  simp only [←two_smul ℝ, norm_smul, hx, one_mul, subtype.coe_mk, coe_nnnorm, norm_two, mul_one],
  refl,
end

lemma convex_mod_eq_one_sub_supr_sphere :
  convex_mod E ε = 1 - (⨆ (x : E) (hx : ∥x∥ = 1) (y : E) (hy : ∥y∥ = 1) (hxy : ε ≤ dist x y),
    ∥x + y∥₊) / 2 :=
begin
  sorry
  -- congr' 2,
end

@[simp] lemma convex_mod_eq_zero_iff : convex_mod E ε = 0 ↔ ε ≤ convex_char E :=
sorry

@[simp] lemma convex_mod_pos_iff : 0 < convex_mod E ε ↔ convex_char E < ε :=
sorry

end semi_normed_group

section normed_division_ring
variables (E) [normed_division_ring E] [normed_space ℝ E]

lemma convex_mod_of_nonpos (hε : ε ≤ 0) : convex_mod E ε = 0 := convex_mod_of_nonpos' norm_one hε
@[simp] lemma convex_mod_zero : convex_mod E 0 = 0 := convex_mod_of_nonpos _ le_rfl

end normed_division_ring
