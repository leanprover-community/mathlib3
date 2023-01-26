/-
Copyright (c) 2023 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import analysis.bounded_variation
import tactic.swap_var
/-!
# Constant speed

This file defines the notion of constant (and unit) speed for a function `f : ℝ → E` with
pseudo-emetric structure on `E` with respect to a set `s : set ℝ` and "speed" `l : ℝ≥0`, and shows
that if `f` has locally bounded variation on `s`, it can be obtained (up to distance zero, on `s`),
as a composite `φ ∘ (variation_on_from_to f s a)`, where `φ` has unit speed and `a ∈ s`.

## Main definitions

* `has_constant_speed_on_with f s l`, stating that the speed of `f` on `s` is `l`.
* `has_unit_speed_on f s`, stating that the speed of `f` on `s` is `1`.
* `natural_parameterization f s a : ℝ → E`, the unit speed reparameterization of `f` on `s` relative
  to `a`.

## Main statements

* `unique_unit_speed_on_Icc_zero` proves that if `f` and `f ∘ φ` are both naturally
  parameterized on closed intervals starting at `0`, then `φ` must be the identity on
  those intervals.
* `edist_natural_parameterization_eq_zero` proves that if `f` has locally bounded variation, then
  precomposing `natural_parameterization f s a` with `variation_on_from_to f s a` yields a function
  at distance zero from `f` on `s`.
* `has_unit_speed_natural_parameterization` proves that if `f` has locally bounded
  variation, then `natural_parameterization f s a` has unit speed on `s`.

## Tags

arc-length, parameterization
-/

open_locale big_operators nnreal ennreal
open set measure_theory classical

variables {α : Type*} [linear_order α] {E : Type*} [pseudo_emetric_space E]
variables (f : ℝ → E) (s : set ℝ) (l : ℝ≥0)

/--
`f` has constant speed `l` on `s` if the variation of `f` on `s ∩ Icc x y` is equal to
`l * (y - x)` for any `x y` in `s`.
-/
def has_constant_speed_on_with :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x))

variables {f} {s} {l}

lemma has_constant_speed_on_with.has_locally_bounded_variation_on
  (h : has_constant_speed_on_with f s l) : has_locally_bounded_variation_on f s := λ x y hx hy,
by simp only [has_bounded_variation_on, h hx hy, ne.def, ennreal.of_real_ne_top, not_false_iff]

lemma has_constant_speed_on_with_of_subsingleton
  (f : ℝ → E) {s : set ℝ} (hs : s.subsingleton) (l : ℝ≥0) : has_constant_speed_on_with f s l :=
begin
  rintro x hx y hy, cases hs hx hy,
  rw evariation_on.subsingleton f (λ y hy z hz, hs hy.1 hz.1 : (s ∩ Icc x x).subsingleton),
  simp only [sub_self, mul_zero, ennreal.of_real_zero],
end

lemma has_constant_speed_on_with_iff_ordered :
  has_constant_speed_on_with f s l ↔
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), (x ≤ y) →
    evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x)) :=
begin
  refine ⟨λ h x xs y ys xy, h xs ys, λ h x xs y ys, _⟩,
  rcases le_total x y with xy|yx,
  { exact h xs ys xy, },
  { rw [evariation_on.subsingleton, ennreal.of_real_of_nonpos],
    { exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx), },
    { rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩,
      cases le_antisymm (zy.trans yx) xz,
      cases le_antisymm (wy.trans yx) xw,
      refl, }, },
end

lemma has_constant_speed_on_with_iff_variation_on_from_to_eq :
  has_constant_speed_on_with f s l ↔ (has_locally_bounded_variation_on f s ∧
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), variation_on_from_to f s x y = l * (y - x)) :=
begin
  split,
  { rintro h, refine ⟨h.has_locally_bounded_variation_on, λ x xs y ys, _⟩,
    rw has_constant_speed_on_with_iff_ordered at h,
    rcases le_total x y with xy|yx,
    { rw [variation_on_from_to.eq_of_le f s xy, h xs ys xy,
          ennreal.to_real_of_real (mul_nonneg l.prop (sub_nonneg.mpr xy))], },
    { rw [variation_on_from_to.eq_of_ge f s yx, h ys xs yx,
          ennreal.to_real_of_real  (mul_nonneg l.prop (sub_nonneg.mpr yx)),
          mul_comm ↑l, mul_comm ↑l, ←neg_mul, neg_sub], }, },
  { rw has_constant_speed_on_with_iff_ordered,
    rintro h x xs y ys xy,
    rw [←h.2 xs ys, variation_on_from_to.eq_of_le f s xy,
        ennreal.of_real_to_real (h.1 x y xs ys)], },
end

lemma has_constant_speed_on_with.union {t : set ℝ}
  (hfs : has_constant_speed_on_with f s l) (hft : has_constant_speed_on_with f t l)
  {x : ℝ} (hs : is_greatest s x) (ht : is_least t x) : has_constant_speed_on_with f (s ∪ t) l :=
begin
  rw has_constant_speed_on_with_iff_ordered at hfs hft ⊢,
  rintro z (zs|zt) y (ys|yt) zy,
  { have : (s ∪ t) ∩ Icc z y = (s ∩ Icc z y), by
    { ext w, split,
      { rintro ⟨(ws|wt), zw, wy⟩,
        { exact ⟨ws, zw, wy⟩, },
        { exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 wt)).symm ▸ hs.1, zw, wy⟩, }, },
      { rintro ⟨ws, zwy⟩, exact ⟨or.inl ws, zwy⟩, }, },
    rw [this, hfs zs ys zy], },
  { have : (s ∪ t) ∩ Icc z y = (s ∩ Icc z x) ∪ (t ∩ Icc x y), by
    { ext w, split,
      { rintro ⟨(ws|wt), zw, wy⟩,
        exacts [or.inl ⟨ws, zw, hs.2 ws⟩, or.inr ⟨wt, ht.2 wt, wy⟩], },
      { rintro (⟨ws, zw, wx⟩|⟨wt, xw, wy⟩),
        exacts [⟨or.inl ws, zw, wx.trans (ht.2 yt)⟩, ⟨or.inr wt, (hs.2 zs).trans xw, wy⟩], }, },
    rw [this,
        @evariation_on.union _ _ _ _ f _ _ x,
        hfs zs hs.1 (hs.2 zs), hft ht.1 yt (ht.2 yt),
        ←ennreal.of_real_add (mul_nonneg l.prop (sub_nonneg.mpr (hs.2 zs)))
                             (mul_nonneg l.prop (sub_nonneg.mpr (ht.2 yt))) ],
    ring_nf,
    exacts [⟨⟨hs.1, hs.2 zs, le_rfl⟩, λ w ⟨ws, zw, wx⟩, wx⟩,
            ⟨⟨ht.1, le_rfl, ht.2 yt⟩, λ w ⟨wt, xw, wy⟩, xw⟩], },
  { cases le_antisymm zy ((hs.2 ys).trans (ht.2 zt)),
    simp only [Icc_self, sub_self, mul_zero, ennreal.of_real_zero],
    exact evariation_on.subsingleton _ (λ _ ⟨_, uz⟩ _ ⟨_, vz⟩, uz.trans vz.symm), },
  { have : (s ∪ t) ∩ Icc z y = (t ∩ Icc z y), by
    { ext w, split,
      { rintro ⟨(ws|wt), zw, wy⟩,
        { exact ⟨(le_antisymm ((ht.2 zt).trans zw) (hs.2 ws)) ▸ ht.1, zw, wy⟩, },
        { exact ⟨wt, zw, wy⟩, }, },
      { rintro ⟨wt, zwy⟩, exact ⟨or.inr wt, zwy⟩, }, },
    rw [this, hft zt yt zy], }
end

lemma has_constant_speed_on_with.Icc_Icc {x y z : ℝ}
  (hfs : has_constant_speed_on_with f (Icc x y) l)
  (hft : has_constant_speed_on_with f (Icc y z) l) : has_constant_speed_on_with f (Icc x z) l :=
begin
  rcases le_total x y with xy|yx,
  rcases le_total y z with yz|zy,
  { rw ←set.Icc_union_Icc_eq_Icc xy yz,
    exact hfs.union hft (is_greatest_Icc xy) (is_least_Icc yz), },
  { rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩,
    rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz,
        ←hfs ⟨xu, uz.trans zy⟩ ⟨xv, vz.trans zy⟩,
        Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right (vz.trans zy)], },
  { rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩,
    rw [Icc_inter_Icc, sup_of_le_right xu, inf_of_le_right vz,
        ←hft ⟨yx.trans xu, uz⟩ ⟨yx.trans xv, vz⟩,
        Icc_inter_Icc, sup_of_le_right (yx.trans xu), inf_of_le_right (vz)], },
end

lemma has_constant_speed_on_with_zero_iff :
  has_constant_speed_on_with f s 0 ↔ ∀ x y ∈ s, edist (f x) (f y) = 0 :=
begin
  dsimp [has_constant_speed_on_with],
  simp only [zero_mul, ennreal.of_real_zero, ←evariation_on.eq_zero_iff],
  split,
  { by_contra',
    obtain ⟨h, hfs⟩ := this,
    simp_rw evariation_on.eq_zero_iff at hfs h,
    push_neg at hfs,
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs,
    rcases le_total x y with xy|yx,
    { exact hxy (h xs ys x ⟨xs, le_rfl, xy⟩ y ⟨ys, xy, le_rfl⟩), },
    { rw edist_comm at hxy,
      exact hxy (h ys xs y ⟨ys, le_rfl, yx⟩ x ⟨xs, yx, le_rfl⟩), }, },
  { rintro h x xs y ys,
    refine le_antisymm _ (zero_le'),
    rw ←h,
    exact evariation_on.mono f (inter_subset_left s (Icc x y)), },
end

lemma has_constant_speed_on_with.ratio {l' : ℝ≥0} (hl' : l' ≠ 0) {φ : ℝ → ℝ}
  (φm : monotone_on φ s)
  (hfφ : has_constant_speed_on_with (f ∘ φ) s l)
  (hf : has_constant_speed_on_with f (φ '' s) l')
  ⦃x : ℝ⦄ (xs : x ∈ s) : eq_on φ (λ y, (l / l') * (y - x) + (φ x)) s :=
begin
  rintro y ys,
  rw [←sub_eq_iff_eq_add, mul_comm, ←mul_div_assoc,
      eq_div_iff (nnreal.coe_ne_zero.mpr hl')],
  rw has_constant_speed_on_with_iff_variation_on_from_to_eq at hf,
  rw has_constant_speed_on_with_iff_variation_on_from_to_eq at hfφ,
  symmetry,
  calc  (y - x) * l
      = l * (y - x) : by rw mul_comm
  ... = variation_on_from_to (f ∘ φ) s x y : (hfφ.2 xs ys).symm
  ... = variation_on_from_to f (φ '' s) (φ x) (φ y) :
    variation_on_from_to.comp_eq_of_monotone_on f φ φm xs ys
  ... = l' * (φ y - φ x) : hf.2 ⟨x,xs,rfl⟩ ⟨y,ys,rfl⟩
  ... = (φ y - φ x) * l' : by rw mul_comm,
end

/-- `f` has unit speed on `s` if it is linearly parameterized by `l = 1` on `s`. -/
def has_unit_speed_on (f : ℝ → E) (s : set ℝ) := has_constant_speed_on_with f s 1

lemma has_unit_speed_on.union {t : set ℝ} {x : ℝ}
  (hfs : has_unit_speed_on f s) (hft : has_unit_speed_on f t)
  (hs : is_greatest s x) (ht : is_least t x) : has_unit_speed_on f (s ∪ t) :=
has_constant_speed_on_with.union hfs hft hs ht

lemma has_unit_speed_on.Icc_Icc {x y z : ℝ}
  (hfs : has_unit_speed_on f (Icc x y)) (hft : has_unit_speed_on f (Icc y z)) :
  has_unit_speed_on f (Icc x z) :=
has_constant_speed_on_with.Icc_Icc hfs hft

/--
If both `f` and `f ∘ φ` have unit speed (on `t` and `s` respectively) and `φ`
monotonically maps `s` onto `t`, then `φ` is just a translation (on `s`).
-/
lemma unique_unit_speed {φ : ℝ → ℝ} (φm : monotone_on φ s)
  (hfφ : has_unit_speed_on (f ∘ φ) s) (hf : has_unit_speed_on f (φ '' s))
  ⦃x : ℝ⦄ (xs : x ∈ s) : eq_on φ (λ y, (y - x) + (φ x)) s :=
begin
  dsimp only [has_unit_speed_on] at hf hfφ,
  convert has_constant_speed_on_with.ratio one_ne_zero φm hfφ hf xs,
  simp only [nonneg.coe_one, div_self, ne.def, one_ne_zero, not_false_iff, one_mul],
end

/--
If both `f` and `f ∘ φ` have unit speed (on `Icc 0 t` and `Icc 0 s` respectively)
and `φ` monotonically maps `Icc 0 s` onto `Icc 0 t`, then `φ` is the identity on `Icc 0 s`
-/
lemma unique_unit_speed_on_Icc_zero {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
  {φ : ℝ → ℝ}  (φm : monotone_on φ $ Icc 0 s) (φst : φ '' (Icc 0 s) = (Icc 0 t))
  (hfφ : has_unit_speed_on (f ∘ φ) (Icc 0 s))
  (hf : has_unit_speed_on f (Icc 0 t)) : eq_on φ id (Icc 0 s) :=
begin
  rw ←φst at hf,
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩,
  have : φ 0 = 0, by
  { obtain ⟨x,xs,hx⟩ :=  φst.rec_on (surj_on_image φ (Icc 0 s)) ⟨le_rfl, ht⟩,
    exact le_antisymm (hx.rec_on (φm ⟨le_rfl,hs⟩ xs xs.1))
                      (φst.rec_on (maps_to_image φ (Icc 0 s)) (⟨le_rfl, hs⟩)).1, },
  simp only [tsub_zero, this, add_zero],
  refl,
end

/--
The natural parameterization of `f` on `s`, which, if `f` has locally bounded variation on `s`,
* has unit speed on `s`
  (by `natural_parameterization_has_unit_speed`).
* composed with `variation_on_from_to f s a`, is at distance zero from `f`
  (by `natural_parameterization_edist_zero`).
-/
noncomputable def natural_parameterization (f : α → E) (s : set α) (a : α) : ℝ → E :=
f ∘ (@function.inv_fun_on _ _ ⟨a⟩ (variation_on_from_to f s a) s)

lemma edist_natural_parameterization_eq_zero {f : α → E} {s : set α}
  (hf : has_locally_bounded_variation_on f s) {a : α} (as : a ∈ s) {b : α} (bs : b ∈ s) :
  edist (natural_parameterization f s a (variation_on_from_to f s a b)) (f b) = 0 :=
begin
  dsimp only [natural_parameterization],
  haveI : nonempty α := ⟨a⟩,
  let c := function.inv_fun_on (variation_on_from_to f s a) s (variation_on_from_to f s a b),
  obtain ⟨cs, hc⟩ := @function.inv_fun_on_pos _ _ _ s
                      (variation_on_from_to f s a) (variation_on_from_to f s a b) ⟨b, bs, rfl⟩,
  rw [variation_on_from_to.eq_left_iff hf as cs bs] at hc,
  apply variation_on_from_to.edist_zero_of_eq_zero hf cs bs hc,
end

lemma has_unit_speed_natural_parameterization (f : α → E) {s : set α}
  (hf : has_locally_bounded_variation_on f s) {a : α} (as : a ∈ s) :
  has_unit_speed_on (natural_parameterization f s a) (variation_on_from_to f s a '' s) :=
begin
  dsimp only [has_unit_speed_on],
  rw has_constant_speed_on_with_iff_ordered,
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h,
  rcases le_total c b with cb|bc,
  { rw [nnreal.coe_one, one_mul, le_antisymm h (variation_on_from_to.monotone_on hf as cs bs cb),
        sub_self, ennreal.of_real_zero, Icc_self, evariation_on.subsingleton],
    exact λ x hx y hy, hx.2.trans hy.2.symm, },
  { rw [nnreal.coe_one, one_mul, sub_eq_add_neg, variation_on_from_to.eq_neg_swap, neg_neg,
        add_comm, variation_on_from_to.add hf bs as cs, ←variation_on_from_to.eq_neg_swap f],
    rw [←evariation_on.comp_inter_Icc_eq_of_monotone_on (natural_parameterization f s a) _
        (variation_on_from_to.monotone_on hf as) bs cs],
    rw [@evariation_on.eq_of_edist_zero_on _ _ _ _ _ f],
    { rw [variation_on_from_to.eq_of_le _ _ bc, ennreal.of_real_to_real (hf b c bs cs)], },
    { rintro x ⟨xs, bx, xc⟩,
      exact edist_natural_parameterization_eq_zero hf as xs, }, },
end
