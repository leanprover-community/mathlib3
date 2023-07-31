/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import analysis.convex.combination
import analysis.convex.function

/-!
# Jensen's inequality and maximum principle for convex functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `analysis.convex.integral`.

## Main declarations

Jensen's inequalities:
* `convex_on.map_center_mass_le`, `convex_on.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `concave_on.le_map_center_mass`, `concave_on.le_map_sum`: Concave Jensen's inequality.

As corollaries, we get:
* `convex_on.exists_ge_of_mem_convex_hull `: Maximum principle for convex functions.
* `concave_on.exists_le_of_mem_convex_hull`: Minimum principle for concave functions.
-/

open finset linear_map set
open_locale big_operators classical convex pointwise

variables {𝕜 E F β ι : Type*}

/-! ### Jensen's inequality -/

section jensen
variables [linear_ordered_field 𝕜] [add_comm_group E] [ordered_add_comm_group β] [module 𝕜 E]
  [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β} {t : finset ι} {w : ι → 𝕜} {p : ι → E}

/-- Convex **Jensen's inequality**, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le (hf : convex_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
  (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
  f (t.center_mass w p) ≤ t.center_mass w (f ∘ p) :=
begin
  have hmem' : ∀ i ∈ t, (p i, (f ∘ p) i) ∈ {p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_rfl⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ h₁ hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum,
      prod.smul_snd, prod.snd_sum],
end

/-- Concave **Jensen's inequality**, `finset.center_mass` version. -/
lemma concave_on.le_map_center_mass (hf : concave_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
  (h₁ : 0 < ∑ i in t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
  t.center_mass w (f ∘ p) ≤ f (t.center_mass w p) :=
@convex_on.map_center_mass_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ _ _ _ _ _ hf h₀ h₁ hmem

/-- Convex **Jensen's inequality**, `finset.sum` version. -/
lemma convex_on.map_sum_le (hf : convex_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, p i ∈ s) :
  f (∑ i in t, w i • p i) ≤ ∑ i in t, w i • f (p i) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- Concave **Jensen's inequality**, `finset.sum` version. -/
lemma concave_on.le_map_sum (hf : concave_on 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, p i ∈ s) :
  ∑ i in t, w i • f (p i) ≤ f (∑ i in t, w i • p i) :=
@convex_on.map_sum_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ _ _ _ _ _ hf h₀ h₁ hmem

end jensen

/-! ### Maximum principle -/

section maximum_principle
variables [linear_ordered_field 𝕜] [add_comm_group E] [linear_ordered_add_comm_group β]
  [module 𝕜 E] [module 𝕜 β] [ordered_smul 𝕜 β] {s : set E} {f : E → β} {t : finset ι} {w : ι → 𝕜}
  {p : ι → E} {x : E}

lemma le_sup_of_mem_convex_hull {s : finset E} (hf : convex_on 𝕜 (convex_hull 𝕜 (s : set E)) f)
  (hx : x ∈ convex_hull 𝕜 (s : set E)) :
  f x ≤ s.sup' (coe_nonempty.1 $ convex_hull_nonempty_iff.1 ⟨x, hx⟩) f :=
begin
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convex_hull.1 hx,
  exact (hf.map_center_mass_le hw₀ (by positivity) $ subset_convex_hull _ _).trans
    (center_mass_le_sup hw₀ $ by positivity),
end

lemma inf_le_of_mem_convex_hull {s : finset E} (hf : concave_on 𝕜 (convex_hull 𝕜 (s : set E)) f)
  (hx : x ∈ convex_hull 𝕜 (s : set E)) :
  s.inf' (coe_nonempty.1 $ convex_hull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
le_sup_of_mem_convex_hull hf.dual hx

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
lemma convex_on.exists_ge_of_center_mass (h : convex_on 𝕜 s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w p) ≤ f (p i) :=
begin
  set y := t.center_mass w p,
  rsuffices ⟨i, hi, hfi⟩ : ∃ i ∈ t.filter (λ i, w i ≠ 0), w i • f y ≤ w i • (f ∘ p) i,
  { rw mem_filter at hi,
    exact ⟨i, hi.1, (smul_le_smul_iff_of_pos $ (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩ },
  have hw' : (0 : 𝕜) < ∑ i in filter (λ i, w i ≠ 0) t, w i := by rwa sum_filter_ne_zero,
  refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _,
  rw [←sum_smul, ←smul_le_smul_iff_of_pos (inv_pos.2 hw'), inv_smul_smul₀ hw'.ne',
    ←finset.center_mass, finset.center_mass_filter_ne_zero],
  exact h.map_center_mass_le hw₀ hw₁ hp,
  apply_instance,
end

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
lemma concave_on.exists_le_of_center_mass (h : concave_on 𝕜 s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i in t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
  ∃ i ∈ t, f (p i) ≤ f (t.center_mass w p) :=
@convex_on.exists_ge_of_center_mass 𝕜 E βᵒᵈ _ _ _ _ _ _ _ _ _ _ _ _ h hw₀ hw₁ hp

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then the eventual maximum of `f` on `convex_hull 𝕜 s` lies in `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull (hf : convex_on 𝕜 (convex_hull 𝕜 s) f) {x}
  (hx : x ∈ convex_hull 𝕜 s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw _root_.convex_hull_eq at hx,
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull 𝕜 s (hp i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨p i, hp i hit, Hi⟩
end

/-- Minimum principle for concave functions. If a function `f` is concave on the convex hull of `s`,
then the eventual minimum of `f` on `convex_hull 𝕜 s` lies in `s`. -/
lemma concave_on.exists_le_of_mem_convex_hull (hf : concave_on 𝕜 (convex_hull 𝕜 s) f) {x}
  (hx : x ∈ convex_hull 𝕜 s) : ∃ y ∈ s, f y ≤ f x :=
@convex_on.exists_ge_of_mem_convex_hull 𝕜 E βᵒᵈ _ _ _ _ _ _ _ _ hf _ hx

end maximum_principle
