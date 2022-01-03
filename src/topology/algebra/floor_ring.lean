/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import algebra.order.floor
import topology.algebra.ordered.basic

/-!
# Topological facts about `int.floor`, `int.ceil` and `int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_at_top`, `tendsto_floor_at_bot`, `tendsto_ceil_at_top`, `tendsto_ceil_at_bot`:
  `int.floor` and `int.ceil` tend to +-∞ in +-∞.
* `continuous_on_floor`: `int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuous_on_ceil`: `int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuous_on_fract`: `int.fract` is continuous on `Ico n (n + 1)`.
* `continuous_on.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `int.fract` yields another continuous function.
-/

open filter function int set
open_locale topological_space

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

lemma tendsto_floor_at_top : tendsto (floor : α → ℤ) at_top at_top :=
floor_mono.tendsto_at_top_at_top $ λ b, ⟨(b + 1 : ℤ), by { rw floor_coe, exact (lt_add_one _).le }⟩

lemma tendsto_floor_at_bot : tendsto (floor : α → ℤ) at_bot at_bot :=
floor_mono.tendsto_at_bot_at_bot $ λ b, ⟨b, (floor_coe _).le⟩

lemma tendsto_ceil_at_top : tendsto (ceil : α → ℤ) at_top at_top :=
ceil_mono.tendsto_at_top_at_top $ λ b, ⟨b, (ceil_coe _).ge⟩

lemma tendsto_ceil_at_bot : tendsto (ceil : α → ℤ) at_bot at_bot :=
ceil_mono.tendsto_at_bot_at_bot $ λ b, ⟨(b - 1 : ℤ), by { rw ceil_coe, exact (sub_one_lt _).le }⟩

variables [topological_space α]

lemma continuous_on_floor (n : ℤ) : continuous_on (λ x, floor x : α → α) (Ico n (n+1) : set α) :=
(continuous_on_congr $ floor_eq_on_Ico' n).mpr continuous_on_const

lemma continuous_on_ceil (n : ℤ) : continuous_on (λ x, ceil x : α → α) (Ioc (n-1) n : set α) :=
(continuous_on_congr $ ceil_eq_on_Ioc' n).mpr continuous_on_const

lemma tendsto_floor_right' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Ici (lt_add_one (n : α)),
  simpa only [floor_coe] using
    (continuous_on_floor n _ (left_mem_Ico.mpr $ lt_add_one (_ : α))).tendsto
end

lemma tendsto_ceil_left' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
begin
  rw ← nhds_within_Ioc_eq_nhds_within_Iic (sub_one_lt (n : α)),
  simpa only [ceil_coe] using
    (continuous_on_ceil _ _ (right_mem_Ioc.mpr $ sub_one_lt (_ : α))).tendsto
end

lemma tendsto_floor_right [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_floor_right' _)
begin
  refine (eventually_nhds_within_of_forall $ λ x (hx : (n : α) ≤ x), _),
  change _ ≤ _,
  norm_cast,
  convert ← floor_mono hx,
  rw floor_eq_iff,
  exact ⟨le_refl _, lt_add_one _⟩
end

lemma tendsto_ceil_left [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ (tendsto_ceil_left' _)
begin
  refine (eventually_nhds_within_of_forall $ λ x (hx : x ≤ (n : α)), _),
  change _ ≤ _,
  norm_cast,
  convert ← ceil_mono hx,
  rw ceil_eq_iff,
  exact ⟨sub_one_lt _, le_refl _⟩
end

lemma tendsto_floor_left [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[<] n) (𝓝[≤] (n-1)) :=
begin
  rw ← nhds_within_Ico_eq_nhds_within_Iio (sub_one_lt (n : α)),
  convert (tendsto_nhds_within_congr $ (λ x hx, (floor_eq_on_Ico' (n-1) x hx).symm))
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
      (eventually_of_forall (λ _, mem_Iic.mpr $ le_refl _)));
  norm_cast <|> apply_instance,
  ring
end

lemma tendsto_ceil_right [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n+1)) :=
begin
  rw ← nhds_within_Ioc_eq_nhds_within_Ioi (lt_add_one (n : α)),
  convert (tendsto_nhds_within_congr $ (λ x hx, (ceil_eq_on_Ioc' (n+1) x hx).symm))
    (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ tendsto_const_nhds
      (eventually_of_forall (λ _, mem_Ici.mpr $ le_refl _)));
  norm_cast <|> apply_instance,
  ring
end

lemma tendsto_floor_left' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, floor x : α → α) (𝓝[<] n) (𝓝 (n-1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_floor_left n),
end

lemma tendsto_ceil_right' [order_closed_topology α] (n : ℤ) :
  tendsto (λ x, ceil x : α → α) (𝓝[>] n) (𝓝 (n+1)) :=
begin
  rw ← nhds_within_univ,
  exact tendsto_nhds_within_mono_right (subset_univ _) (tendsto_ceil_right n),
end

lemma continuous_on_fract [topological_add_group α] (n : ℤ) :
  continuous_on (fract : α → α) (Ico n (n+1) : set α) :=
continuous_on_id.sub (continuous_on_floor n)

lemma tendsto_fract_left' [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_left' n);
  [{norm_cast, ring}, apply_instance, apply_instance]
end

lemma tendsto_fract_left [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  (tendsto_fract_left' _) (eventually_of_forall fract_lt_one)

lemma tendsto_fract_right' [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) :=
begin
  convert (tendsto_nhds_within_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n);
  [exact (sub_self _).symm, apply_instance, apply_instance]
end

lemma tendsto_fract_right [order_closed_topology α] [topological_add_group α]
  (n : ℤ) : tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  (tendsto_fract_right' _) (eventually_of_forall fract_nonneg)

local notation `I` := (Icc 0 1 : set α)

lemma continuous_on.comp_fract' {β γ : Type*} [order_topology α]
  [topological_add_group α] [topological_space β] [topological_space γ] {f : β → α → γ}
  (h : continuous_on (uncurry f) $ (univ : set β).prod I) (hf : ∀ s, f s 0 = f s 1) :
  continuous (λ st : β × α, f st.1 $ fract st.2) :=
begin
  change continuous ((uncurry f) ∘ (prod.map id (fract))),
  rw continuous_iff_continuous_at,
  rintro ⟨s, t⟩,
  by_cases ht : t = floor t,
  { rw ht,
    rw ← continuous_within_at_univ,
    have : (univ : set (β × α)) ⊆ (set.prod univ (Iio $ floor t)) ∪ (set.prod univ (Ici $ floor t)),
    { rintros p -,
      rw ← prod_union,
      exact ⟨true.intro, lt_or_le _ _⟩ },
    refine continuous_within_at.mono _ this,
    refine continuous_within_at.union _ _,
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq,
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      have : (uncurry f) (s, 0) = (uncurry f) (s, (1 : α)),
        by simp [uncurry, hf],
      rw this,
      refine (h _ ⟨true.intro, by exact_mod_cast right_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ],
      rw nhds_within_Icc_eq_nhds_within_Iic (@zero_lt_one α _ _),
      exact tendsto_id.prod_map
        (tendsto_nhds_within_mono_right Iio_subset_Iic_self $ tendsto_fract_left _) },
    { simp only [continuous_within_at, fract_coe, nhds_within_prod_eq,
                  nhds_within_univ, id.def, comp_app, prod.map_mk],
      refine (h _ ⟨true.intro, by exact_mod_cast left_mem_Icc.mpr zero_le_one⟩).tendsto.comp _,
      rw [nhds_within_prod_eq, nhds_within_univ,
        nhds_within_Icc_eq_nhds_within_Ici (@zero_lt_one α _ _)],
      exact tendsto_id.prod_map (tendsto_fract_right _) } },
  { have : t ∈ Ioo (floor t : α) ((floor t : α) + 1),
      from ⟨lt_of_le_of_ne (floor_le t) (ne.symm ht), lt_floor_add_one _⟩,
    apply (h ((prod.map _ fract) _) ⟨trivial, ⟨fract_nonneg _, (fract_lt_one _).le⟩⟩).tendsto.comp,
    simp only [nhds_prod_eq, nhds_within_prod_eq, nhds_within_univ, id.def, prod.map_mk],
    exact continuous_at_id.tendsto.prod_map
            (tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
              (((continuous_on_fract _ _ (Ioo_subset_Ico_self this)).mono
                  Ioo_subset_Ico_self).continuous_at (Ioo_mem_nhds this.1 this.2))
              (eventually_of_forall (λ x, ⟨fract_nonneg _, (fract_lt_one _).le⟩)) ) }
end

lemma continuous_on.comp_fract {β : Type*} [order_topology α]
  [topological_add_group α] [topological_space β] {f : α → β}
  (h : continuous_on f I) (hf : f 0 = f 1) : continuous (f ∘ fract) :=
begin
  let f' : unit → α → β := λ x y, f y,
  have : continuous_on (uncurry f') ((univ : set unit).prod I),
  { rintros ⟨s, t⟩ ⟨-, ht : t ∈ I⟩,
    simp only [continuous_within_at, uncurry, nhds_within_prod_eq, nhds_within_univ, f'],
    rw tendsto_prod_iff,
    intros W hW,
    specialize h t ht hW,
    rw mem_map_iff_exists_image at h,
    rcases h with ⟨V, hV, hVW⟩,
    rw image_subset_iff at hVW,
    use [univ, univ_mem, V, hV],
    intros x y hx hy,
    exact hVW hy },
  have key : continuous (λ s, ⟨unit.star, s⟩ : α → unit × α) := by continuity,
  exact (this.comp_fract' (λ s, hf)).comp key
end
