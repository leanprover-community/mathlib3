/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.instances.ennreal
import data.real.ereal

noncomputable theory

open classical set filter metric
open_locale classical topological_space ennreal nnreal big_operators filter

variables {α : Type*} [topological_space α]

namespace ereal


section topological_space
open topological_space


instance : topological_space ereal := preorder.topology ereal

instance : order_topology ereal := ⟨rfl⟩

instance : t2_space ereal := by apply_instance

instance : second_countable_topology ereal :=
⟨begin
  refine ⟨⋃ (q : ℚ), {{a : ereal | a < (q : ℝ)}, {a : ereal | ((q : ℝ) : ereal) < a}},
    countable_Union (λ a, (countable_singleton _).insert _), _⟩,
  refine le_antisymm
    (le_generate_from $ by simp [or_imp_distrib, is_open_lt', is_open_gt'] {contextual := tt}) _,
  apply le_generate_from (λ s h, _),
  rcases h with ⟨a, hs | hs⟩;
  [ rw show s = ⋃q∈{q:ℚ | a < (q : ℝ)}, {b | ((q : ℝ) : ereal) < b},
      by { ext x, simpa only [hs, exists_prop, mem_Union] using a.lt_iff_exists_rat_btwn x},
    rw show s = ⋃q∈{q:ℚ | ((q : ℝ) : ereal) < a}, {b | b < ((q : ℝ) : ereal)},
      by { ext x, simpa only [hs, and_comm, exists_prop, mem_Union]
        using x.lt_iff_exists_rat_btwn a, }];
  { apply is_open_Union, intro q,
    apply is_open_Union, intro hq,
    apply generate_open.basic,
    exact mem_Union.2 ⟨q, by simp⟩ },
end⟩

lemma ereal_cases : ∀ (a : ereal), a = ⊥ ∨ (∃ (x : ℝ), a = x) ∨ a = ⊤
| ⊤ := by simp
| ⊥ := by simp
| (a : ℝ) := by simp

lemma embedding_coe : embedding (coe : ℝ → ereal) :=
⟨⟨begin
  refine le_antisymm _ _,
  { rw [@order_topology.topology_eq_generate_intervals ereal _,
      ← coinduced_le_iff_le_induced],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : ℝ | a < ↑b},
    { rcases ereal_cases a with rfl|⟨x, rfl⟩|rfl,
      { simp only [is_open_univ, bot_lt_coe, set_of_true] },
      { simp only [ereal.coe_real_lt], exact is_open_Ioi },
      { simp only [set_of_false, is_open_empty, not_top_lt] } },
    show is_open {b : ℝ | ↑b < a},
    { rcases ereal_cases a with rfl|⟨x, rfl⟩|rfl,
      { simp only [not_lt_bot, set_of_false, is_open_empty] },
      { simp only [ereal.coe_real_lt], exact is_open_Iio },
      { simp only [is_open_univ, coe_lt_top, set_of_true]} } },
  { rw [@order_topology.topology_eq_generate_intervals ℝ _],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨Ioi a, is_open_Ioi, by simp [Ioi]⟩,
    exact ⟨Iio a, is_open_Iio, by simp [Iio]⟩ }
  end⟩,
  assume a b, by simp only [imp_self, ereal.coe_real_inj']⟩

lemma open_embedding_coe : open_embedding (coe : ℝ → ereal) :=
⟨embedding_coe,
begin
  convert @is_open_Ioo ereal _ _ _ ⊥ ⊤,
  ext x,
  rcases ereal_cases x with rfl|⟨y, rfl⟩|rfl,
  { simp only [left_mem_Ioo, mem_range, (bot_ne_coe _).symm, exists_false, not_false_iff] },
  { simp only [mem_range_self, mem_Ioo, bot_lt_coe, coe_lt_top, and_self] },
  { simp only [mem_range, right_mem_Ioo, exists_false, coe_ne_top] }
end⟩

@[norm_cast] lemma tendsto_coe {f : filter α} {m : α → ℝ} {a : ℝ} :
  tendsto (λ a, (m a : ereal)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coe.tendsto_nhds_iff.symm

lemma continuous_coe : continuous (coe : ℝ → ereal) :=
embedding_coe.continuous

lemma continuous_coe_iff {f : α → ℝ} :
  continuous (λa, (f a : ereal)) ↔ continuous f :=
embedding_coe.continuous_iff.symm

lemma nhds_coe {r : ℝ} : 𝓝 (r : ereal) = (𝓝 r).map coe :=
(open_embedding_coe.map_nhds_eq r).symm

lemma nhds_coe_coe {r p : ℝ} :
  𝓝 ((r : ereal), (p : ereal)) = (𝓝 (r, p)).map (λp:ℝ × ℝ, (p.1, p.2)) :=
((open_embedding_coe.prod open_embedding_coe).map_nhds_eq (r, p)).symm

lemma nhds_top : 𝓝 (⊤ : ereal) = ⨅ a ≠ ⊤, 𝓟 (Ioi a) :=
nhds_top_order.trans $ by simp [lt_top_iff_ne_top, Ioi]

lemma nhds_top' : 𝓝 (⊤ : ereal) = ⨅ a : ℝ, 𝓟 (Ioi a) :=
begin
  rw [nhds_top],
  apply le_antisymm,
  { exact infi_le_infi2 (λ x, ⟨x, by simp⟩) },
  { refine le_infi (λ r, le_infi (λ hr, _)),
    rcases ereal_cases r with rfl|⟨x, rfl⟩|rfl,
    { exact (infi_le _ 0).trans (by simp) },
    { exact infi_le _ _ },
    { simpa using hr, } }
end

lemma tendsto_nhds_top_iff_real {m : α → ereal} {f : filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
by simp only [nhds_top', mem_Ioi, tendsto_infi, tendsto_principal]

lemma continuous_at_add_of_real (a b :ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (a, b) :=
by simp only [continuous_at, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (∘),
    tendsto_coe, tendsto_add]

lemma tendsto_coe_add_at_top (y : ℝ) :
  tendsto (λ (x : ereal), x + y) (𝓝 ⊤) (𝓝 ⊤) :=
begin
  simp [tendsto_nhds_top_iff_real],
  assume x,
  simp [nhds_top'],
end

#exit

lemma continuous_at_add_top (a : ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (⊤, a) :=
begin
  exact tendsto_nhds_top_mono' continuous_at_fst (λ p, le_add_right le_rfl)
end

end
