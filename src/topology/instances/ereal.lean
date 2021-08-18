/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.instances.ennreal
import data.real.ereal

/-!
# Topological structure on `ereal`

We endow `ereal` with the order topology, and prove basic properties of this topology.

## Main results

* `coe : ℝ → ereal` is an open embedding
* `coe : ℝ≥0∞ → ereal` is an embedding
* The addition on `ereal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `ereal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

noncomputable theory

open classical set filter metric topological_space
open_locale classical topological_space ennreal nnreal big_operators filter

variables {α : Type*} [topological_space α]

namespace ereal

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
      by { ext x, simpa only [hs, exists_prop, mem_Union] using lt_iff_exists_rat_btwn },
    rw show s = ⋃q∈{q:ℚ | ((q : ℝ) : ereal) < a}, {b | b < ((q : ℝ) : ereal)},
      by { ext x, simpa only [hs, and_comm, exists_prop, mem_Union] using lt_iff_exists_rat_btwn }];
  { apply is_open_Union, intro q,
    apply is_open_Union, intro hq,
    apply generate_open.basic,
    exact mem_Union.2 ⟨q, by simp⟩ },
end⟩


/-! ### Real coercion -/

lemma embedding_coe : embedding (coe : ℝ → ereal) :=
⟨⟨begin
  refine le_antisymm _ _,
  { rw [@order_topology.topology_eq_generate_intervals ereal _,
      ← coinduced_le_iff_le_induced],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : ℝ | a < ↑b},
    { rcases a.cases with rfl|⟨x, rfl⟩|rfl,
      { simp only [is_open_univ, bot_lt_coe, set_of_true] },
      { simp only [ereal.coe_lt_coe_iff], exact is_open_Ioi },
      { simp only [set_of_false, is_open_empty, not_top_lt] } },
    show is_open {b : ℝ | ↑b < a},
    { rcases a.cases with rfl|⟨x, rfl⟩|rfl,
      { simp only [not_lt_bot, set_of_false, is_open_empty] },
      { simp only [ereal.coe_lt_coe_iff], exact is_open_Iio },
      { simp only [is_open_univ, coe_lt_top, set_of_true] } } },
  { rw [@order_topology.topology_eq_generate_intervals ℝ _],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨Ioi a, is_open_Ioi, by simp [Ioi]⟩,
    exact ⟨Iio a, is_open_Iio, by simp [Iio]⟩ }
  end⟩,
  assume a b, by simp only [imp_self, ereal.coe_eq_coe_iff]⟩

lemma open_embedding_coe : open_embedding (coe : ℝ → ereal) :=
⟨embedding_coe,
begin
  convert @is_open_Ioo ereal _ _ _ ⊥ ⊤,
  ext x,
  rcases x.cases with rfl|⟨y, rfl⟩|rfl,
  { simp only [left_mem_Ioo, mem_range, coe_ne_bot, exists_false, not_false_iff] },
  { simp only [mem_range_self, mem_Ioo, bot_lt_coe, coe_lt_top, and_self] },
  { simp only [mem_range, right_mem_Ioo, exists_false, coe_ne_top] }
end⟩

@[norm_cast] lemma tendsto_coe {α : Type*} {f : filter α} {m : α → ℝ} {a : ℝ} :
  tendsto (λ a, (m a : ereal)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coe.tendsto_nhds_iff.symm

lemma _root_.continuous_coe_real_ereal : continuous (coe : ℝ → ereal) :=
embedding_coe.continuous

lemma continuous_coe_iff {f : α → ℝ} :
  continuous (λa, (f a : ereal)) ↔ continuous f :=
embedding_coe.continuous_iff.symm

lemma nhds_coe {r : ℝ} : 𝓝 (r : ereal) = (𝓝 r).map coe :=
(open_embedding_coe.map_nhds_eq r).symm

lemma nhds_coe_coe {r p : ℝ} :
  𝓝 ((r : ereal), (p : ereal)) = (𝓝 (r, p)).map (λp:ℝ × ℝ, (p.1, p.2)) :=
((open_embedding_coe.prod open_embedding_coe).map_nhds_eq (r, p)).symm

lemma tendsto_to_real {a : ereal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
  tendsto ereal.to_real (𝓝 a) (𝓝 a.to_real) :=
begin
  lift a to ℝ using and.intro ha h'a,
  rw [nhds_coe, tendsto_map'_iff],
  exact tendsto_id
end

lemma continuous_on_to_real : continuous_on ereal.to_real ({⊥, ⊤} : set ereal).compl :=
λ a ha, continuous_at.continuous_within_at (tendsto_to_real
  (by { simp [not_or_distrib] at ha, exact ha.2 }) (by { simp [not_or_distrib] at ha, exact ha.1 }))

/-- The set of finite `ereal` numbers is homeomorphic to `ℝ`. -/
def ne_bot_top_homeomorph_real : ({⊥, ⊤} : set ereal).compl ≃ₜ ℝ :=
{ continuous_to_fun := continuous_on_iff_continuous_restrict.1 continuous_on_to_real,
  continuous_inv_fun := continuous_subtype_mk _ continuous_coe_real_ereal,
  .. ne_top_bot_equiv_real }


/-! ### ennreal coercion -/

lemma embedding_coe_ennreal : embedding (coe : ℝ≥0∞ → ereal) :=
⟨⟨begin
  refine le_antisymm _ _,
  { rw [@order_topology.topology_eq_generate_intervals ereal _,
      ← coinduced_le_iff_le_induced],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    show is_open {b : ℝ≥0∞ | a < ↑b},
    { rcases a.cases with rfl|⟨x, rfl⟩|rfl,
      { simp only [is_open_univ, bot_lt_coe_ennreal, set_of_true] },
      { rcases le_or_lt 0 x with h|h,
        { have : (x : ereal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl,
          rw this,
          simp only [id.def, coe_ennreal_lt_coe_ennreal_iff],
          exact is_open_Ioi, },
        { have : ∀ (y : ℝ≥0∞), (x : ereal) < y := λ y,
            (ereal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg _),
          simp only [this, is_open_univ, set_of_true] } },
      { simp only [set_of_false, is_open_empty, not_top_lt] } },
    show is_open {b : ℝ≥0∞ | ↑b < a},
    { rcases a.cases with rfl|⟨x, rfl⟩|rfl,
      { simp only [not_lt_bot, set_of_false, is_open_empty] },
      { rcases le_or_lt 0 x with h|h,
        { have : (x : ereal) = ((id ⟨x, h⟩ : ℝ≥0) : ℝ≥0∞) := rfl,
          rw this,
          simp only [id.def, coe_ennreal_lt_coe_ennreal_iff],
          exact is_open_Iio, },
        { convert is_open_empty,
          apply eq_empty_iff_forall_not_mem.2 (λ y hy, lt_irrefl (x : ereal) _),
          exact ((ereal.coe_lt_coe_iff.2 h).trans_le (coe_ennreal_nonneg y)).trans hy } },
      { simp only [← coe_ennreal_top, coe_ennreal_lt_coe_ennreal_iff],
        exact is_open_Iio } } },
  { rw [@order_topology.topology_eq_generate_intervals ℝ≥0∞ _],
    refine le_generate_from (assume s ha, _),
    rcases ha with ⟨a, rfl | rfl⟩,
    exact ⟨Ioi a, is_open_Ioi, by simp [Ioi]⟩,
    exact ⟨Iio a, is_open_Iio, by simp [Iio]⟩ }
  end⟩,
  assume a b, by simp only [imp_self, coe_ennreal_eq_coe_ennreal_iff]⟩

@[norm_cast] lemma tendsto_coe_ennreal {α : Type*} {f : filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
  tendsto (λ a, (m a : ereal)) f (𝓝 ↑a) ↔ tendsto m f (𝓝 a) :=
embedding_coe_ennreal.tendsto_nhds_iff.symm

lemma _root_.continuous_coe_ennreal_ereal : continuous (coe : ℝ≥0∞ → ereal) :=
embedding_coe_ennreal.continuous

lemma continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
  continuous (λa, (f a : ereal)) ↔ continuous f :=
embedding_coe_ennreal.continuous_iff.symm


/-! ### Neighborhoods of infinity -/

lemma nhds_top : 𝓝 (⊤ : ereal) = ⨅ a ≠ ⊤, 𝓟 (Ioi a) :=
nhds_top_order.trans $ by simp [lt_top_iff_ne_top, Ioi]

lemma nhds_top' : 𝓝 (⊤ : ereal) = ⨅ a : ℝ, 𝓟 (Ioi a) :=
begin
  rw [nhds_top],
  apply le_antisymm,
  { exact infi_le_infi2 (λ x, ⟨x, by simp⟩) },
  { refine le_infi (λ r, le_infi (λ hr, _)),
    rcases r.cases with rfl|⟨x, rfl⟩|rfl,
    { exact (infi_le _ 0).trans (by simp) },
    { exact infi_le _ _ },
    { simpa using hr, } }
end

lemma mem_nhds_top_iff {s : set ereal} :
  s ∈ 𝓝 (⊤ : ereal) ↔ ∃ (y : ℝ), Ioi (y : ereal) ⊆ s :=
begin
  rw [nhds_top', mem_infi_of_directed],
  { refl },
  exact λ x y, ⟨max x y, by simp [le_refl], by simp [le_refl]⟩,
end

lemma tendsto_nhds_top_iff_real {α : Type*} {m : α → ereal} {f : filter α} :
  tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
by simp only [nhds_top', mem_Ioi, tendsto_infi, tendsto_principal]

lemma nhds_bot : 𝓝 (⊥ : ereal) = ⨅ a ≠ ⊥, 𝓟 (Iio a) :=
nhds_bot_order.trans $ by simp [bot_lt_iff_ne_bot]

lemma nhds_bot' : 𝓝 (⊥ : ereal) = ⨅ a : ℝ, 𝓟 (Iio a) :=
begin
  rw [nhds_bot],
  apply le_antisymm,
  { exact infi_le_infi2 (λ x, ⟨x, by simp⟩) },
  { refine le_infi (λ r, le_infi (λ hr, _)),
    rcases r.cases with rfl|⟨x, rfl⟩|rfl,
    { simpa using hr },
    { exact infi_le _ _ },
    { exact (infi_le _ 0).trans (by simp) } }
end

lemma mem_nhds_bot_iff {s : set ereal} :
  s ∈ 𝓝 (⊥ : ereal) ↔ ∃ (y : ℝ), Iio (y : ereal) ⊆ s :=
begin
  rw [nhds_bot', mem_infi_of_directed],
  { refl },
  exact λ x y, ⟨min x y, by simp [le_refl], by simp [le_refl]⟩,
end

lemma tendsto_nhds_bot_iff_real {α : Type*} {m : α → ereal} {f : filter α} :
  tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x :=
by simp only [nhds_bot', mem_Iio, tendsto_infi, tendsto_principal]


/-! ### Continuity of addition -/

lemma continuous_at_add_coe_coe (a b :ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (a, b) :=
by simp only [continuous_at, nhds_coe_coe, ← coe_add, tendsto_map'_iff, (∘),
    tendsto_coe, tendsto_add]

lemma continuous_at_add_top_coe (a : ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (⊤, a) :=
begin
  simp only [continuous_at, tendsto_nhds_top_iff_real, top_add, nhds_prod_eq],
  assume r,
  rw eventually_prod_iff,
  refine ⟨λ z, ((r - (a - 1): ℝ) : ereal) < z, Ioi_mem_nhds (coe_lt_top _),
          λ z, ((a - 1 : ℝ) : ereal) < z, Ioi_mem_nhds (by simp [zero_lt_one]),
          λ x hx y hy, _⟩,
  dsimp,
  convert add_lt_add hx hy,
  simp,
end

lemma continuous_at_add_coe_top (a : ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (a, ⊤) :=
begin
  change continuous_at ((λ (p : ereal × ereal), p.2 + p.1) ∘ prod.swap) (a, ⊤),
  apply continuous_at.comp _ continuous_swap.continuous_at,
  simp_rw add_comm,
  exact continuous_at_add_top_coe a
end

lemma continuous_at_add_top_top :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (⊤, ⊤) :=
begin
  simp only [continuous_at, tendsto_nhds_top_iff_real, top_add, nhds_prod_eq],
  assume r,
  rw eventually_prod_iff,
  refine ⟨λ z, (r : ereal) < z, Ioi_mem_nhds (coe_lt_top _),
          λ z, ((0 : ℝ) : ereal) < z, Ioi_mem_nhds (by simp [zero_lt_one]),
          λ x hx y hy, _⟩,
  dsimp,
  convert add_lt_add hx hy,
  simp,
end

lemma continuous_at_add_bot_coe (a : ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (⊥, a) :=
begin
  simp only [continuous_at, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add_coe],
  assume r,
  rw eventually_prod_iff,
  refine ⟨λ z, z < ((r - (a + 1): ℝ) : ereal), Iio_mem_nhds (bot_lt_coe _),
          λ z, z < ((a + 1 : ℝ) : ereal), Iio_mem_nhds (by simp [-coe_add, zero_lt_one]),
          λ x hx y hy, _⟩,
  dsimp,
  convert add_lt_add hx hy,
  dsimp,
  ring,
end

lemma continuous_at_add_coe_bot (a : ℝ) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (a, ⊥) :=
begin
  change continuous_at ((λ (p : ereal × ereal), p.2 + p.1) ∘ prod.swap) (a, ⊥),
  apply continuous_at.comp _ continuous_swap.continuous_at,
  simp_rw add_comm,
  exact continuous_at_add_bot_coe a
end

lemma continuous_at_add_bot_bot :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) (⊥, ⊥) :=
begin
  simp only [continuous_at, tendsto_nhds_bot_iff_real, nhds_prod_eq, bot_add_bot],
  assume r,
  rw eventually_prod_iff,
  refine ⟨λ z, z < r, Iio_mem_nhds (bot_lt_coe _),
          λ z, z < 0, Iio_mem_nhds (bot_lt_coe _),
          λ x hx y hy, _⟩,
  dsimp,
  convert add_lt_add hx hy,
  simp
end

/-- The addition on `ereal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
lemma continuous_at_add {p : ereal × ereal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
  continuous_at (λ (p : ereal × ereal), p.1 + p.2) p :=
begin
  rcases p with ⟨x, y⟩,
  rcases x.cases with rfl|⟨x, rfl⟩|rfl; rcases y.cases with rfl|⟨y, rfl⟩|rfl,
  { exact continuous_at_add_bot_bot },
  { exact continuous_at_add_bot_coe _ },
  { simpa using h' },
  { exact continuous_at_add_coe_bot _ },
  { exact continuous_at_add_coe_coe _ _ },
  { exact continuous_at_add_coe_top _ },
  { simpa using h },
  { exact continuous_at_add_top_coe _ },
  { exact continuous_at_add_top_top },
end

/-! ### Negation-/

/-- Negation on `ereal` as a homeomorphism -/
def neg_homeo : ereal ≃ₜ ereal :=
neg_order_iso.to_homeomorph

lemma continuous_neg : continuous (λ (x : ereal), -x) :=
neg_homeo.continuous

end ereal
