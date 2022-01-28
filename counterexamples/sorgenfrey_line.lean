/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.real
import data.set.intervals.monotone

/-!
-/

open set filter topological_space
open_locale topological_space filter
noncomputable theory

@[derive [conditionally_complete_linear_order, linear_ordered_field, archimedean]]
def sorgenfrey_line : Type := ℝ

notation `ℝₗ` := sorgenfrey_line

namespace sorgenfrey_line

def to_real : ℝₗ ≃+* ℝ := ring_equiv.refl ℝ

instance : topological_space ℝₗ :=
topological_space.generate_from {s : set ℝₗ | ∃ a b : ℝₗ, Ico a b = s}

lemma is_open_Ico (a b : ℝₗ) : is_open (Ico a b) :=
topological_space.generate_open.basic _ ⟨a, b, rfl⟩

lemma is_open_Ici (a : ℝₗ) : is_open (Ici a) :=
begin
  have : (⋃ b, Ico a b) = Ici a,
  { simp only [← Ici_inter_Iio, ← inter_Union, inter_eq_left_iff_subset],
    exact λ b hb, mem_Union.2 (exists_gt b) },
  rw ← this,
  exact is_open_Union (is_open_Ico a)
end

lemma nhds_basis_Ico (a : ℝₗ) : (𝓝 a).has_basis ((<) a) (Ico a) :=
begin
  rw topological_space.nhds_generate_from,
  haveI : nonempty {x // x ≤ a} := set.nonempty_Iic_subtype,
  have : (⨅ (x : {i // i ≤ a}), 𝓟 (Ici ↑x)) = 𝓟 (Ici a),
  { refine (is_least.is_glb _).infi_eq,
    exact ⟨⟨⟨a, le_rfl⟩, rfl⟩, forall_range_iff.2 $
      λ b, principal_mono.2 $ Ici_subset_Ici.2 b.2⟩, },
  simp only [mem_set_of_eq, infi_and, infi_exists, @infi_comm _ (_ ∈ _),
    @infi_comm _ (set ℝₗ), infi_infi_eq_right],
  simp_rw [@infi_comm _ ℝₗ (_ ≤ _), infi_subtype', ← Ici_inter_Iio, ← inf_principal, ← inf_infi,
    ← infi_inf, this, infi_subtype],
  suffices : (⨅ x ∈ Ioi a, 𝓟 (Iio x)).has_basis ((<) a) Iio, from this.principal_inf _,
  refine has_basis_binfi_principal _ nonempty_Ioi,
  exact directed_on_iff_directed.2 (directed_of_inf $ λ x y hxy, Iio_subset_Iio hxy),
end

lemma nhds_basis_Ico_rat (a : ℝₗ) :
  (𝓝 a).has_countable_basis (λ r : ℚ, a < r) (λ r, Ico a r) :=
begin
  refine ⟨(nhds_basis_Ico a).to_has_basis (λ b hb, _) (λ r hr, ⟨_, hr, subset.rfl⟩),
    countable_encodable _⟩,
  rcases exists_rat_btwn hb with ⟨r, har, hrb⟩,
  exact ⟨r, har, Ico_subset_Ico_right hrb.le⟩
end

@[simp] lemma map_to_real_nhds (a : ℝₗ) : map to_real (𝓝 a) = 𝓝[≥] (to_real a) :=
begin
  refine ((nhds_basis_Ico a).map _).eq_of_same_basis _,
  simpa only [to_real.image_eq_preimage] using nhds_within_Ici_basis_Ico (to_real a)
end

@[continuity] lemma continuous_to_real : continuous to_real :=
continuous_iff_continuous_at.2 $ λ x,
  by { rw [continuous_at, tendsto, map_to_real_nhds], exact inf_le_left }

instance : order_closed_topology ℝₗ :=
⟨is_closed_le_prod.preimage (continuous_to_real.prod_map continuous_to_real)⟩

lemma is_clopen_Ici (a : ℝₗ) : is_clopen (Ici a) := ⟨is_open_Ici a, is_closed_Ici⟩

lemma is_clopen_Iio (a : ℝₗ) : is_clopen (Iio a) :=
by simpa only [compl_Ici] using (is_clopen_Ici a).compl

lemma is_clopen_Ico (a b : ℝₗ) : is_clopen (Ico a b) :=
(is_clopen_Ici a).inter (is_clopen_Iio b)

lemma exists_Ico_disjoint_closed {a : ℝₗ} {s : set ℝₗ} (hs : is_closed s) (ha : a ∉ s) :
  ∃ b > a, disjoint (Ico a b) s :=
by simpa only [disjoint_left]
  using (nhds_basis_Ico a).mem_iff.1 (hs.is_open_compl.mem_nhds ha)

instance : totally_disconnected_space ℝₗ :=
begin
  refine ⟨λ s hs' hs x hx y hy, _⟩, clear hs',
  by_contra' hne : x ≠ y, wlog hlt : x < y := hne.lt_or_lt using [x y, y x],
  exact hlt.not_le (hs.subset_clopen (is_clopen_Ici y) ⟨y, hy, le_rfl⟩ hx)
end

instance : first_countable_topology ℝₗ := ⟨λ x, (nhds_basis_Ico_rat x).is_countably_generated⟩

instance : normal_space ℝₗ :=
begin
  refine ⟨λ s t hs ht hd, _⟩,
  choose! X hX hXd using λ x (hx : x ∈ s), exists_Ico_disjoint_closed ht (disjoint_left.1 hd hx),
  choose! Y hY hYd using λ y (hy : y ∈ t), exists_Ico_disjoint_closed hs (disjoint_right.1 hd hy),
  refine ⟨⋃ x ∈ s, Ico x (X x), ⋃ y ∈ t, Ico y (Y y), is_open_bUnion $ λ _ _, is_open_Ico _ _,
    is_open_bUnion $ λ _ _, is_open_Ico _ _, _, _, _⟩,
  { exact λ x hx, mem_Union₂.2 ⟨x, hx, left_mem_Ico.2 $ hX x hx⟩ },
  { exact λ y hy, mem_Union₂.2 ⟨y, hy, left_mem_Ico.2 $ hY y hy⟩ },
  { simp only [disjoint_Union_left, disjoint_Union_right, Ico_disjoint_Ico],
    intros y hy x hx,
    clear hs ht hX hY,
    wlog : x ≤ y := le_total x y using [x y s t X Y, y x t s Y X] tactic.skip,
    {  }
 }
end

end sorgenfrey_line
