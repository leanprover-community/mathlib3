import order.filter.lift
import topology.maps

open set filter topological_space
open_locale filter topological_space

variables {ι : Sort*} {α X : Type*}

namespace filter

instance : topological_space (filter α) :=
generate_from $ range $ λ s : set α, {l : filter α | s ∈ l}

lemma nhds_eq (l : filter α) : 𝓝 l = l.lift' (λ s, {l' | s ∈ l'}) :=
begin
  refine nhds_generate_from.trans _,
  simp only [mem_set_of_eq, and_comm (l ∈ _), infi_and, infi_range, filter.lift', filter.lift]
end

protected lemma nhds_arg_mono : monotone (λ s : set α, {l : filter α | s ∈ l}) :=
λ s t hst l hl, mem_of_superset hl hst

lemma has_basis.nhds {l : filter α} {p : ι → Prop} {s : ι → set α} (h : has_basis l p s) :
  has_basis (𝓝 l) p (λ i, {l' | s i ∈ l'}) :=
begin
  rw nhds_eq,
  exact h.lift' filter.nhds_arg_mono
end

lemma nhds_at_top [preorder α] : 𝓝 (at_top : filter α) = ⨅ x : α, 𝓟 {l | Ici x ∈ l} :=
begin
  rw [nhds_eq, at_top, lift'_infi_of_map_univ]; [skip, by simp [set.ext_iff], by simp],
  simp only [lift'_principal filter.nhds_arg_mono],
end

variables [topological_space X]

lemma inducing_nhds : inducing (𝓝 : X → filter X) :=
begin
  refine ⟨eq_of_nhds_eq_nhds $ λ x, _⟩,
  simp only [nhds_induced, nhds_eq, comap_lift'_eq],
  refine le_antisymm (le_infi₂ $ λ s hs, le_principal_iff.2 _) (λ s hs, _),
  { filter_upwards [interior_mem_nhds.mpr hs] with y using mem_interior_iff_mem_nhds.mp },
  { exact mem_infi_of_mem s (mem_infi_of_mem hs $ λ y, mem_of_mem_nhds) }
end

lemma continuous_nhds  : continuous (𝓝 : X → filter X) :=
inducing_nhds.continuous

end filter
