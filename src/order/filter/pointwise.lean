import algebra.pointwise
import order.filter.basic

open classical set lattice

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

local attribute [instance] classical.prop_decidable pointwise_mul pointwise_add

namespace filter
open set

def pointwise_mul [monoid α] : has_mul (filter α) := ⟨λf g,
{ sets             := { s | ∃t₁∈f, ∃t₂∈g, t₁ * t₂  ⊆ s },
  univ_sets        :=
  begin
    have h₁ : (∃x, x ∈ f.sets) := ⟨univ, univ_sets f⟩,
    have h₂ : (∃x, x ∈ g.sets) := ⟨univ, univ_sets g⟩,
    simpa using and.intro h₁ h₂
  end,
  sets_of_superset := λx y hx hxy,
  begin
   rcases hx with ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
   exact ⟨t₁, ht₁, t₂, ht₂, subset.trans t₁t₂ hxy⟩
  end,
  inter_sets       := λx y,
  begin
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff],
    rintros ⟨s₁, hs₁, s₂, hs₂, s₁s₂⟩ ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    exact ⟨s₁ ∩ t₁, inter_sets f hs₁ ht₁, s₂ ∩ t₂, inter_sets g hs₂ ht₂,
    subset.trans (mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
    subset.trans (mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩,
  end }⟩

def pointwise_add [add_monoid α] : has_add (filter α) := ⟨λf g,
{ sets             := { s | ∃t₁∈f, ∃t₂∈g, t₁ + t₂  ⊆ s },
  univ_sets        :=
  begin
    have h₁ : (∃x, x ∈ f.sets) := ⟨univ, univ_sets f⟩,
    have h₂ : (∃x, x ∈ g.sets) := ⟨univ, univ_sets g⟩,
    simpa using and.intro h₁ h₂
  end,
  sets_of_superset := λx y hx hxy,
  begin
   rcases hx with ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
   exact ⟨t₁, ht₁, t₂, ht₂, subset.trans t₁t₂ hxy⟩
  end,
  inter_sets       := λx y,
  begin
    simp only [exists_prop, mem_set_of_eq, subset_inter_iff],
    rintros ⟨s₁, hs₁, s₂, hs₂, s₁s₂⟩ ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    exact ⟨s₁ ∩ t₁, inter_sets f hs₁ ht₁, s₂ ∩ t₂, inter_sets g hs₂ ht₂,
    subset.trans (add_subset_add (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
    subset.trans (add_subset_add (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩,
  end }⟩

attribute [to_additive filter.pointwise_add] pointwise_mul
attribute [to_additive filter.pointwise_add._proof_1] pointwise_mul._proof_1
attribute [to_additive filter.pointwise_add._proof_2] pointwise_mul._proof_2
attribute [to_additive filter.pointwise_add._proof_3] pointwise_mul._proof_3
attribute [to_additive filter.pointwise_add.equations.eqn_1] filter.pointwise_mul.equations._eqn_1

local attribute [instance] pointwise_mul pointwise_add

@[to_additive filter.mem_pointwise_add]
lemma mem_pointwise_mul [monoid α] {f g : filter α} {s : set α} :
  s ∈ f * g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ * t₂ ⊆ s := iff.rfl

@[to_additive filter.add_mem_pointwise_add]
lemma mul_mem_pointwise_mul [monoid α] {f g : filter α} {s t : set α} (hs : s ∈ f) (ht : t ∈ g) :
  s * t ∈ f * g := ⟨_, hs, _, ht, subset.refl _⟩

@[to_additive filter.add_le_add]
lemma mul_le_mul [monoid α] {f₁ f₂ g₁ g₂ : filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ * g₁ ≤ f₂ * g₂ := assume _ ⟨s, hs, t, ht, hst⟩, ⟨s, hf hs, t, hg ht, hst⟩

@[to_additive filter.add_ne_bot]
lemma mul_ne_bot [monoid α] {f g : filter α} : f ≠ ⊥ → g ≠ ⊥ → f * g ≠ ⊥ :=
begin
  simp only [forall_sets_neq_empty_iff_neq_bot.symm],
  rintros hf hg s ⟨a, ha, b, hb, ab⟩,
  rcases ne_empty_iff_exists_mem.1 (pointwise_mul_ne_empty (hf a ha) (hg b hb)) with ⟨x, hx⟩,
  exact ne_empty_iff_exists_mem.2 ⟨x, ab hx⟩
end

@[to_additive filter.pointwise_add_assoc]
lemma pointwise_mul_assoc [monoid α] {f g h : filter α} : f * g * h = f * (g * h) :=
begin
  ext s, split,
  { rintros ⟨a, ⟨a₁, ha₁, a₂, ha₂, a₁a₂⟩, b, hb, ab⟩,
    refine ⟨a₁, ha₁, a₂ * b, mul_mem_pointwise_mul ha₂ hb, _⟩,
    rw [← pointwise_mul_semigroup.mul_assoc],
    exact calc
      a₁ * a₂ * b ⊆ a * b : mul_subset_mul a₁a₂ (subset.refl _)
      ...         ⊆ s     : ab },
  { rintros ⟨a, ha, b, ⟨b₁, hb₁, b₂, hb₂, b₁b₂⟩, ab⟩,
    refine ⟨a * b₁, mul_mem_pointwise_mul ha hb₁, b₂, hb₂, _⟩,
    rw [pointwise_mul_semigroup.mul_assoc],
    exact calc
      a * (b₁ * b₂) ⊆ a * b : mul_subset_mul (subset.refl _) b₁b₂
      ...           ⊆ s     : ab }
end

section map
open is_mul_hom

variables [monoid α] [monoid β] {f : filter α}
          (m : α → β) [is_mul_hom m]

@[to_additive filter.map_add_map]
lemma map_mul_map {f₁ f₂ : filter α} : map m f₁ * map m f₂ = map m (f₁ * f₂) :=
filter_eq $ set.ext $ assume s,
begin
  simp only [mem_pointwise_mul], split,
  { rintro ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    refine ⟨m ⁻¹' t₁, ht₁, m ⁻¹' t₂, ht₂, image_subset_iff.1 _⟩,
    rw image_pointwise_mul m,
    exact subset.trans
      (mul_subset_mul (image_preimage_subset _ _) (image_preimage_subset _ _)) t₁t₂ },
  { rintro ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    have : m '' (t₁ * t₂) ⊆ s := subset.trans (image_subset m t₁t₂) (image_preimage_subset _ _),
    refine ⟨m '' t₁, image_mem_map ht₁, m '' t₂, image_mem_map ht₂, _⟩,
    rwa ← image_pointwise_mul m t₁ t₂ }
end

-- The other direction does not hold in general.
@[to_additive filter.comap_add_comap_le]
lemma comap_mul_comap_le {f₁ f₂ : filter β} : comap m f₁ * comap m f₂ ≤ comap m (f₁ * f₂) :=
begin
  rintros s ⟨t, ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩, mt⟩,
  refine ⟨m ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, m ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, _⟩,
  have := subset.trans (preimage_mono t₁t₂) mt,
  exact subset.trans (preimage_pointwise_mul_preimage_subset m _ _) this
end

variables {m}

@[to_additive filter.tendsto_add_add]
lemma tendsto_mul_mul {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
assume hf hg, by { rw [tendsto, ← map_mul_map m], exact mul_le_mul hf hg }

variables (m)

end map

end filter
