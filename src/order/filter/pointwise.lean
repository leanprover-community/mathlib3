/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou

The pointwise operations on filters have nice properties, such as
  • map m (f₁ * f₂) = map m f₁ * map m f₂
  • nhds x * nhds y = nhds (x * y)

-/

import algebra.pointwise
import order.filter.basic

open classical set lattice

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

local attribute [instance] classical.prop_decidable pointwise_one pointwise_mul pointwise_add

namespace filter
open set

@[to_additive filter.pointwise_zero]
def pointwise_one [has_one α] : has_one (filter α) := ⟨principal {1}⟩

local attribute [instance] pointwise_one

@[simp, to_additive filter.mem_pointwise_zero]
lemma mem_pointwise_one [has_one α] (s : set α) :
  s ∈ (1 : filter α) ↔ (1:α) ∈ s :=
calc
  s ∈ (1:filter α) ↔ {(1:α)} ⊆ s : iff.rfl
  ... ↔ (1:α) ∈ s : by simp

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
    subset.trans (pointwise_mul_subset_mul (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
    subset.trans (pointwise_mul_subset_mul (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩,
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
    subset.trans (pointwise_add_subset_add (inter_subset_left _ _) (inter_subset_left _ _)) s₁s₂,
    subset.trans (pointwise_add_subset_add (inter_subset_right _ _) (inter_subset_right _ _)) t₁t₂⟩,
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

@[to_additive filter.pointwise_add_le_add]
lemma pointwise_mul_le_mul [monoid α] {f₁ f₂ g₁ g₂ : filter α} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ * g₁ ≤ f₂ * g₂ := assume _ ⟨s, hs, t, ht, hst⟩, ⟨s, hf hs, t, hg ht, hst⟩

@[to_additive filter.pointwise_add_ne_bot]
lemma pointwise_mul_ne_bot [monoid α] {f g : filter α} : f ≠ ⊥ → g ≠ ⊥ → f * g ≠ ⊥ :=
begin
  simp only [forall_sets_neq_empty_iff_neq_bot.symm],
  rintros hf hg s ⟨a, ha, b, hb, ab⟩,
  rcases ne_empty_iff_exists_mem.1 (pointwise_mul_ne_empty (hf a ha) (hg b hb)) with ⟨x, hx⟩,
  exact ne_empty_iff_exists_mem.2 ⟨x, ab hx⟩
end

@[to_additive filter.pointwise_add_assoc]
lemma pointwise_mul_assoc [monoid α] (f g h : filter α) : f * g * h = f * (g * h) :=
begin
  ext s, split,
  { rintros ⟨a, ⟨a₁, ha₁, a₂, ha₂, a₁a₂⟩, b, hb, ab⟩,
    refine ⟨a₁, ha₁, a₂ * b, mul_mem_pointwise_mul ha₂ hb, _⟩,
    rw [← pointwise_mul_semigroup.mul_assoc],
    exact calc
      a₁ * a₂ * b ⊆ a * b : pointwise_mul_subset_mul a₁a₂ (subset.refl _)
      ...         ⊆ s     : ab },
  { rintros ⟨a, ha, b, ⟨b₁, hb₁, b₂, hb₂, b₁b₂⟩, ab⟩,
    refine ⟨a * b₁, mul_mem_pointwise_mul ha hb₁, b₂, hb₂, _⟩,
    rw [pointwise_mul_semigroup.mul_assoc],
    exact calc
      a * (b₁ * b₂) ⊆ a * b : pointwise_mul_subset_mul (subset.refl _) b₁b₂
      ...           ⊆ s     : ab }
end

local attribute [instance] pointwise_mul_monoid

@[to_additive filter.pointwise_zero_add]
lemma pointwise_one_mul [monoid α] (f : filter α) : 1 * f = f :=
begin
  ext s, split,
  { rintros ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    refine mem_sets_of_superset (mem_sets_of_superset ht₂ _) t₁t₂,
    assume x hx,
    exact ⟨1, by rwa [← mem_pointwise_one], x, hx, (one_mul _).symm⟩ },
  { assume hs,
    refine ⟨(1:set α), mem_principal_self _, s, hs, by simp only [one_mul]⟩ }
end

@[to_additive filter.pointwise_add_zero]
lemma pointwise_mul_one [monoid α] (f : filter α) : f * 1 = f :=
begin
  ext s, split,
  { rintros ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    refine mem_sets_of_superset (mem_sets_of_superset ht₁ _) t₁t₂,
    assume x hx,
    exact ⟨x, hx, 1, by rwa [← mem_pointwise_one], (mul_one _).symm⟩ },
  { assume hs,
    refine ⟨s, hs, (1:set α), mem_principal_self _, by simp only [mul_one]⟩ }
end

@[to_additive filter.pointwise_add_add_monoid]
def pointwise_mul_monoid [monoid α] : monoid (filter α) :=
{ mul_assoc := pointwise_mul_assoc,
  one_mul := pointwise_one_mul,
  mul_one := pointwise_mul_one,
  .. pointwise_mul,
  .. pointwise_one }

local attribute [instance] filter.pointwise_mul_monoid filter.pointwise_add_add_monoid

section map
open is_mul_hom

variables [monoid α] [monoid β] {f : filter α} (m : α → β)

@[to_additive filter.map_pointwise_add]
lemma map_pointwise_mul [is_mul_hom m] {f₁ f₂ : filter α} : map m (f₁ * f₂) = map m f₁ * map m f₂ :=
filter_eq $ set.ext $ assume s,
begin
  simp only [mem_pointwise_mul], split,
  { rintro ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    have : m '' (t₁ * t₂) ⊆ s := subset.trans (image_subset m t₁t₂) (image_preimage_subset _ _),
    refine ⟨m '' t₁, image_mem_map ht₁, m '' t₂, image_mem_map ht₂, _⟩,
    rwa ← image_pointwise_mul m t₁ t₂ },
  { rintro ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩,
    refine ⟨m ⁻¹' t₁, ht₁, m ⁻¹' t₂, ht₂, image_subset_iff.1 _⟩,
    rw image_pointwise_mul m,
    exact subset.trans
      (pointwise_mul_subset_mul (image_preimage_subset _ _) (image_preimage_subset _ _)) t₁t₂ },
end

@[to_additive filter.map_pointwise_zero]
lemma map_pointwise_one [is_monoid_hom m] : map m (1:filter α) = 1 :=
le_antisymm
  (le_principal_iff.2 $ mem_map_sets_iff.2 ⟨(1:set α), by simp,
    by { assume x, simp [is_monoid_hom.map_one m], rintros rfl, refl  }⟩)
  (le_map $ assume s hs,
   begin
     simp only [mem_pointwise_one],
     exact ⟨(1:α), (mem_pointwise_one s).1 hs, is_monoid_hom.map_one _⟩
   end)

-- TODO: prove similar statements when `m` is group homomorphism etc.
def pointwise_mul_map_is_monoid_hom [is_monoid_hom m] : is_monoid_hom (map m) :=
{ map_one := map_pointwise_one m,
  map_mul := λ _ _, map_pointwise_mul m }

def pointwise_add_map_is_add_monoid_hom {α : Type*} {β : Type*} [add_monoid α] [add_monoid β]
  (m : α → β) [is_add_monoid_hom m] : is_add_monoid_hom (map m) :=
{ map_zero := map_pointwise_zero m,
  map_add := λ _ _, map_pointwise_add m }

attribute [to_additive filter.pointwise_add_map_is_add_monoid_hom] pointwise_mul_map_is_monoid_hom

-- The other direction does not hold in general.
@[to_additive filter.comap_add_comap_le]
lemma comap_mul_comap_le [is_mul_hom m] {f₁ f₂ : filter β} :
  comap m f₁ * comap m f₂ ≤ comap m (f₁ * f₂) :=
begin
  rintros s ⟨t, ⟨t₁, ht₁, t₂, ht₂, t₁t₂⟩, mt⟩,
  refine ⟨m ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, m ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, _⟩,
  have := subset.trans (preimage_mono t₁t₂) mt,
  exact subset.trans (preimage_pointwise_mul_preimage_subset m _ _) this
end

variables {m}

@[to_additive filter.tendsto_add_add]
lemma tendsto_mul_mul [is_mul_hom m] {f₁ g₁ : filter α} {f₂ g₂ : filter β} :
  tendsto m f₁ f₂ → tendsto m g₁ g₂ → tendsto m (f₁ * g₁) (f₂ * g₂) :=
assume hf hg, by { rw [tendsto, map_pointwise_mul m], exact pointwise_mul_le_mul hf hg }

end map

end filter
