/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.bornology.basic

/-!
# TODO
-/

open set filter function

variables {α β γ : Type*} {b₁ b₂ : bornology α} {s t u v : set α}

namespace bornology

lemma cobounded_injective : injective (@cobounded α) :=
λ b₁ b₂ h, by ext; rw h

instance : partial_order (bornology α) := partial_order.lift
  (_ : bornology α → order_dual (filter α)) cobounded_injective

protected lemma le_def : b₁ ≤ b₂ ↔ b₂.cobounded ≤ b₁.cobounded := iff.rfl

protected lemma le_iff : b₁ ≤ b₂ ↔ (∀ s, @is_bounded _ b₁ s → @is_bounded _ b₂ s) :=
begin
  rw [bornology.le_def, ← @comap_id α (@cobounded _ b₂), comap_cobounded_le_iff],
  simp
end

instance : has_Inf (bornology α) :=
⟨λ S, ⟨Sup (@cobounded α '' S), Sup_le (λ f ⟨b, hb, hbf⟩, hbf ▸ b.le_cofinite)⟩⟩

instance : has_Sup (bornology α) :=
⟨λ S, ⟨filter.cofinite ⊓ (Inf (@cobounded α '' S)), inf_le_left⟩⟩

instance : has_inf (bornology α) :=
⟨λ b₁ b₂, ⟨@cobounded α b₁ ⊔ @cobounded α b₂, sup_le b₁.le_cofinite b₂.le_cofinite⟩⟩

instance : has_sup (bornology α) :=
⟨λ b₁ b₂, ⟨@cobounded α b₁ ⊓ @cobounded α b₂, inf_le_of_left_le b₁.le_cofinite⟩⟩

instance : has_bot (bornology α) :=
⟨bornology.cofinite⟩

instance : has_top (bornology α) :=
⟨⟨⊥, bot_le⟩⟩

instance : lattice (bornology α) :=
{ le_sup_left := λ b₁ b₂, by {rw [bornology.le_def], exact inf_le_left},
  le_sup_right := λ b₁ b₂, by {rw [bornology.le_def], exact inf_le_right},
  sup_le := λ b₁ b₂ b₃ h₁₃ h₂₃, by {rw [bornology.le_def] at *, exact le_inf h₁₃ h₂₃},
  inf_le_left := λ b₁ b₂, by {rw [bornology.le_def], exact le_sup_left},
  inf_le_right := λ b₁ b₂, by {rw [bornology.le_def], exact le_sup_right},
  le_inf := λ b₁ b₂ b₃ h₁₃ h₂₃, by {rw [bornology.le_def] at *, exact sup_le h₁₃ h₂₃},
  ..bornology.partial_order,
  ..bornology.has_inf,
  ..bornology.has_sup }

instance : complete_lattice (bornology α) :=
{ le_Sup := λ S b hb,
    by {rw [bornology.le_def], exact inf_le_of_right_le (Inf_le  $ mem_image_of_mem _ hb)},
  Sup_le := λ S b hb,
    by {simp_rw [bornology.le_def] at *,
        exact le_inf b.le_cofinite (le_Inf $ λ f ⟨b', hb', hfb'⟩, hfb' ▸ hb b' hb')},
  Inf_le := λ S b hb, by {rw [bornology.le_def], exact le_Sup (mem_image_of_mem _ hb)},
  le_Inf := λ S b hb,
    by {simp_rw [bornology.le_def] at *,
        refine Sup_le (λ f ⟨b', hb', hfb'⟩, hfb' ▸ hb b' hb')},
  le_top := λ b, by {rw [bornology.le_def], exact bot_le},
  bot_le := λ b, by {rw [bornology.le_def], exact b.le_cofinite},
  ..bornology.lattice,
  ..bornology.has_Inf,
  ..bornology.has_Sup,
  ..bornology.has_bot,
  ..bornology.has_top }

lemma is_bounded_Inf_iff {B : set (bornology α)} :
  @is_bounded _ (Inf B) s ↔ ∀ b ∈ B, @is_bounded _ b s :=
begin
  let b : bornology α := of_bounded' {t | ∀ b ∈ B, @is_bounded _ b t}
    (λ b' hb', @is_bounded_empty _ b')
    (λ t₁ h₁ t₂ h₁₂ b' hb', @is_bounded.subset _ b' _ _ (h₁ b' hb') h₁₂)
    (λ t₁ h₁ t₂ h₂ b' hb', @is_bounded.union _ b' _ _ (h₁ b' hb') (h₂ b' hb'))
    (λ x b' hb', @is_bounded_singleton _ b' x),
  suffices : Inf B = b,
  { rw [this, is_bounded_of_bounded_iff], refl },
  refine le_antisymm _ (le_Inf $ λ b' hb', bornology.le_iff.mpr $
    λ s hs, ((is_bounded_of_bounded_iff _).mp hs) b' hb'),
  rw bornology.le_iff,
  intros s hs,
  rw [is_bounded_of_bounded_iff],
  intros b' hb',
  revert s hs,
  rw ← bornology.le_iff,
  exact Inf_le hb'
end

lemma is_bounded_infi_iff {ι : Type*} {B : ι → bornology α} :
  @is_bounded _ (⨅ i, B i) s ↔ ∀ i, @is_bounded _ (B i) s :=
by rw [infi, is_bounded_Inf_iff, forall_range_iff]

lemma is_bounded_inf_iff :
  @is_bounded _ (b₁ ⊓ b₂) s ↔ @is_bounded _ b₁ s ∧ @is_bounded _ b₂ s :=
by rw [inf_eq_infi, is_bounded_infi_iff, bool.forall_bool, and_comm]

--def map (b : bornology α) (f : α → β) : bornology β :=
--of_bounded ((image f) '' {s | @is_bounded _ b s}) ⟨∅, is_bounded_empty, image_empty f⟩
--  (λ s₁ ⟨t₁, ht₁, hst₁⟩ s₂ hs₁₂, ⟨f ⁻¹' s₂ ∩ t₁, ht₁.subset (inter_subset_right _ _),
--    (image_preimage_inter f t₁ s₂).symm ▸ hst₁.symm ▸ inter_eq_left_iff_subset.mpr hs₁₂⟩)
--  (λ s₁ ⟨t₁, ht₁, hst₁⟩ s₂ ⟨t₂, ht₂, hst₂⟩,
--    hst₁ ▸ hst₂ ▸ image_union f t₁ t₂ ▸ mem_image_of_mem (image f) (ht₁.union ht₂))
--  (eq_univ_of_forall $ λ x, mem_sUnion_of_mem (mem_singleton_of_eq rfl) _)

lemma cobounded_antitone : antitone (@cobounded α) :=
λ b₁ b₂, id

lemma cobounded_strict_anti : strict_anti (@cobounded α) :=
λ b₁ b₂, id

@[simp] lemma cobounded_sup :
  @cobounded _ (b₁ ⊔ b₂) = (@cobounded _ b₁) ⊓ (@cobounded _ b₂) :=
rfl

@[simp] lemma cobounded_inf :
  @cobounded _ (b₁ ⊓ b₂) = (@cobounded _ b₁) ⊔ (@cobounded _ b₂) :=
rfl

@[simp] lemma cobounded_Sup {B : set (bornology α)} :
  @cobounded _ (Sup B) = filter.cofinite ⊓ ⨅ (b ∈ B), @cobounded _ b :=
by rw ← Inf_image; refl

lemma cobounded_Sup' {B : set (bornology α)} (h : B.nonempty) :
  @cobounded _ (Sup B) = ⨅ (b ∈ B), @cobounded _ b :=
begin
  rw [cobounded_Sup, inf_eq_right],
  exact binfi_le_of_le h.some h.some_mem h.some.le_cofinite
end

@[simp] lemma cobounded_Inf {B : set (bornology α)} :
  @cobounded _ (Inf B) = ⨆ (b ∈ B), @cobounded _ b :=
by rw ← Sup_image; refl

@[simp] lemma cobounded_supr {ι : Sort*} {B : ι → bornology α} :
  @cobounded _ (⨆ i, B i) = filter.cofinite ⊓ ⨅ i, @cobounded _ (B i) :=
by rw [supr, cobounded_Sup, infi_range]

lemma cobounded_supr' {ι : Sort*} [nonempty ι] {B : ι → bornology α} :
  @cobounded _ (⨆ i, B i) = ⨅ i, @cobounded _ (B i) :=
by rw [supr, cobounded_Sup' (set.range_nonempty _), infi_range]; assumption

@[simp] lemma cobounded_infi {ι : Sort*} {B : ι → bornology α} :
  @cobounded _ (⨅ i, B i) = ⨆ i, @cobounded _ (B i) :=
by rw [infi, cobounded_Inf, supr_range]

def generate (S : set (set α)) : bornology α :=
Inf {b | ∀ s ∈ S, @is_bounded _ b s}

lemma generate_minimal {S : set (set α)} {b : bornology α} (h : ∀ s ∈ S, @is_bounded _ b s) :
  generate S ≤ b :=
Inf_le h

lemma generate_mono : monotone (generate : set (set α) → bornology α) :=
λ S T (hST : S ⊆ T), Inf_le_Inf (λ b hb s hsS, hb s (hST hsS))

lemma is_bounded_generate {S : set (set α)} {s : set α} (h : s ∈ S) :
  @is_bounded _ (generate S) s :=
begin
  rw [generate, is_bounded_Inf_iff],
  exact λ b hb, hb s h
end

lemma cobounded_generate_eq_generate_compl_inf_cofinite (S : set (set α)) :
  @cobounded _ (bornology.generate S) = filter.generate (compl '' S) ⊓ filter.cofinite :=
begin
  refine le_antisymm (le_inf _ (@le_cofinite _ $ generate S)) _,
  { rw sets_iff_generate,
    rintros s ⟨t, ht, rfl⟩,
    exact @is_bounded.compl _ (generate S) _ (is_bounded_generate ht) },
  { let b : bornology α :=
    { cobounded := filter.generate (compl '' S) ⊓ filter.cofinite,
      le_cofinite := inf_le_right },
    change generate S ≤ b,
    exact generate_minimal
      (λ s hs, mem_inf_of_left $ generate_sets.basic $ mem_image_of_mem _ hs) }
end

end bornology
