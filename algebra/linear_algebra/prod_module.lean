/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Semigroup, monoid, group and module structures on product spaces.
-/

import data.prod algebra.linear_algebra.basic
open set function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {p q : α × β}

namespace prod

section
variables [has_mul α] [has_mul β]

instance : has_mul (α × β) := ⟨λp q, (p.1 * q.1, p.2 * q.2)⟩

@[simp] lemma fst_mul : (p * q).1 = p.1 * q.1 := rfl
@[simp] lemma snd_mul : (p * q).2 = p.2 * q.2 := rfl

end

section
variables [has_one α] [has_one β]

instance : has_one (α × β) := ⟨(1, 1)⟩

@[simp] lemma fst_one : (1 : α × β).1 = 1 := rfl
@[simp] lemma snd_one : (1 : α × β).2 = 1 := rfl

end

section
variables [has_inv α] [has_inv β]

instance : has_inv (α × β) := ⟨λp, (p.1⁻¹, p.2⁻¹)⟩

@[simp] lemma fst_inv : (p⁻¹).1 = (p.1)⁻¹ := rfl
@[simp] lemma snd_inv : (p⁻¹).2 = (p.2)⁻¹ := rfl

end

instance [semigroup α] [semigroup β] : semigroup (α × β) :=
{ mul_assoc := assume a b c, mk.inj_iff.mpr ⟨mul_assoc _ _ _, mul_assoc _ _ _⟩,
  .. prod.has_mul }

instance [monoid α] [monoid β] : monoid (α × β) :=
{ one_mul := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨one_mul _, one_mul _⟩,
  mul_one := assume a, prod.rec_on a $ λa b, mk.inj_iff.mpr ⟨mul_one _, mul_one _⟩,
  .. prod.semigroup, .. prod.has_one }

instance [group α] [group β] : group (α × β) :=
{ mul_left_inv := assume a, mk.inj_iff.mpr ⟨mul_left_inv _, mul_left_inv _⟩,
  .. prod.monoid, .. prod.has_inv }

instance [comm_semigroup α] [comm_semigroup β] : comm_semigroup (α × β) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.semigroup }

instance [comm_monoid α] [comm_monoid β] : comm_monoid (α × β) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.monoid }

instance [comm_group α] [comm_group β] : comm_group (α × β) :=
{ mul_comm := assume a b, mk.inj_iff.mpr ⟨mul_comm _ _, mul_comm _ _⟩,
  .. prod.group }

lemma fst_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).1 = t.prod (λc, (f c).1) :=
(finset.prod_hom prod.fst (show (1:α×β).1 = 1, from rfl) $ assume x y, rfl).symm

lemma snd_prod [comm_monoid α] [comm_monoid β] {t : finset γ} {f : γ → α × β} :
  (t.prod f).2 = t.prod (λc, (f c).2) :=
(finset.prod_hom prod.snd (show (1:α×β).2 = 1, from rfl) $ assume x y, rfl).symm

section
variables [has_add α] [has_add β]

instance : has_add (α × β) := ⟨λp q, (p.1 + q.1, p.2 + q.2)⟩
attribute [to_additive prod.has_add] prod.has_mul
attribute [to_additive prod.fst_add] prod.fst_mul
attribute [to_additive prod.snd_add] prod.snd_mul
attribute [simp] fst_add snd_add

end

section
variables [has_zero α] [has_zero β]

instance : has_zero (α × β) := ⟨(0, 0)⟩
attribute [to_additive prod.has_zero] prod.has_one
attribute [to_additive prod.fst_zero] prod.fst_one
attribute [to_additive prod.snd_zero] prod.snd_one
attribute [simp] fst_zero snd_zero

end

section
variables [has_neg α] [has_neg β]

instance : has_neg (α × β) := ⟨λp, (- p.1, - p.2)⟩
attribute [to_additive prod.has_neg] prod.has_inv
attribute [to_additive prod.fst_neg] prod.fst_inv
attribute [to_additive prod.snd_neg] prod.snd_inv
attribute [simp] fst_neg snd_neg

end

instance [add_semigroup α] [add_semigroup β] : add_semigroup (α × β) :=
{ add_assoc := assume a b c, mk.inj_iff.mpr ⟨add_assoc _ _ _, add_assoc _ _ _⟩, .. prod.has_add }
attribute [to_additive prod.add_semigroup]      prod.semigroup

instance [add_monoid α] [add_monoid β] : add_monoid (α × β) :=
{ zero_add := assume ⟨a, b⟩, mk.inj_iff.mpr ⟨zero_add _, zero_add _⟩,
  add_zero := assume ⟨a, b⟩, mk.inj_iff.mpr ⟨add_zero _, add_zero _⟩,
  .. prod.add_semigroup, .. prod.has_zero }
attribute [to_additive prod.add_monoid]         prod.monoid

instance [add_group α] [add_group β] : add_group (α × β) :=
{ add_left_neg := assume a, mk.inj_iff.mpr ⟨add_left_neg _, add_left_neg _⟩,
  .. prod.add_monoid, .. prod.has_neg }
attribute [to_additive prod.add_group]          prod.group

instance [add_comm_semigroup α] [add_comm_semigroup β] : add_comm_semigroup (α × β) :=
{ add_comm := assume a b, mk.inj_iff.mpr ⟨add_comm _ _, add_comm _ _⟩,
  .. prod.add_semigroup }
attribute [to_additive prod.add_comm_semigroup] prod.comm_semigroup

instance [add_comm_monoid α] [add_comm_monoid β] : add_comm_monoid (α × β) :=
{ add_comm := assume a b, mk.inj_iff.mpr ⟨add_comm _ _, add_comm _ _⟩,
  .. prod.add_monoid }
attribute [to_additive prod.add_comm_monoid]    prod.comm_monoid

instance [add_comm_group α] [add_comm_group β] : add_comm_group (α × β) :=
{ add_comm := assume a b, mk.inj_iff.mpr ⟨add_comm _ _, add_comm _ _⟩,
  .. prod.add_group }
attribute [to_additive prod.add_comm_group]     prod.comm_group

attribute [to_additive prod.fst_sum] prod.fst_prod
attribute [to_additive prod.snd_sum] prod.snd_prod

/- TODO: this fils with a code generation error

attribute [to_additive add_semigroup.add] semigroup.mul
attribute [to_additive add_monoid.one] monoid.one -- code generation error: unexpected macro found
attribute [to_additive add_monoid.add] monoid.mul
attribute [to_additive add_monoid.add_assoc] monoid.mul_assoc

attribute [to_additive prod.add_semigroup._proof_1] prod.semigroup._proof_1
attribute [to_additive prod.add_semigroup] prod.semigroup
attribute [instance] prod.add_semigroup

attribute [to_additive prod.add_monoid._proof_1] prod.monoid._proof_1
attribute [to_additive prod.add_monoid._proof_2] prod.monoid._proof_2
attribute [to_additive prod.add_monoid._proof_3] prod.monoid._proof_3
attribute [to_additive prod.add_monoid] prod.monoid

attribute [to_additive prod.add_group._proof_1] prod.group._proof_1
attribute [to_additive prod.add_group] prod.group
-/

/-- Left injection function for the inner product
From a vector space (and also group and module) perspective the product is the same as the sum of
two vector spaces. `inl` and `inr` provide the corresponding injection functions.
-/
def inl [has_zero β] (a : α) : α × β := (a, 0)

/-- Right injection function for the inner product -/
def inr [has_zero α] (b : β) : α × β := (0, b)


lemma injective_inl [has_zero β] : injective (inl : α → α × β) :=
assume x y h, (prod.mk.inj_iff.mp h).1

lemma injective_inr [has_zero α] : injective (inr : β → α × β) :=
assume x y h, (prod.mk.inj_iff.mp h).2

@[simp] lemma inl_eq_inl [has_zero β] {a₁ a₂ : α} : (inl a₁ : α × β) = inl a₂ ↔ a₁ = a₂ :=
iff.intro (assume h, injective_inl h) (assume h, h ▸ rfl)

@[simp] lemma inr_eq_inr [has_zero α] {b₁ b₂ : β} : (inr b₁ : α × β) = inr b₂ ↔ b₁ = b₂ :=
iff.intro (assume h, injective_inr h) (assume h, h ▸ rfl)

@[simp] lemma inl_eq_inr [has_zero α] [has_zero β] {a : α} {b : β} :
  (inl a = inr b) ↔ (a = 0 ∧ b = 0) :=
by constructor; simp [inl, inr] {contextual := tt}

@[simp] lemma inr_eq_inl [has_zero α] [has_zero β] {a : α} {b : β} :
  (inr b = inl a) ↔ (a = 0 ∧ b = 0) :=
by constructor; simp [inl, inr] {contextual := tt}

@[simp] lemma fst_inl [has_zero β] (a : α) : (inl a : α × β).1 = a := rfl
@[simp] lemma snd_inl [has_zero β] (a : α) : (inl a : α × β).2 = 0 := rfl
@[simp] lemma fst_inr [has_zero α] (b : β) : (inr b : α × β).1 = 0 := rfl
@[simp] lemma snd_inr [has_zero α] (b : β) : (inr b : α × β).2 = b := rfl

instance [has_scalar α β] [has_scalar α γ] : has_scalar α (β × γ) := ⟨λa p, (a • p.1, a • p.2)⟩

section module
variables [ring α] [module α β] [module α γ] [module α δ]
include α

instance : module α (β × γ) :=
{ smul_add := assume a p₁ p₂, mk.inj_iff.mpr ⟨smul_add, smul_add⟩,
  add_smul := assume a p₁ p₂, mk.inj_iff.mpr ⟨add_smul, add_smul⟩,
  mul_smul := assume a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul, mul_smul⟩,
  one_smul := assume ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul, one_smul⟩,
  .. prod.add_comm_group, .. prod.has_scalar }

lemma is_linear_map_prod_fst : is_linear_map (prod.fst : β × γ → β) :=
⟨assume x y, rfl, assume x y, rfl⟩

lemma is_linear_map_prod_snd : is_linear_map (prod.snd : β × γ → γ) :=
⟨assume x y, rfl, assume x y, rfl⟩

lemma is_linear_map_prod_mk {f : δ → β} {g : δ → γ} (hf : is_linear_map f) (hg : is_linear_map g):
  is_linear_map (λd, (f d, g d)) :=
⟨assume x y, mk.inj_iff.mpr ⟨hf.add _ _, hg.add _ _⟩,
  assume x y, mk.inj_iff.mpr ⟨hf.smul _ _, hg.smul _ _⟩⟩

lemma is_linear_map_prod_inl : is_linear_map (prod.inl : β → β × γ) :=
is_linear_map_prod_mk is_linear_map.id is_linear_map.map_zero

lemma is_linear_map_prod_inr : is_linear_map (prod.inr : γ → β × γ) :=
is_linear_map_prod_mk is_linear_map.map_zero is_linear_map.id

instance {s : set β} {t : set γ} [is_submodule s] [is_submodule t] : is_submodule (set.prod s t) :=
@is_submodule.inter_submodule _ _ _ _ _ _
  (is_submodule.preimage is_linear_map_prod_fst) (is_submodule.preimage is_linear_map_prod_snd)

lemma span_prod {s : set β} {t : set γ} : span (set.prod s t) ⊆ set.prod (span s) (span t) :=
span_minimal prod.is_submodule (set.prod_mono subset_span subset_span)

lemma span_inl_union_inr {s : set β} {t : set γ} :
  span (inl '' s ∪ inr '' t) = set.prod (span s) (span t) :=
span_eq prod.is_submodule
  (set.union_subset
    (set.image_subset_iff.mpr $ assume b hbs, ⟨subset_span hbs, is_submodule.zero⟩)
    (set.image_subset_iff.mpr $ assume c hct, ⟨is_submodule.zero, subset_span hct⟩))
  (assume ⟨b, c⟩ ⟨hb, hc⟩,
  begin
    simp [span_union, span_image_of_linear_map is_linear_map_prod_inl,
      span_image_of_linear_map is_linear_map_prod_inr],
    exact ⟨b, 0, ⟨b, hb, rfl⟩, 0, c, ⟨c, hc, rfl⟩,
      mk.inj_iff.mpr ⟨(add_zero _).symm, (zero_add _).symm⟩⟩
  end)

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent s) (ht : linear_independent t) :
  linear_independent (inl '' s ∪ inr '' t) :=
linear_independent_union
  (hs.image is_linear_map_prod_inl $ assume a ha b hb eq, injective_inl eq)
  (ht.image is_linear_map_prod_inr $ assume a ha b hb eq, injective_inr eq)
  (subset.antisymm
    (by rw [span_image_of_linear_map is_linear_map_prod_inl,
      span_image_of_linear_map is_linear_map_prod_inr];
      exact assume ⟨b, c⟩ ⟨⟨b', hb', beq⟩, ⟨c', hc', ceq⟩⟩,
        have c = 0, from (prod.mk.inj beq).2.symm,
        have b = 0, from (prod.mk.inj ceq).1.symm,
        by simp *; refl)
    (by simp [is_submodule.zero]))

lemma is_basis_inl_union_inr {s : set β} {t : set γ}
  (hs : is_basis s) (ht : is_basis t) : is_basis (inl '' s ∪ inr '' t) :=
⟨linear_independent_inl_union_inr hs.1 ht.1,
  by rw [span_inl_union_inr]; exact assume ⟨b, c⟩, ⟨hs.2 b, ht.2 c⟩⟩

end module
end prod
