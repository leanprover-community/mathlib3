/-
Copyright (c) 2022 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
import order.bounded_order

/-!
# Involution lattices

This file concerns orders that admit an order-reversing involution. In the case of a lattice,
these are sometimes referred to as 'i-lattices' or 'lattices with involution'. Such an involution
is more general than a `boolean_algebra` complement, but retains many of its properties. Other than
a boolean algebra, an example is the subspace lattice of the vector space `𝕂ⁿ` for `𝕂` of nonzero
characteristic, where for each subspace `W` we have `compl W = {a ∈ V | ∀ w ∈ W, wᵀx = 0}`; this is
not a complement in the stronger sense because `compl W` can intersect `W`.

## Main declarations

* `involution_lattice`: Lattice with an antitone involution.

## Notation

* `xᶜ` is notation for `compl x`

## TODO

Provide instances other than the one from `boolean_algebra`.
-/

namespace function
variables {α β : Type*} {f : α → α} {g : β → β}

lemma involutive.prod_map (hf : involutive f) (hg : involutive g) : involutive (prod.map f g) :=
λ a, by rw [prod.map_map, hf.comp_self, hg.comp_self, prod.map_id, id]

end function

section
variables {α β γ δ : Type*} [preorder α] [preorder β] [preorder γ] [preorder δ]
  {f : α → γ} {g : β → δ} {a b : α}

lemma monotone.imp (hf : monotone f) (h : a ≤ b) : f a ≤ f b := hf h
lemma antitone.imp (hf : antitone f) (h : a ≤ b) : f b ≤ f a := hf h
lemma strict_mono.imp (hf : strict_mono f) (h : a < b) : f a < f b := hf h
lemma strict_anti.imp (hf : strict_anti f) (h : a < b) : f b < f a := hf h

lemma monotone.prod_map (hf : monotone f) (hg : monotone g) : monotone (prod.map f g) :=
λ a b h, ⟨hf h.1, hg h.2⟩

lemma antitone.prod_map (hf : antitone f) (hg : antitone g) : antitone (prod.map f g) :=
λ a b h, ⟨hf h.1, hg h.2⟩

end

section
variables {α β γ δ : Type*} [partial_order α] [partial_order β] [partial_order γ] [partial_order δ]
  {f : α → γ} {g : β → δ}

lemma strict_mono.prod_map (hf : strict_mono f) (hg : strict_mono g) : strict_mono (prod.map f g) :=
λ a b, by { simp_rw prod.lt_iff,
  exact or.imp (and.imp hf.imp hg.monotone.imp) (and.imp hf.monotone.imp hg.imp) }

lemma strict_anti.prod_map (hf : strict_anti f) (hg : strict_anti g) : strict_anti (prod.map f g) :=
λ a b, by { simp_rw prod.lt_iff,
  exact or.imp (and.imp hf.imp hg.antitone.imp) (and.imp hf.antitone.imp hg.imp) }

end

open function order_dual

variables {ι α β : Type*}

/-! ### Notation -/

/-- Syntax typeclass for lattice complement. -/
@[notation_class] class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl) has_sdiff (sdiff)

postfix `ᶜ`:(max+1) := compl

namespace prod

instance [has_sdiff α] [has_sdiff β] : has_sdiff (α × β) := ⟨λ a b, (a.1 \ b.1, a.2 \ b.2)⟩
instance [has_compl α] [has_compl β] : has_compl (α × β) := ⟨λ a, (a.1ᶜ, a.2ᶜ)⟩

@[simp] lemma fst_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).1 = a.1 \ b.1 := rfl
@[simp] lemma snd_sdiff [has_sdiff α] [has_sdiff β] (a b : α × β) : (a \ b).2 = a.2 \ b.2 := rfl
@[simp] lemma fst_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.1 = a.1ᶜ := rfl
@[simp] lemma snd_compl [has_compl α] [has_compl β] (a : α × β) : aᶜ.2 = a.2ᶜ := rfl

end prod

namespace pi
variables {π : ι → Type*}

instance [Π i, has_compl (π i)] : has_compl (Π i, π i) := ⟨λ a i, (a i)ᶜ⟩
instance [Π i, has_sdiff (π i)] : has_sdiff (Π i, π i) := ⟨λ a b i, a i \ b i⟩

lemma sdiff_def [Π i, has_sdiff (π i)] (a b : Π i, π i) : a \ b = λ i, a i \ b i := rfl
lemma compl_def [Π i, has_compl (π i)] (a : Π i, π i) : aᶜ = λ i, (a i)ᶜ := rfl

@[simp] lemma sdiff_apply [Π i, has_sdiff (π i)] (a b : Π i, π i) (i : ι) : (a \ b) i = a i \ b i :=
rfl
@[simp] lemma compl_apply [Π i, has_compl (π i)] (a : Π i, π i) (i : ι) : aᶜ i = (a i)ᶜ := rfl

end pi

/-- An antitone involution on a preorder -/
class involution_lattice (α : Type*) extends lattice α, has_compl α :=
(compl_antitone' : antitone compl)
(compl_involutive' : involutive compl)

variables [involution_lattice α] {a b : α}

lemma compl_antitone : antitone (compl : α → α) := involution_lattice.compl_antitone'
lemma compl_involutive : involutive (compl : α → α) := involution_lattice.compl_involutive'
lemma compl_bijective : bijective (compl : α → α) := compl_involutive.bijective
lemma compl_surjective : surjective (compl : α → α) := compl_involutive.surjective
lemma compl_injective : injective (compl : α → α) := compl_involutive.injective
lemma compl_comp_compl : compl ∘ compl = @id α := compl_involutive.comp_self
@[simp] lemma compl_inj : aᶜ = bᶜ ↔ a = b := compl_injective.eq_iff

@[simp] lemma compl_compl (a : α) : aᶜᶜ = a := compl_involutive _

lemma compl_eq_comm : aᶜ = b ↔ bᶜ = a := eq_comm.trans compl_involutive.eq_iff.symm
lemma eq_compl_comm : a = bᶜ ↔ b = aᶜ := compl_involutive.eq_iff.symm.trans eq_comm

lemma compl_le_compl (h : a ≤ b) : bᶜ ≤ aᶜ := compl_antitone h

lemma le_of_compl_le_compl (h : aᶜ ≤ bᶜ) : b ≤ a :=
by { rw [←compl_compl a, ←compl_compl b], exact compl_le_compl h }

lemma compl_le_compl_iff : aᶜ ≤ bᶜ ↔ b ≤ a := ⟨le_of_compl_le_compl, compl_le_compl⟩
lemma le_compl_iff_le_compl : a ≤ bᶜ ↔ b ≤ aᶜ := by rw [←compl_le_compl_iff, compl_compl]
lemma compl_le_iff_compl_le : aᶜ ≤ b ↔ bᶜ ≤ a := by rw [←compl_le_compl_iff, compl_compl]
lemma le_compl_of_le_compl : b ≤ aᶜ → a ≤ bᶜ := le_compl_iff_le_compl.1
lemma compl_le_of_compl_le : bᶜ ≤ a → aᶜ ≤ b := compl_le_iff_compl_le.1

lemma compl_lt_compl_iff : aᶜ < bᶜ ↔ b < a :=
lt_iff_lt_of_le_iff_le' compl_le_compl_iff compl_le_compl_iff
lemma lt_compl_iff_lt_compl : a < bᶜ ↔ b < aᶜ := by rw [←compl_lt_compl_iff, compl_compl]
lemma compl_lt_iff_compl_lt : aᶜ < b ↔ bᶜ < a := by rw [←compl_lt_compl_iff, compl_compl]

/-- Taking the involution as an order isomorphism to the order dual. -/
@[simps] def order_iso.compl (α : Type*) [involution_lattice α] : α ≃o αᵒᵈ :=
{ to_fun := to_dual ∘ compl,
  inv_fun := compl ∘ of_dual,
  left_inv := compl_compl,
  right_inv := compl_compl,
  map_rel_iff' := λ _ _, compl_le_compl_iff }

lemma compl_strict_anti : strict_anti (compl : α → α) := (order_iso.compl α).strict_mono

@[simp] lemma compl_sup (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := (order_iso.compl α).map_sup _ _
@[simp] lemma compl_inf (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := (order_iso.compl α).map_inf _ _

section bounded_order
variables [bounded_order α]

@[simp] lemma compl_top : (⊤ : α)ᶜ = ⊥ := (order_iso.compl α).map_top
@[simp] lemma compl_bot : (⊥ : α)ᶜ = ⊤ := (order_iso.compl α).map_bot
@[simp] lemma compl_eq_top : aᶜ = ⊤ ↔ a = ⊥ := by rw [←compl_bot, compl_inj]
@[simp] lemma compl_eq_bot : aᶜ = ⊥ ↔ a = ⊤ := by rw [←compl_top, compl_inj]

end bounded_order

instance : involution_lattice αᵒᵈ :=
{ compl := λ a, to_dual (of_dual a)ᶜ,
  compl_antitone' := compl_antitone.dual,
  compl_involutive' := compl_involutive }

@[simp] lemma of_dual_compl (a : αᵒᵈ) : of_dual aᶜ = (of_dual a)ᶜ := rfl
@[simp] lemma to_dual_compl (a : α) : to_dual aᶜ = (to_dual a)ᶜ := rfl

/-- Pullback an `involution_lattice` along an injection. -/
@[reducible] -- See note [reducible non-instances]
protected def function.injective.involution_lattice [has_sup α] [has_inf α] [has_bot α]
  [has_compl α] [involution_lattice β] (f : α → β) (hf : injective f)
  (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
  (map_compl : ∀ a, f aᶜ = (f a)ᶜ) :
  involution_lattice α :=
{ compl := compl,
  compl_antitone' := λ a b h, (map_compl _).trans_le $ (compl_antitone h).trans_eq
    (map_compl _).symm,
  compl_involutive' := λ a, hf $ by rw [map_compl, map_compl, compl_compl],
  ..hf.lattice f map_sup map_inf }

instance [involution_lattice β] : involution_lattice (α × β) :=
{ compl := compl,
  compl_antitone' := compl_antitone.prod_map compl_antitone,
  compl_involutive' := compl_involutive.prod_map compl_involutive }

instance {α : ι → Type*} [Π i, involution_lattice (α i)] : involution_lattice (Π i, α i) :=
{ le := (≤),
  compl := compl,
  compl_antitone' := λ a b h i, compl_antitone (h i),
  compl_involutive' := λ a, funext $ λ i, compl_compl _ }

/-! ### Stuff to move to `data.set.intervals.basic` -/

section image

variables [involution_lattice α] {s : set α} {a b : α}

open set order_dual

lemma image_compl_eq_preimage_compl : compl '' s = compl ⁻¹' s :=
ext (λ a, ⟨by {rintro ⟨x',hx',rfl⟩, rwa [←compl_compl x'] at hx'}, λ h, ⟨aᶜ, ⟨h, compl_compl a⟩⟩⟩)

@[simp] lemma compl_compl_image : compl '' compl '' s = s := by { ext, simp }

lemma is_antichain.image_compl (hs : is_antichain (≤) s) : is_antichain (≤) (compl '' s) :=
(hs.image_embedding (order_iso.compl α).to_order_embedding).flip

lemma is_antichain.preimage_compl (hs : is_antichain (≤) s) : is_antichain (≤) (compl ⁻¹' s) :=
image_compl_eq_preimage_invo.subst hs.image_invo

@[simp] lemma preimage_compl_Iic : compl ⁻¹' Iic a = Ici aᶜ := ext $ λ _, compl_le_iff_compl_le
@[simp] lemma preimage_compl_Ici : compl ⁻¹' Ici a = Iic aᶜ := ext $ λ _, le_compl_iff_le_compl
@[simp] lemma preimage_compl_Iio : compl ⁻¹' Iio a = Ioi aᶜ := ext $ λ _, compl_lt_iff_compl_lt
@[simp] lemma preimage_compl_Ioi : compl ⁻¹' Ioi a = Iio aᶜ := ext $ λ _, lt_compl_iff_lt_compl

@[simp] lemma preimage_compl_Icc : compl ⁻¹' Icc a b = Icc bᶜ aᶜ :=
by simp [←Iic_inter_Ici, inter_comm]

@[simp] lemma preimage_compl_Ico : compl ⁻¹' Ico a b = Ioc bᶜ aᶜ :=
by simp [←Iio_inter_Ici, ←Iic_inter_Ioi, inter_comm]

@[simp] lemma preimage_compl_Ioc : compl ⁻¹' Ioc a b = Ico bᶜ aᶜ :=
by simp [←Iio_inter_Ici, ←Iic_inter_Ioi, inter_comm]

@[simp] lemma preimage_compl_Ioo : compl ⁻¹' Ioo a b = Ioo bᶜ aᶜ :=
by simp [←Iio_inter_Ioi, inter_comm]

@[simp] lemma image_compl_Iic : compl '' Iic a = Ici aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Iic]

@[simp] lemma image_compl_Ici : compl '' Ici a = Iic aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Ici]

@[simp] lemma image_compl_Iio : compl '' Iio a = Ioi aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Iio]

@[simp] lemma image_compl_Ioi : compl '' Ioi a = Iio aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Ioi]

@[simp] lemma image_compl_Icc : compl '' Icc a b = Icc bᶜ aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Icc]

@[simp] lemma image_compl_Ioo : compl '' Ioo a b = Ioo bᶜ aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Ioo]

@[simp] lemma image_compl_Ioc : compl '' Ioc a b = Ico bᶜ aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Ioc]

@[simp] lemma image_compl_Ico : compl '' Ico a b = Ioc bᶜ aᶜ :=
by rw [image_compl_eq_preimage_invo, preimage_compl_Ico]

end image
