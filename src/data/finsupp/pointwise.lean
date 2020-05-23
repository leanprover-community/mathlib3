/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.finsupp

/-!
# The pointwise product on `finsupp`.

TODO per issue #1864:
We intend to remove the convolution product on finsupp, and define
it only on a type synonym `add_monoid_algebra`. After we've done this,
it would be good to make this the default product on `finsupp`.
-/

noncomputable theory
open_locale classical

open finset

universes u₁ u₂ u₃ u₄ u₅
variables {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace finsupp

/-! ### Declarations about the pointwise product on `finsupp`s -/

section
variables [mul_zero_class β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : has_mul (α →₀ β) := ⟨zip_with (*) (mul_zero 0)⟩

@[simp] lemma mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
rfl

lemma support_mul {g₁ g₂ : α →₀ β} : (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
begin
  intros a h,
  simp only [mul_apply, mem_support_iff] at h,
  simp only [mem_support_iff, mem_inter, ne.def],
  rw ←not_or_distrib,
  intro w,
  apply h,
  cases w; { rw w, simp },
end
end

instance [semiring β] : semigroup (α →₀ β) :=
{ mul       := (*),
  mul_assoc := λ f g h, by { ext, simp only [mul_apply, mul_assoc], }, }

instance [ring β] : distrib (α →₀ β) :=
{ left_distrib := λ f g h, by { ext, simp only [mul_apply, add_apply, left_distrib] {proj := ff} },
  right_distrib := λ f g h, by { ext, simp only [mul_apply, add_apply, right_distrib] {proj := ff} },
  ..(infer_instance : semigroup (α →₀ β)),
  ..(infer_instance : add_comm_group (α →₀ β)) }

-- If `non_unital_semiring` existed in the algebraic hierarchy, we could produce one here.

end finsupp
