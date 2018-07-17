/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu

Functions over sets.
-/
import data.set.basic
open function

namespace set
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

/- maps to -/

/-- `maps_to f a b` means that the image of `a` is contained in `b`. -/
@[reducible] def maps_to (f : α → β) (a : set α) (b : set β) : Prop := a ⊆ f ⁻¹' b

theorem maps_to_of_eq_on {f1 f2 : α → β} {a : set α} {b : set β} (h₁ : eq_on f1 f2 a)
    (h₂ : maps_to f1 a b) :
  maps_to f2 a b :=
λ x h, by rw [mem_preimage_eq, ← h₁ _ h]; exact h₂ h

theorem maps_to_comp {g : β → γ} {f : α → β} {a : set α} {b : set β} {c : set γ}
   (h₁ : maps_to g b c) (h₂ : maps_to f a b) : maps_to (g ∘ f) a c :=
λ x h, h₁ (h₂ h)

theorem maps_to_univ (f : α → β) (a) : maps_to f a univ :=
λ x h, trivial

theorem image_subset_of_maps_to_of_subset {f : α → β} {a c : set α} {b : set β} (h₁ : maps_to f a b)
  (h₂ : c ⊆ a) :
  f '' c ⊆ b :=
λ y hy, let ⟨x, hx, heq⟩ := hy in
by rw [←heq]; apply h₁; apply h₂; assumption

theorem image_subset_of_maps_to {f : α → β} {a : set α} {b : set β} (h : maps_to f a b) :
  f '' a ⊆ b :=
image_subset_of_maps_to_of_subset h (subset.refl _)

/- injectivity -/

/-- `f` is injective on `a` if the restriction of `f` to `a` is injective. -/
@[reducible] def inj_on (f : α → β) (a : set α) : Prop :=
∀⦃x1 x2 : α⦄, x1 ∈ a → x2 ∈ a → f x1 = f x2 → x1 = x2

theorem inj_on_empty (f : α → β) : inj_on f ∅ :=
λ _ _ h₁ _ _, false.elim h₁

theorem inj_on_of_eq_on {f1 f2 : α → β} {a : set α} (h₁ : eq_on f1 f2 a)
    (h₂ : inj_on f1 a) :
  inj_on f2 a :=
λ _ _ h₁' h₂' heq, by apply h₂ h₁' h₂'; rw [h₁, heq, ←h₁]; repeat {assumption}

theorem inj_on_comp {g : β → γ} {f : α → β} {a : set α} {b : set β}
    (h₁ : maps_to f a b) (h₂ : inj_on g b) (h₃: inj_on f a) :
  inj_on (g ∘ f) a :=
λ _ _ h₁' h₂' heq,
by apply h₃ h₁' h₂'; apply h₂; repeat {apply h₁, assumption}; assumption

theorem inj_on_of_inj_on_of_subset {f : α → β} {a b : set α} (h₁ : inj_on f b) (h₂ : a ⊆ b) :
  inj_on f a :=
λ _ _ h₁' h₂' heq, h₁ (h₂ h₁') (h₂ h₂') heq

lemma injective_iff_inj_on_univ {f : α → β} : injective f ↔ inj_on f univ :=
iff.intro (λ h _ _ _ _ heq, h heq) (λ h _ _ heq, h trivial trivial heq)

lemma inj_on_iff_injective {f : α → β} {s : set α} : inj_on f s ↔ injective (λ x:s, f x.1) :=
⟨λ H a b h, subtype.eq $ H a.2 b.2 h,
 λ H a b as bs h, congr_arg subtype.val $ @H ⟨a, as⟩ ⟨b, bs⟩ h⟩

/- surjectivity -/

/-- `f` is surjective from `a` to `b` if `b` is contained in the image of `a`. -/
@[reducible] def surj_on (f : α → β) (a : set α) (b : set β) : Prop := b ⊆ f '' a

theorem surj_on_of_eq_on {f1 f2 : α → β} {a : set α} {b : set β} (h₁ : eq_on f1 f2 a)
    (h₂ : surj_on f1 a b) :
  surj_on f2 a b :=
λ _ h, let ⟨x, hx⟩ := h₂ h in
⟨x, hx.left, by rw [←h₁ _ hx.left]; exact hx.right⟩

theorem surj_on_comp {g : β → γ} {f : α → β} {a : set α} {b : set β} {c : set γ}
  (h₁ : surj_on g b c) (h₂ : surj_on f a b) :
  surj_on (g ∘ f) a c :=
λ z h, let ⟨y, hy⟩ := h₁ h, ⟨x, hx⟩ := h₂ hy.left in
       ⟨x, hx.left, calc g (f x) = g y : by rw [hx.right]
                          ...    = z   : hy.right⟩

lemma surjective_iff_surj_on_univ {f : α → β} : surjective f ↔ surj_on f univ univ :=
by simp [surjective, surj_on, subset_def]

lemma surj_on_iff_surjective {f : α → β} {s : set α} : surj_on f s univ ↔ surjective (λ x:s, f x.1) :=
⟨λ H b, let ⟨a, as, e⟩ := @H b trivial in ⟨⟨a, as⟩, e⟩,
 λ H b _, let ⟨⟨a, as⟩, e⟩ := H b in ⟨a, as, e⟩⟩

lemma image_eq_of_maps_to_of_surj_on {f : α → β} {a : set α} {b : set β}
    (h₁ : maps_to f a b) (h₂ : surj_on f a b) :
  f '' a = b :=
eq_of_subset_of_subset (image_subset_of_maps_to h₁) h₂

/- bijectivity -/

/-- `f` is bijective from `a` to `b` if `f` is injective on `a` and `f '' a = b`. -/
@[reducible] def bij_on (f : α → β) (a : set α) (b : set β) : Prop :=
maps_to f a b ∧ inj_on f a ∧ surj_on f a b

lemma maps_to_of_bij_on {f : α → β} {a : set α} {b : set β} (h : bij_on f a b) :
      maps_to f a b :=
h.left

lemma inj_on_of_bij_on {f : α → β} {a : set α} {b : set β} (h : bij_on f a b) :
      inj_on f a :=
h.right.left

lemma surj_on_of_bij_on {f : α → β} {a : set α} {b : set β} (h : bij_on f a b) :
      surj_on f a b :=
h.right.right

lemma bij_on.mk {f : α → β} {a : set α} {b : set β}
                (h₁ : maps_to f a b) (h₂ : inj_on f a) (h₃ : surj_on f a b) :
      bij_on f a b :=
⟨h₁, h₂, h₃⟩

theorem bij_on_of_eq_on {f1 f2 : α → β} {a : set α} {b : set β} (h₁ : eq_on f1 f2 a)
     (h₂ : bij_on f1 a b) : bij_on f2 a b :=
let ⟨map, inj, surj⟩ := h₂ in
⟨maps_to_of_eq_on h₁ map, inj_on_of_eq_on h₁ inj, surj_on_of_eq_on h₁ surj⟩

lemma image_eq_of_bij_on {f : α → β} {a : set α} {b : set β} (h : bij_on f a b) :
  f '' a = b :=
image_eq_of_maps_to_of_surj_on h.left h.right.right

theorem bij_on_comp {g : β → γ} {f : α → β} {a : set α} {b : set β} {c : set γ}
  (h₁ : bij_on g b c) (h₂: bij_on f a b) :
  bij_on (g ∘ f) a c :=
let ⟨gmap, ginj, gsurj⟩ := h₁, ⟨fmap, finj, fsurj⟩ := h₂ in
⟨maps_to_comp gmap fmap, inj_on_comp fmap ginj finj, surj_on_comp gsurj fsurj⟩

lemma bijective_iff_bij_on_univ {f : α → β} : bijective f ↔ bij_on f univ univ :=
iff.intro
(λ h, let ⟨inj, surj⟩ := h in
⟨maps_to_univ f _, iff.mp injective_iff_inj_on_univ inj, iff.mp surjective_iff_surj_on_univ surj⟩)
(λ h, let ⟨map, inj, surj⟩ := h in
⟨iff.mpr injective_iff_inj_on_univ inj, iff.mpr surjective_iff_surj_on_univ surj⟩)

/- left inverse -/

/-- `g` is a left inverse to `f` on `a` means that `g (f x) = x` for all `x ∈ a`. -/
@[reducible] def left_inv_on (g : β → α) (f : α → β) (a : set α) : Prop :=
∀ x ∈ a, g (f x) = x

theorem left_inv_on_of_eq_on_left {g1 g2 : β → α} {f : α → β} {a : set α} {b : set β}
  (h₁ : maps_to f a b) (h₂ : eq_on g1 g2 b) (h₃ : left_inv_on g1 f a) : left_inv_on g2 f a :=
λ x h,
calc
  g2 (f x) = g1 (f x) : eq.symm $ h₂ _ (h₁ h)
       ... = x        : h₃ _ h

theorem left_inv_on_of_eq_on_right {g : β → α} {f1 f2 : α → β} {a : set α}
  (h₁ : eq_on f1 f2 a) (h₂ : left_inv_on g f1 a) : left_inv_on g f2 a :=
λ x h,
calc
  g (f2 x) = g (f1 x) : congr_arg g (h₁ _ h).symm
       ... = x        : h₂ _ h

theorem inj_on_of_left_inv_on {g : β → α} {f : α → β} {a : set α} (h : left_inv_on g f a) :
  inj_on f a :=
λ x₁ x₂ h₁ h₂ heq,
calc
  x₁    = g (f x₁) : eq.symm $ h _ h₁
  ...   = g (f x₂) : congr_arg g heq
  ...   = x₂       : h _ h₂

theorem left_inv_on_comp {f' : β → α} {g' : γ → β} {g : β → γ} {f : α → β}
   {a : set α} {b : set β} (h₁ : maps_to f a b)
    (h₂ : left_inv_on f' f a) (h₃ : left_inv_on g' g b) : left_inv_on (f' ∘ g') (g ∘ f) a :=
λ x h,
calc
  (f' ∘ g') ((g ∘ f) x) = f' (f x) : congr_arg f' (h₃ _ (h₁ h))
  ...                   = x        : h₂ _ h

/- right inverse -/

/-- `g` is a right inverse to `f` on `b` if `f (g x) = x` for all `x ∈ b`. -/
@[reducible] def right_inv_on (g : β → α) (f : α → β) (b : set β) : Prop :=
left_inv_on f g b

theorem right_inv_on_of_eq_on_left {g1 g2 : β → α} {f : α → β} {a : set α} {b : set β}
  (h₁ : eq_on g1 g2 b) (h₂ : right_inv_on g1 f b) : right_inv_on g2 f b :=
left_inv_on_of_eq_on_right h₁ h₂

theorem right_inv_on_of_eq_on_right {g : β → α} {f1 f2 : α → β} {a : set α} {b : set β}
  (h₁ : maps_to g b a) (h₂ : eq_on f1 f2 a) (h₃ : right_inv_on g f1 b) : right_inv_on g f2 b :=
left_inv_on_of_eq_on_left h₁ h₂ h₃

theorem surj_on_of_right_inv_on {g : β → α} {f : α → β} {a : set α} {b : set β}
    (h₁ : maps_to g b a) (h₂ : right_inv_on g f b) :
  surj_on f a b :=
λ y h, ⟨g y, h₁ h, h₂ _ h⟩

theorem right_inv_on_comp {f' : β → α} {g' : γ → β} {g : β → γ} {f : α → β}
   {c : set γ} {b : set β} (g'cb : maps_to g' c b)
    (h₁ : right_inv_on f' f b) (h₂ : right_inv_on g' g c) : right_inv_on (f' ∘ g') (g ∘ f) c :=
left_inv_on_comp g'cb h₂ h₁

theorem right_inv_on_of_inj_on_of_left_inv_on {f : α → β} {g : β → α} {a : set α} {b : set β}
    (h₁ : maps_to f a b) (h₂ : maps_to g b a) (h₃ : inj_on f a) (h₄ : left_inv_on f g b) :
  right_inv_on f g a :=
λ x h, h₃ (h₂ $ h₁ h) h (h₄ _ (h₁ h))

theorem eq_on_of_left_inv_of_right_inv {g₁ g₂ : β → α} {f : α → β} {a : set α} {b : set β}
  (h₁ : maps_to g₂ b a) (h₂ : left_inv_on g₁ f a) (h₃ : right_inv_on g₂ f b) : eq_on g₁ g₂ b :=
λ y h,
calc
  g₁ y = (g₁ ∘ f ∘ g₂) y : congr_arg g₁ (h₃ _ h).symm
  ...  = g₂ y            : h₂ _ (h₁ h)

theorem left_inv_on_of_surj_on_right_inv_on {f : α → β} {g : β → α} {a : set α} {b : set β}
    (h₁ : surj_on f a b) (h₂ : right_inv_on f g a) :
  left_inv_on f g b :=
λ y h, let ⟨x, hx, heq⟩ := h₁ h in
calc
  (f ∘ g) y = (f ∘ g ∘ f) x : congr_arg (f ∘ g) heq.symm
  ...     = f x             : congr_arg f (h₂ _ hx)
  ...     = y               : heq

/- inverses -/

/-- `g` is an inverse to `f` viewed as a map from `a` to `b` -/
@[reducible] def inv_on (g : β → α) (f : α → β) (a : set α) (b : set β) : Prop :=
left_inv_on g f a ∧ right_inv_on g f b

theorem bij_on_of_inv_on {g : β → α} {f : α → β} {a : set α} {b : set β} (h₁ : maps_to f a b)
  (h₂ : maps_to g b a) (h₃ : inv_on g f a b) : bij_on f a b :=
⟨h₁, inj_on_of_left_inv_on h₃.left, surj_on_of_right_inv_on h₂ h₃.right⟩

end set
