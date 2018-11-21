/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Miscellaneous function constructions and lemmas.
-/
import logic.basic data.option

universes u v w

namespace function

section
variables {α : Sort u} {β : Sort v} {f : α → β}

lemma hfunext {α α': Sort u} {β : α → Sort v} {β' : α' → Sort v} {f : Πa, β a} {f' : Πa, β' a}
  (hα : α = α') (h : ∀a a', a == a' → f a == f' a') : f == f' :=
begin
  subst hα,
  have : ∀a, f a == f' a,
  { intro a, exact h a a (heq.refl a) },
  have : β = β',
  { funext a, exact type_eq_of_heq (this a) },
  subst this,
  apply heq_of_eq,
  funext a,
  exact eq_of_heq (this a)
end

lemma funext_iff {β : α → Sort*} {f₁ f₂ : Π (x : α), β x} : f₁ = f₂ ↔ (∀a, f₁ a = f₂ a) :=
iff.intro (assume h a, h ▸ rfl) funext

lemma comp_apply {α : Sort u} {β : Sort v} {φ : Sort w} (f : β → φ) (g : α → β) (a : α) :
  (f ∘ g) a = f (g a) := rfl

@[simp] theorem injective.eq_iff (I : injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨@I _ _, congr_arg f⟩

def injective.decidable_eq [decidable_eq β] (I : injective f) : decidable_eq α
| a b := decidable_of_iff _ I.eq_iff

instance decidable_eq_pfun (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, decidable_eq (α hp)] : decidable_eq (Π hp, α hp)
| f g := decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem cantor_surjective {α} (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

theorem cantor_injective {α : Type*} (f : (α → Prop) → α) :
  ¬ function.injective f | i :=
cantor_surjective (λ a b, ∀ U, a = f U → U b) $
surjective_of_has_right_inverse ⟨f, λ U, funext $
  λ a, propext ⟨λ h, h U rfl, λ h' U' e, i e ▸ h'⟩⟩

/-- `g` is a partial inverse to `f` (an injective but not necessarily
  surjective function) if `g y = some x` implies `f x = y`, and `g y = none`
  implies that `y` is not in the range of `f`. -/
def is_partial_inv {α β} (f : α → β) (g : β → option α) : Prop :=
∀ x y, g y = some x ↔ f x = y

theorem is_partial_inv_left {α β} {f : α → β} {g} (H : is_partial_inv f g) (x) : g (f x) = some x :=
(H _ _).2 rfl

theorem injective_of_partial_inv {α β} {f : α → β} {g} (H : is_partial_inv f g) : injective f :=
λ a b h, option.some.inj $ ((H _ _).2 h).symm.trans ((H _ _).2 rfl)

theorem injective_of_partial_inv_right {α β} {f : α → β} {g} (H : is_partial_inv f g)
 (x y b) (h₁ : b ∈ g x) (h₂ : b ∈ g y) : x = y :=
((H _ _).1 h₁).symm.trans ((H _ _).1 h₂)

theorem left_inverse.comp_eq_id {f : α → β} {g : β → α} (h : left_inverse f g) : f ∘ g = id :=
funext h

theorem right_inverse.comp_eq_id {f : α → β} {g : β → α} (h : right_inverse f g) : g ∘ f = id :=
funext h

theorem left_inverse.comp {γ} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : left_inverse f g) (hh : left_inverse h i) : left_inverse (h ∘ f) (g ∘ i) :=
assume a, show h (f (g (i a))) = a, by rw [hf (i a), hh a]

theorem right_inverse.comp {γ} {f : α → β} {g : β → α} {h : β → γ} {i : γ → β}
  (hf : right_inverse f g) (hh : right_inverse h i) : right_inverse (h ∘ f) (g ∘ i) :=
left_inverse.comp hh hf

local attribute [instance] classical.prop_decidable

/-- We can use choice to construct explicitly a partial inverse for
  a given injective function `f`. -/
noncomputable def partial_inv {α β} (f : α → β) (b : β) : option α :=
if h : ∃ a, f a = b then some (classical.some h) else none

theorem partial_inv_of_injective {α β} {f : α → β} (I : injective f) :
  is_partial_inv f (partial_inv f) | a b :=
⟨λ h, if h' : ∃ a, f a = b then begin
    rw [partial_inv, dif_pos h'] at h,
    injection h with h, subst h,
    apply classical.some_spec h'
  end else by rw [partial_inv, dif_neg h'] at h; contradiction,
 λ e, e ▸ have h : ∃ a', f a' = f a, from ⟨_, rfl⟩,
   (dif_pos h).trans (congr_arg _ (I $ classical.some_spec h))⟩

theorem partial_inv_left {α β} {f : α → β} (I : injective f) : ∀ x, partial_inv f (f x) = some x :=
is_partial_inv_left (partial_inv_of_injective I)

end

section inv_fun
variables {α : Type u} [inhabited α] {β : Sort v} {f : α → β} {s : set α} {a : α} {b : β}

local attribute [instance] classical.prop_decidable

/-- Construct the inverse for a function `f` on domain `s`. -/
noncomputable def inv_fun_on (f : α → β) (s : set α) (b : β) : α :=
if h : ∃a, a ∈ s ∧ f a = b then classical.some h else default α

theorem inv_fun_on_pos (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
by rw [bex_def] at h; rw [inv_fun_on, dif_pos h]; exact classical.some_spec h

theorem inv_fun_on_mem (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s := (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃a∈s, f a = b) : f (inv_fun_on f s b) = b := (inv_fun_on_pos h).right

theorem inv_fun_on_eq' (h : ∀ x y ∈ s, f x = f y → x = y) (ha : a ∈ s) :
  inv_fun_on f s (f a) = a :=
have ∃a'∈s, f a' = f a, from ⟨a, ha, rfl⟩,
h _ _ (inv_fun_on_mem this) ha (inv_fun_on_eq this)

theorem inv_fun_on_neg (h : ¬ ∃a∈s, f a = b) : inv_fun_on f s b = default α :=
by rw [bex_def] at h; rw [inv_fun_on, dif_neg h]

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α := inv_fun_on f set.univ

theorem inv_fun_eq (h : ∃a, f a = b) : f (inv_fun f b) = b :=
inv_fun_on_eq $ let ⟨a, ha⟩ := h in ⟨a, trivial, ha⟩

theorem inv_fun_eq_of_injective_of_right_inverse {g : β → α}
  (hf : injective f) (hg : right_inverse g f) : inv_fun f = g :=
funext $ assume b,
hf begin rw [hg b], exact inv_fun_eq ⟨g b, hg b⟩ end

lemma right_inverse_inv_fun (hf : surjective f) : right_inverse (inv_fun f) f :=
assume b, inv_fun_eq $ hf b

lemma left_inverse_inv_fun (hf : injective f) : left_inverse (inv_fun f) f :=
assume b,
have f (inv_fun f (f b)) = f b,
  from inv_fun_eq ⟨b, rfl⟩,
hf this

lemma inv_fun_surjective (hf : injective f) : surjective (inv_fun f) :=
surjective_of_has_right_inverse ⟨_, left_inverse_inv_fun hf⟩

lemma inv_fun_comp (hf : injective f) : inv_fun f ∘ f = id := funext $ left_inverse_inv_fun hf

lemma injective.has_left_inverse (hf : injective f) : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

lemma injective_iff_has_left_inverse : injective f ↔ has_left_inverse f :=
⟨injective.has_left_inverse, injective_of_has_left_inverse⟩

end inv_fun

section surj_inv
variables {α : Sort u} {β : Sort v} {f : α → β}

/-- The inverse of a surjective function. (Unlike `inv_fun`, this does not require
  `α` to be inhabited.) -/
noncomputable def surj_inv {f : α → β} (h : surjective f) (b : β) : α := classical.some (h b)

lemma surj_inv_eq (h : surjective f) (b) : f (surj_inv h b) = b := classical.some_spec (h b)

lemma right_inverse_surj_inv (hf : surjective f) : right_inverse (surj_inv hf) f :=
surj_inv_eq hf

lemma left_inverse_surj_inv (hf : bijective f) : left_inverse (surj_inv hf.2) f :=
right_inverse_of_injective_of_left_inverse hf.1 (right_inverse_surj_inv hf.2)

lemma surjective.has_right_inverse (hf : surjective f) : has_right_inverse f :=
⟨_, right_inverse_surj_inv hf⟩

lemma surjective_iff_has_right_inverse : surjective f ↔ has_right_inverse f :=
⟨surjective.has_right_inverse, surjective_of_has_right_inverse⟩

lemma bijective_iff_has_inverse : bijective f ↔ ∃ g, left_inverse g f ∧ right_inverse g f :=
⟨λ hf, ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩,
 λ ⟨g, gl, gr⟩, ⟨injective_of_left_inverse gl, surjective_of_has_right_inverse ⟨_, gr⟩⟩⟩

lemma injective_surj_inv (h : surjective f) : injective (surj_inv h) :=
injective_of_has_left_inverse ⟨f, right_inverse_surj_inv h⟩

end surj_inv

section update
variables {α : Sort u} {β : α → Sort v} [decidable_eq α]

def update (f : Πa, β a) (a' : α) (v : β a') (a : α) : β a :=
if h : a = a' then eq.rec v h.symm else f a

@[simp] lemma update_same {a : α} {v : β a} {f : Πa, β a} : update f a v a = v :=
dif_pos rfl

@[simp] lemma update_noteq {a a' : α} {v : β a'} {f : Πa, β a} (h : a ≠ a') : update f a' v a = f a :=
dif_neg h

end update

lemma uncurry_def {α β γ} (f : α → β → γ) : uncurry f = (λp, f p.1 p.2) :=
funext $ assume ⟨a, b⟩, rfl
end function
