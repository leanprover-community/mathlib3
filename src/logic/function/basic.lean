/-
Copyright (c) 2016 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import logic.basic
import data.option.defs

/-!
# Miscellaneous function constructions and lemmas
-/

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

theorem injective.eq_iff' (I : injective f) {a b : α} {c : β} (h : f b = c) :
  f a = c ↔ a = b :=
h ▸ I.eq_iff

lemma injective.ne (hf : injective f) {a₁ a₂ : α} : a₁ ≠ a₂ → f a₁ ≠ f a₂ :=
mt (assume h, hf h)

lemma injective.ne_iff (hf : injective f) {x y : α} : f x ≠ f y ↔ x ≠ y :=
⟨mt $ congr_arg f, hf.ne⟩

lemma injective.ne_iff' (hf : injective f) {x y : α} {z : β} (h : f y = z) :
  f x ≠ z ↔ x ≠ y :=
h ▸ hf.ne_iff

/-- If the co-domain `β` of an injective function `f : α → β` has decidable equality, then
the domain `α` also has decidable equality. -/
def injective.decidable_eq [decidable_eq β] (I : injective f) : decidable_eq α :=
λ a b, decidable_of_iff _ I.eq_iff

lemma injective.of_comp {γ : Sort w} {g : γ → α} (I : injective (f ∘ g)) : injective g :=
λ x y h, I $ show f (g x) = f (g y), from congr_arg f h

lemma surjective.of_comp {γ : Sort w} {g : γ → α} (S : surjective (f ∘ g)) : surjective f :=
λ y, let ⟨x, h⟩ := S y in ⟨g x, h⟩

instance decidable_eq_pfun (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, decidable_eq (α hp)] : decidable_eq (Π hp, α hp)
| f g := decidable_of_iff (∀ hp, f hp = g hp) funext_iff.symm

theorem surjective.forall {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∀ y, p y) ↔ ∀ x, p (f x) :=
⟨λ h x, h (f x), λ h y, let ⟨x, hx⟩ := hf y in hx ▸ h x⟩

theorem surjective.forall₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∀ y₁ y₂, p y₁ y₂) ↔ ∀ x₁ x₂, p (f x₁) (f x₂) :=
hf.forall.trans $ forall_congr $ λ x, hf.forall

theorem surjective.forall₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∀ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∀ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.forall.trans $ forall_congr $ λ x, hf.forall₂

theorem surjective.exists {f : α → β} (hf : surjective f) {p : β → Prop} :
  (∃ y, p y) ↔ ∃ x, p (f x) :=
⟨λ ⟨y, hy⟩, let ⟨x, hx⟩ := hf y in ⟨x, hx.symm ▸ hy⟩, λ ⟨x, hx⟩, ⟨f x, hx⟩⟩

theorem surjective.exists₂ {f : α → β} (hf : surjective f) {p : β → β → Prop} :
  (∃ y₁ y₂, p y₁ y₂) ↔ ∃ x₁ x₂, p (f x₁) (f x₂) :=
hf.exists.trans $ exists_congr $ λ x, hf.exists

theorem surjective.exists₃ {f : α → β} (hf : surjective f) {p : β → β → β → Prop} :
  (∃ y₁ y₂ y₃, p y₁ y₂ y₃) ↔ ∃ x₁ x₂ x₃, p (f x₁) (f x₂) (f x₃) :=
hf.exists.trans $ exists_congr $ λ x, hf.exists₂

/-- Cantor's diagonal argument implies that there are no surjective functions from `α`
to `set α`. -/
theorem cantor_surjective {α} (f : α → set α) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 $ iff_of_eq (congr_fun e D)

/-- Cantor's diagonal argument implies that there are no injective functions from `set α` to `α`. -/
theorem cantor_injective {α : Type*} (f : (set α) → α) :
  ¬ function.injective f | i :=
cantor_surjective (λ a b, ∀ U, a = f U → U b) $
right_inverse.surjective (λ U, funext $ λ a, propext ⟨λ h, h U rfl, λ h' U' e, i e ▸ h'⟩)

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

theorem left_inverse.right_inverse {f : α → β} {g : β → α} (h : left_inverse g f) :
  right_inverse f g := h

theorem right_inverse.left_inverse {f : α → β} {g : β → α} (h : right_inverse g f) :
  left_inverse f g := h

theorem left_inverse.surjective {f : α → β} {g : β → α} (h : left_inverse f g) :
  surjective f :=
h.right_inverse.surjective

theorem right_inverse.injective {f : α → β} {g : β → α} (h : right_inverse f g) :
  injective f :=
h.left_inverse.injective

theorem left_inverse.eq_right_inverse {f : α → β} {g₁ g₂ : β → α} (h₁ : left_inverse g₁ f)
  (h₂ : right_inverse g₂ f) :
  g₁ = g₂ :=
calc g₁ = g₁ ∘ f ∘ g₂ : by rw [h₂.comp_eq_id, comp.right_id]
    ... = g₂          : by rw [← comp.assoc, h₁.comp_eq_id, comp.left_id]

local attribute [instance, priority 10] classical.prop_decidable

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
variables {α : Type u} [n : nonempty α] {β : Sort v} {f : α → β} {s : set α} {a : α} {b : β}
include n
local attribute [instance, priority 10] classical.prop_decidable

/-- Construct the inverse for a function `f` on domain `s`. This function is a right inverse of `f`
on `f '' s`. -/
noncomputable def inv_fun_on (f : α → β) (s : set α) (b : β) : α :=
if h : ∃a, a ∈ s ∧ f a = b then classical.some h else classical.choice n

theorem inv_fun_on_pos (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s ∧ f (inv_fun_on f s b) = b :=
by rw [bex_def] at h; rw [inv_fun_on, dif_pos h]; exact classical.some_spec h

theorem inv_fun_on_mem (h : ∃a∈s, f a = b) : inv_fun_on f s b ∈ s := (inv_fun_on_pos h).left

theorem inv_fun_on_eq (h : ∃a∈s, f a = b) : f (inv_fun_on f s b) = b := (inv_fun_on_pos h).right

theorem inv_fun_on_eq' (h : ∀ (x ∈ s) (y ∈ s), f x = f y → x = y) (ha : a ∈ s) :
  inv_fun_on f s (f a) = a :=
have ∃a'∈s, f a' = f a, from ⟨a, ha, rfl⟩,
h _ (inv_fun_on_mem this) _ ha (inv_fun_on_eq this)

theorem inv_fun_on_neg (h : ¬ ∃a∈s, f a = b) : inv_fun_on f s b = classical.choice n :=
by rw [bex_def] at h; rw [inv_fun_on, dif_neg h]

/-- The inverse of a function (which is a left inverse if `f` is injective
  and a right inverse if `f` is surjective). -/
noncomputable def inv_fun (f : α → β) : β → α := inv_fun_on f set.univ

theorem inv_fun_eq (h : ∃a, f a = b) : f (inv_fun f b) = b :=
inv_fun_on_eq $ let ⟨a, ha⟩ := h in ⟨a, trivial, ha⟩

lemma inv_fun_neg (h : ¬ ∃ a, f a = b) : inv_fun f b = classical.choice n :=
by refine inv_fun_on_neg (mt _ h); exact assume ⟨a, _, ha⟩, ⟨a, ha⟩

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
(left_inverse_inv_fun hf).surjective

lemma inv_fun_comp (hf : injective f) : inv_fun f ∘ f = id := funext $ left_inverse_inv_fun hf

end inv_fun

section inv_fun
variables {α : Type u} [i : nonempty α] {β : Sort v} {f : α → β}
include i

lemma injective.has_left_inverse (hf : injective f) : has_left_inverse f :=
⟨inv_fun f, left_inverse_inv_fun hf⟩

lemma injective_iff_has_left_inverse : injective f ↔ has_left_inverse f :=
⟨injective.has_left_inverse, has_left_inverse.injective⟩

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
⟨surjective.has_right_inverse, has_right_inverse.surjective⟩

lemma bijective_iff_has_inverse : bijective f ↔ ∃ g, left_inverse g f ∧ right_inverse g f :=
⟨λ hf, ⟨_, left_inverse_surj_inv hf, right_inverse_surj_inv hf.2⟩,
 λ ⟨g, gl, gr⟩, ⟨gl.injective,  gr.surjective⟩⟩

lemma injective_surj_inv (h : surjective f) : injective (surj_inv h) :=
(right_inverse_surj_inv h).injective

end surj_inv

section update
variables {α : Sort u} {β : α → Sort v} {α' : Sort w} [decidable_eq α] [decidable_eq α']

/-- Replacing the value of a function at a given point by a given value. -/
def update (f : Πa, β a) (a' : α) (v : β a') (a : α) : β a :=
if h : a = a' then eq.rec v h.symm else f a

@[simp] lemma update_same (a : α) (v : β a) (f : Πa, β a) : update f a v a = v :=
dif_pos rfl

@[simp] lemma update_noteq {a a' : α} (h : a ≠ a') (v : β a') (f : Πa, β a) : update f a' v a = f a :=
dif_neg h

@[simp] lemma update_eq_self (a : α) (f : Πa, β a) : update f a (f a) = f :=
begin
  refine funext (λi, _),
  by_cases h : i = a,
  { rw h, simp },
  { simp [h] }
end

lemma update_comp {β : Sort v} (f : α → β) {g : α' → α} (hg : injective g) (a : α') (v : β) :
  (update f (g a) v) ∘ g = update (f ∘ g) a v :=
begin
  refine funext (λi, _),
  by_cases h : i = a,
  { rw h, simp },
  { simp [h, hg.ne] }
end

lemma comp_update {α' : Sort*} {β : Sort*} (f : α' → β) (g : α → α') (i : α) (v : α') :
  f ∘ (update g i v) = update (f ∘ g) i (f v) :=
begin
  refine funext (λj, _),
  by_cases h : j = i,
  { rw h, simp },
  { simp [h] }
end

theorem update_comm {α} [decidable_eq α] {β : α → Sort*}
  {a b : α} (h : a ≠ b) (v : β a) (w : β b) (f : Πa, β a) :
  update (update f a v) b w = update (update f b w) a v :=
begin
  funext c, simp [update],
  by_cases h₁ : c = b; by_cases h₂ : c = a; try {simp [h₁, h₂]},
  cases h (h₂.symm.trans h₁),
end

@[simp] theorem update_idem {α} [decidable_eq α] {β : α → Sort*}
  {a : α} (v w : β a) (f : Πa, β a) : update (update f a v) a w = update f a w :=
by {funext b, by_cases b = a; simp [update, h]}

end update

lemma uncurry_def {α β γ} (f : α → β → γ) : uncurry f = (λp, f p.1 p.2) :=
rfl

section bicomp
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ε : Type*}

/-- Compose a binary function `f` with a pair of unary functions `g` and `h`.
If both arguments of `f` have the same type and `g = h`, then `bicompl f g g = f on g`. -/
def bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) (a b) :=
f (g a) (h b)

/-- Compose an unary function `f` with a binary function `g`. -/
def bicompr (f : γ → δ) (g : α → β → γ) (a b) :=
f (g a b)

-- Suggested local notation:
local notation f `∘₂` g := bicompr f g

lemma uncurry_bicompr (f : α → β → γ) (g : γ → δ) :
  uncurry (g ∘₂ f) = (g ∘ uncurry f) := rfl

lemma uncurry_bicompl (f : γ → δ → ε) (g : α → γ) (h : β → δ) :
  uncurry (bicompl f g h) = (uncurry f) ∘ (prod.map g h) :=
rfl

end bicomp

/-- A function is involutive, if `f ∘ f = id`. -/
def involutive {α} (f : α → α) : Prop := ∀ x, f (f x) = x

lemma involutive_iff_iter_2_eq_id {α} {f : α → α} : involutive f ↔ (f^[2] = id) :=
funext_iff.symm

namespace involutive
variables {α : Sort u} {f : α → α} (h : involutive f)

protected lemma left_inverse : left_inverse f f := h
protected lemma right_inverse : right_inverse f f := h

protected lemma injective : injective f := h.left_inverse.injective
protected lemma surjective : surjective f := λ x, ⟨f x, h x⟩
protected lemma bijective : bijective f := ⟨h.injective, h.surjective⟩

end involutive

/-- The property of a binary function `f : α → β → γ` being injective.
  Mathematically this should be thought of as the corresponding function `α × β → γ` being injective.
-/
@[reducible] def injective2 {α β γ} (f : α → β → γ) : Prop :=
∀ ⦃a₁ a₂ b₁ b₂⦄, f a₁ b₁ = f a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂

namespace injective2
variables {α β γ : Type*} (f : α → β → γ)

protected lemma left (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : a₁ = a₂ :=
(hf h).1

protected lemma right (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ (h : f a₁ b₁ = f a₂ b₂) : b₁ = b₂ :=
(hf h).2

lemma eq_iff (hf : injective2 f) ⦃a₁ a₂ b₁ b₂⦄ : f a₁ b₁ = f a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
⟨λ h, hf h, λ⟨h1, h2⟩, congr_arg2 f h1 h2⟩

end injective2

end function

/-- `s.piecewise f g` is the function equal to `f` on the set `s`, and to `g` on its complement. -/
def set.piecewise {α : Type u} {β : α → Sort v} (s : set α) (f g : Πi, β i) [∀j, decidable (j ∈ s)] :
  Πi, β i :=
λi, if i ∈ s then f i else g i
