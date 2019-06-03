/-
Copyright (c) 2019 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

(Semi)conjugate functions.

Most constructions here can be restated for morphisms in
categories. However, applying such definitions and lemmas to functions
between sorts from different universes would require using `(p)ulift`
in some tricky way.
-/

import data.rel data.quot

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

variables (f₁ : α → α) (f₂ : β → β)
          {f₁' : α → α} {f₂' : β → β} {f₃ : γ → γ}

namespace function
  /-- Some sources require `g` to be surjective; if `g` is bijective, then `f₁` is conjugate to `f₂`. -/
  def semiconj_by (g : α → β) : rel (α → α) (β → β) := λ f₁ f₂, ∀ x : α, g (f₁ x) = f₂ (g x)

  namespace semiconj_by
    variables {f₁ f₂} {g g₁ : α → β} {g₂ : β → γ}

    lemma refl : semiconj_by id f₁ f₁ := assume x, rfl

    lemma trans (h₁ : semiconj_by g₁ f₁ f₂) (h₂ : semiconj_by g₂ f₂ f₃) : semiconj_by (g₂ ∘ g₁) f₁ f₃ :=
    assume x,
    show g₂ (g₁ (f₁ x)) = f₃ (g₂ (g₁ x)),
    by rw [h₁, h₂]

    lemma comp (h₁ : semiconj_by g f₁ f₂) (h₂ : semiconj_by g f₁' f₂') : semiconj_by g (f₁ ∘ f₁') (f₂ ∘ f₂') :=
    assume x,
    show g (f₁ (f₁' x)) = f₂ (f₂' (g x)),
    by rw [h₁, h₂]

    lemma quot (f : α → α) (r : rel α α) (h : ∀ x y, r x y → r (f x) (f y)) :
      semiconj_by (quot.mk r) f (quot.map f h) :=
    assume x,
    rfl
  end semiconj_by

  structure is_semiconj :=
  (hom : α → β)
  (conj : semiconj_by hom f₁ f₂)

  namespace is_semiconj
    @[refl] def refl : is_semiconj f₁ f₁ :=
    ⟨_, semiconj_by.refl⟩

    @[trans] def trans (h₁ : is_semiconj f₁ f₂) (h₂ : is_semiconj f₂ f₃) : is_semiconj f₁ f₃ :=
    ⟨_, semiconj_by.trans h₁.conj h₂.conj⟩

    lemma quot (f : α → α) (r : rel α α) (h : ∀ x y, r x y → r (f x) (f y)) :
      is_semiconj f (quot.map f h) :=
    ⟨_, semiconj_by.quot f r h⟩
  end is_semiconj

  lemma conj_to_semiconj_by (e : α ≃ β) : semiconj_by e.to_fun f₁ (e.conj f₁) :=
  assume x,
  show _ = e.to_fun (f₁ (e.inv_fun _)),
  by rw e.left_inv

  lemma conj_of_semiconj_by {e : α ≃ β} (h : semiconj_by e.to_fun f₁ f₂) :
    ∀ y, e.conj f₁ y = f₂ y :=
  assume y,
  show e.to_fun (f₁ _) = _,
  by rw [h, e.right_inv]

  structure is_conj :=
  (hom : α ≃ β)
  (conj : ∀ y, hom.conj f₁ y = f₂ y)

  variables {f₁ f₂ f₃}

  namespace is_conj
    def mk' (e : α ≃ β) (f : α → α) : is_conj f (e.conj f) :=
    ⟨e, λ x, rfl⟩

    @[refl] def refl : is_conj f₁ f₁ :=
    ⟨by refl, λ y, rfl⟩

    @[trans] def trans (h₁ : is_conj f₁ f₂) (h₂ : is_conj f₂ f₃) : is_conj f₁ f₃ :=
    { hom := h₁.hom.trans h₂.hom,
      conj := assume z,
              show (h₂.hom.to_fun $ h₁.hom.conj f₁ $ h₂.hom.inv_fun z) = f₃ z,
              by rw [h₁.conj]; exact h₂.conj z }

    @[symm] def symm (h : is_conj f₁ f₂) : is_conj f₂ f₁ :=
    { hom := h.hom.symm,
      conj := assume x,
              show (h.hom.inv_fun $ f₂ $ h.hom.to_fun x) = f₁ x,
              from (h.conj $ h.hom.to_fun x) ▸
                show (h.hom.inv_fun $ h.hom.to_fun $ f₁ $ h.hom.inv_fun $ h.hom.to_fun x) = f₁ x,
                by rw [h.hom.left_inv, h.hom.left_inv] }

    def to_semiconj_by (h : is_conj f₁ f₂) : semiconj_by h.hom.to_fun f₁ f₂ :=
    λ x, (h.conj $ h.hom.to_fun x) ▸ conj_to_semiconj_by f₁ h.hom x

    def to_semiconj_by_inv (h : is_conj f₁ f₂) : semiconj_by h.hom.inv_fun f₂ f₁ :=
    h.symm.to_semiconj_by

    def to_is_semiconj (h : is_conj f₁ f₂) : is_semiconj f₁ f₂ :=
    { hom := h.hom.to_fun,
      conj := h.to_semiconj_by }

    def of_semiconj_by {e : α ≃ β} (h : semiconj_by e.to_fun f₁ f₂) :
      is_conj f₁ f₂ :=
    { hom := e,
      conj := conj_of_semiconj_by f₁ f₂ h }
  end is_conj

  def semiconj_by_equiv_symm {e : α ≃ β} (h : semiconj_by e.to_fun f₁ f₂) :
    semiconj_by e.inv_fun f₂ f₁ :=
  (is_conj.of_semiconj_by h).to_semiconj_by_inv
end function
