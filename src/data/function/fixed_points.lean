/-
Copyright (c) 2019 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Fixed points of endomorphisms and permutations
-/

import data.rel data.function.conjugate

universes u v
variables {α : Type u} {β : Type v}

namespace function
  def fixed_points (f : α → α) : set α := { x | f x = x }

  instance fixed_points_dec [h : decidable_eq α] (f : α → α) :
    decidable_pred (fixed_points f) :=
  λ x, h (f x) x

  namespace fixed_points
    lemma mem_id (x : α) : x ∈ (fixed_points $ @id α) :=
    eq.refl x

    lemma id_eq_univ : fixed_points (@id α) = set.univ :=
    set.eq_univ_of_forall mem_id

    lemma mem_comp {f₁ f₂ : α → α} {x : α} :
      x ∈ fixed_points f₁ → x ∈ fixed_points f₂ → x ∈ fixed_points (f₁ ∘ f₂) :=
    assume (h₁ : _ = _) (h₂ : _ = _),
    show f₁ (f₂ x) = x,
    from h₂.symm ▸ h₁

    lemma comp_sub (f₁ f₂ : α → α) :
      fixed_points f₁ ∩ fixed_points f₂ ⊆ fixed_points (f₁ ∘ f₂) :=
    λ x ⟨h₁, h₂⟩, mem_comp h₁ h₂

    lemma mem_iterate {f : α → α} {x : α} (h : x ∈ fixed_points f) (n : nat) :
      x ∈ fixed_points (f^[n]) :=
    nat.rec_on n (mem_id x) (λ n ihn, @mem_comp _ (f^[n]) _ _ ihn h)

    lemma iterate_sub (f : α → α) (n : nat) :
      fixed_points f ⊆ fixed_points (f^[n]) :=
    λ x h, mem_iterate h n
  end fixed_points
end function

namespace function
  variables {f₁ : α → α} {f₂ : β → β}
  namespace is_semiconj
    variables (h : is_semiconj f₁ f₂)

    lemma mem_fixed_points {x : α} : x ∈ fixed_points f₁ →  h.hom x ∈ fixed_points f₂ :=
    assume (h₁ : _ = _),
    show _ = _,
    by rw [← h.conj, h₁]

    lemma fixed_points_sub : h.hom '' (fixed_points f₁) ⊆ fixed_points f₂ :=
    λ y ⟨x, ⟨h₁, h₂⟩⟩, h₂ ▸ h.mem_fixed_points h₁
  end is_semiconj

  namespace is_conj
    variables (h : is_conj f₁ f₂)

    lemma mem_fixed_points_iff (x : α) :
      x ∈ fixed_points f₁ ↔ h.hom x ∈ fixed_points f₂ :=
    iff.intro
      h.to_is_semiconj.mem_fixed_points
      (assume h₁,
        h.hom.left_inv x ▸ h.symm.to_is_semiconj.mem_fixed_points h₁)

    lemma fixed_points_equiv : fixed_points f₁ ≃ fixed_points f₂ :=
    { to_fun := λ x, ⟨h.hom x, (h.mem_fixed_points_iff x).1 x.property⟩,
      inv_fun := λ y, ⟨h.hom.inv_fun y, (h.symm.mem_fixed_points_iff y).1 y.property⟩,
      left_inv := λ x, by cases x; dsimp; congr; apply h.hom.left_inv,
      right_inv := λ x, by cases x; dsimp; congr; apply h.hom.right_inv }

    lemma fixed_points_eq : fixed_points f₂ = h.hom.to_fun '' (fixed_points f₁) :=
    set.eq_of_subset_of_subset
      (λ y h₁, ⟨h.hom.inv_fun y, ⟨(h.symm.mem_fixed_points_iff _).1 h₁, h.hom.right_inv _⟩⟩)
      h.to_is_semiconj.fixed_points_sub

  end is_conj

end function


namespace equiv
  open function

  lemma mem_fixed_points_of_conj (e : α ≃ β) (f : α → α) (x : α) :
    x ∈ fixed_points f ↔ e x ∈ fixed_points (e.conj f) :=
  (is_conj.mk' e f).mem_fixed_points_iff x

  lemma fixed_points_of_conj (e : α ≃ β) (f : α → α) :
    fixed_points (e.conj f) = e '' fixed_points f :=
  (is_conj.mk' e f).fixed_points_eq

  lemma fixed_points_self_equiv_conj (e : α ≃ β) (f : α → α) :
    fixed_points f ≃ fixed_points (e.conj f) :=
  (is_conj.mk' e f).fixed_points_equiv

  namespace perm
    def fixed_points (e : equiv.perm α) : set α := function.fixed_points e

    instance fixed_points_dec [decidable_eq α] (e : equiv.perm α) :
      decidable_pred e.fixed_points :=
    function.fixed_points_dec e

    lemma fixed_points_refl :
      (1 : equiv.perm α).fixed_points = _root_.set.univ :=
    function.fixed_points.id_eq_univ

    lemma fixed_points_mul (e₁ e₂ : equiv.perm α) :
      e₁.fixed_points ∩ e₂.fixed_points ⊆ (e₁ * e₂).fixed_points :=
    function.fixed_points.comp_sub e₁ e₂

    lemma mem_fixed_points_symm {e : equiv.perm α} {x : α} :
      x ∈ e.fixed_points → x ∈ e⁻¹.fixed_points :=
    assume h : _ = _,
    calc e.inv_fun x = e.inv_fun (e x) : by rw h
                 ... = x               : e.left_inv x

    lemma fixed_points_symm (e : equiv.perm α) :
      e.fixed_points = e⁻¹.fixed_points :=
    by ext; split; exact mem_fixed_points_symm

  end perm
end equiv
