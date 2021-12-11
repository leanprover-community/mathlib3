/-
Copyright (c) 2021 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/

import category_theory.functor
import category_theory.eq_to_hom
import category_theory.over

/-!
# Grothendieck fibrations of categories

Define cartesian and weakly cartesian morphisms and Grothendieck fibrations.

Reference: https://ncatlab.org/nlab/show/Grothendieck+fibration

-/

namespace category_theory

universes v v₁ v₂ v₃ u u₁ u₂ u₃

variables {E : Type u₁} [category.{v₁} E] {B : Type u₂} [category.{v₂} B] (p : E ⥤ B)

namespace functor

def fiber (b : B) := { e : E // p.obj e = b }

instance (b : B) : category (p.fiber b) :=
{ hom := λ e₁ e₂, { ψ : e₁.1 ⟶ e₂.1 // p.map ψ = eq_to_hom (by rw [e₁.2, e₂.2]) },
  id := λ e, ⟨𝟙 _, by simp⟩,
  comp := λ _ _ _ ψ₁ ψ₂, ⟨ψ₁.1 ≫ ψ₂.1, by { rw [map_comp, ψ₁.2, ψ₂.2], simp }⟩ }

def fiber_inclusion (b : B) : p.fiber b ⥤ E :=
{ obj := λ e, e.1,
  map := λ _ _ ψ, ψ.1 }

variables {e : E} {b : B} (ψ : p.obj e ⟶ b)

def hom_fiber := (under.post p).fiber (under.mk ψ)
  --(costructured_arrow.proj p b).fiber g
  --under (by { apply structured_arrow.mk, } : structured_arrow b₁ (p.fiber_obj_include b₂ ⋙ p))

instance : category (p.hom_fiber ψ) := by { unfold hom_fiber, apply_instance }

end functor

variables {e e₁ e₂ e₃ e₄ : E} (φ : e₁ ⟶ e₂) {f : p.obj e₁ ⟶ p.obj e₂} (hf : p.map φ = f)

def hom_lift (ψ : e₁ ⟶ e₃) (g : p.obj e₂ ⟶ p.obj e₃) := { χ : e₂ ⟶ e₃ // φ ≫ χ = ψ ∧ p.map χ = g }

include hf
def hom_lift_equiv_hom (ψ : p.hom_fiber f) (ho : p.obj e₂ = p.obj ψ.1.right) :
  hom_lift p φ ψ.1.hom (eq_to_hom ho) ≃ (by {exact ⟨under.mk φ, by simp [hf]⟩} ⟶ ψ) :=
{ to_fun := λ χ, ⟨under.hom_mk χ.1 χ.2.1,
    by { ext, convert χ.2.2, rw ← under.forget_map, apply eq_to_hom_map }⟩,
  inv_fun := λ χ, ⟨χ.1.right, (under.w χ.1),
    by { convert congr_arg (functor.map (under.forget _)) χ.2, symmetry, apply eq_to_hom_map }⟩,
  left_inv := λ χ, by simp,
  right_inv := λ χ, by { ext, simp } }
omit hf

def wcocartesian := ∀ {e₃} ψ (ho : p.obj e₂ = p.obj e₃)
  (hm : p.map ψ = p.map φ ≫ eq_to_hom ho), unique (hom_lift p φ ψ (eq_to_hom ho))

include hf
def wcocartesian_equiv_initial :
  wcocartesian p φ ≃ limits.is_initial (by exact ⟨under.mk φ, by simp [hf]⟩ : p.hom_fiber f) :=
{ to_fun := λ hw, by { fapply @limits.is_initial.of_unique _ _ _ _,
    intro ψ, have := (congr_arg comma.right ψ.2).symm,
    exact equiv.unique_congr (hom_lift_equiv_hom p φ hf ψ this)
      (hw ψ.1.hom this (by { rw hf, exact
        (eq_to_hom.family_congr comma.hom ψ.2).trans (category.id_comp _) })) },
  inv_fun := λ hl e₃ ψ ho hm, by {
    refine (equiv.unique_congr (hom_lift_equiv_hom p φ hf ⟨under.mk ψ, _⟩ _)).symm _,
    { dsimp, rw [hm, hf], congr' 1, rw ho,
      { rw ← congr_arg_mpr_hom_right, { dsimp, simp }, rw ho } },
    exact ⟨⟨hl.desc (limits.as_empty_cocone _)⟩,
      λ a, by { apply hl.uniq (limits.as_empty_cocone _), rintro ⟨⟩ }⟩ },
  left_inv := λ _, by ext,
  right_inv := λ _, by simp }
omit hf
  --(limits.is_initial (@structured_arrow.mk (p.fiber (p.obj e₂)) _ _ _ _ ⟨e₂,rfl⟩ (p.fiber_include _) φ)) :=
#check @wcocartesian
#check wcocartesian p φ
variable (h : wcocartesian p φ)
#check @h
example (h : wcocartesian p φ) := wcocartesian_equiv_initial p φ rfl @h

def wcocartesian_lifts_eq (φ' : e₁ ⟶ e₂) (hp : p.map φ = p.map φ')
  (h : wcocartesian p φ) (h' : wcocartesian p φ') : φ = φ' :=
by { let := wcocartesian_equiv_initial p φ hp @h,
     let := wcocartesian_equiv_initial p φ' rfl @h', }


def wcocartesian_iso (h : wcocartesian p φ) (φ' : e₁ ⟶ e₄) :

--def wcocartesian_lift_equiv : p.fiber (p.obj e₂) ≅ Σ ()
-- e₄ must project to p.obj e₂ ...
def wcocartesian_comp_iso (α : e₂ ≅ e₄) (h : wcocartesian p φ) : wcocartesian p (φ ≫ α.hom) :=
λ e₃ ψ ho hm, ⟨⟨⟨ by { }, by { }⟩⟩, by {}⟩


/-lemma wcocartesian_lift_self {φ : e₁ ⟶ e₂} (h : is_wcocartesian p φ) :
  (h φ rfl (by simp)).some = 𝟙 _ :=
((h φ rfl (by simp)).some_spec.2 (𝟙 _) (by simp)).symm-/

def wcocartesian_lift_wcocartesian {φ₁ : e ⟶ e₁} {φ₂ : e ⟶ e₂}
  (ho : p.obj e₁ = p.obj e₂) (hm : p.map φ₁ = p.map φ₂ ≫ eq_to_hom (by rw ho))
  (h₁ : is_wcocartesian p φ₁) (h₂ : is_wcocartesian p φ₂) : e₁ ≅ e₂ :=
{ hom := (h₁ φ₂ ho (by simp [hm])).some,
  inv := (h₂ φ₁ ho.symm hm).some,
  hom_inv_id' := ,
  inv_hom_id' := }

-- prefibered only needs map_id, not map_comp!
-- no need of pseudofunctor, lax functor enough to get wcartesian
-- need slightly different definition of the factorization through, but equal to the general case when inv of map_comp exists

-- isomorphic to (w)cartesian in under category -> itself (w)cartesian
-- have one wcartesian lift, then the other lift is wcartesian iff isomorphic to it through morphism that projects to eq_to_hom
-- isomorphism clearly cocartesian, hence wcocartesian

-- transfer fibration across equivalence of total category ..?
-- composition of fibration is fibration, but equivalence may not be fibration ..


def cocartesian := ∀ {e₃} ψ (g : p.obj e₂ ⟶ p.obj e₃)
  (h : p.map ψ = p.map φ ≫ g), unique (hom_lift p φ ψ g)

def wcocartesian_of_cocartesian {φ : e₁ ⟶ e₂} (h : cocartesian p φ) :
  wcocartesian p φ := λ _ _ _, h _ _

/-- Isomorphisms are cocartesian. -/
noncomputable def cocartesian_iso (h : is_iso φ) : cocartesian p φ :=
λ e₃ ψ g h, ⟨⟨⟨inv φ ≫ ψ, by simp [h]⟩⟩, λ ⟨χ,H⟩, by simp [H]⟩

/-- Compositions of cocartesian morphisms are cocartesian. -/
def cocartesian_comp  {φ₁ : e₁ ⟶ e₂} {φ₂ : e₂ ⟶ e₃}
  (h₁ : cocartesian p φ₁) (h₂ : cocartesian p φ₂) : cocartesian p (φ₁ ≫ φ₂) :=
λ e₄ ψ g h, let ⟨⟨⟨χ₁,H₁⟩⟩,u₁⟩ := h₁ ψ (p.map φ₂ ≫ g) (by simp [h]),
                ⟨⟨⟨χ₂,H₂⟩⟩,u₂⟩ := h₂ χ₁ g H₁.2 in
⟨⟨⟨χ₂, by simp [H₁.1, H₂.1], H₂.2⟩⟩, λ ⟨χ,H⟩, subtype.eq (subtype.ext_iff.1
  (u₂ ⟨χ, subtype.ext_iff.1 (u₁ ⟨_, by simp [← H.1, H.2]⟩), H.2⟩))⟩

--u₂ ⟨χ.1, (u₁ _ (by simp [h])).symm⟩, ⟩
/-let ⟨⟨χ₁⟩,H₁⟩ := h₁ ψ (p.map φ₂ ≫ g) (by simp [h]),
                ⟨χ₂,H₂⟩ := h₂ χ₁ g H₁.1.2 in
⟨χ₂, ⟨by simp [H₁.1.1, H₂.1.1], H₂.1.2⟩,
  λ χ h, H₂.2 χ ⟨(H₁.2 _ (by simp [h])).symm, h.2⟩⟩
-/

-- one cocartesian lift -> another lift is cocartesian iff it's isomorphic in under category
-- cocartesian <-> initial in under category / structured arrow of under cat?
-- adjunction between under in C and under in D, given by chosen cocartesians ..

-- opfibration_cleavage

def is_prefibered : Prop :=
  ∀ {e : E} {b : B} (f : p.obj e ⟶ b),
  ∃ (e' : E) (φ : e ⟶ e') (h : b = p.obj e'),
  is_wcocartesian p φ ∧ p.map φ = f ≫ eq_to_hom h

def is_fibration : Prop :=
  ∀ {e : E} {b : B} (f : p.obj e ⟶ b),
  ∃ (e' : E) (φ : e ⟶ e') (h : b = p.obj e'),
  is_cocartesian p φ ∧ p.map φ = f ≫ eq_to_hom h

lemma cocartesian_of_w_of_fibration (hf : is_fibration p) {φ : e₁ ⟶ e₂}
  (hw : is_wcocartesian p φ) : is_cocartesian p φ :=
begin

end

def wcocartesian_comp :=
  ∀ {e₁ e₂ e₃} {φ₁ : e₁ ⟶ e₂} {φ₂ : e₂ ⟶ e₃}
  (h₁ : wcocartesian p φ₁) (h₂ : wcocartesian p φ₂), wcocartesian p (φ₁ ≫ φ₂)



end category_theory
