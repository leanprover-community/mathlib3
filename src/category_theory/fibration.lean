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

variables {e : E} {b : B} (f : p.obj e ⟶ b)

def hom_fiber := (under.post p).fiber (under.mk f)

instance : category (p.hom_fiber f) :=
by { unfold hom_fiber, apply_instance }

def structured_under := structured_arrow (under.mk f) (under.post p)

instance : category (p.structured_under f) :=
by { unfold structured_under, apply_instance }

end functor

namespace fibration

variables {e e₁ e₂ e₃ e₄ : E} (φ : e₁ ⟶ e₂) {f : p.obj e₁ ⟶ p.obj e₂} (hf : p.map φ = f)

def hom_lift (ψ : e₁ ⟶ e₃) (g : p.obj e₂ ⟶ p.obj e₃) := { χ : e₂ ⟶ e₃ // φ ≫ χ = ψ ∧ p.map χ = g }

def wcocartesian := ∀ {e₃} ψ (ho : p.obj e₂ = p.obj e₃)
  (hm : p.map ψ = p.map φ ≫ eq_to_hom ho), unique (hom_lift p φ ψ (eq_to_hom ho))

def cocartesian := ∀ {e₃} ψ (g : p.obj e₂ ⟶ p.obj e₃)
  (h : p.map ψ = p.map φ ≫ g), unique (hom_lift p φ ψ g)

def wcocartesian_of_cocartesian {φ : e₁ ⟶ e₂} (h : cocartesian p φ) :
  wcocartesian p φ := λ _ _ _, h _ _

/-- Isomorphisms are cocartesian. -/
noncomputable def cocartesian_of_iso (h : is_iso φ) : cocartesian p φ :=
λ e₃ ψ g h, ⟨⟨⟨inv φ ≫ ψ, by simp [h]⟩⟩, λ ⟨χ,H⟩, by simp [H]⟩

/-- Compositions of cocartesian morphisms are cocartesian. -/
def cocartesian_comp  {φ₁ : e₁ ⟶ e₂} {φ₂ : e₂ ⟶ e₃}
  (h₁ : cocartesian p φ₁) (h₂ : cocartesian p φ₂) : cocartesian p (φ₁ ≫ φ₂) :=
λ e₄ ψ g h, let ⟨⟨⟨χ₁,H₁⟩⟩,u₁⟩ := h₁ ψ (p.map φ₂ ≫ g) (by simp [h]),
                ⟨⟨⟨χ₂,H₂⟩⟩,u₂⟩ := h₂ χ₁ g H₁.2 in
⟨⟨⟨χ₂, by simp [H₁.1, H₂.1], H₂.2⟩⟩, λ ⟨χ,H⟩, subtype.eq (subtype.ext_iff.1
  (u₂ ⟨χ, subtype.ext_iff.1 (u₁ ⟨_, by simp [← H.1, H.2]⟩), H.2⟩))⟩

include hf

def mk_hom_fiber : p.hom_fiber f := ⟨under.mk φ, by simp [hf]⟩

def hom_lift_equiv_hom (ψ : p.hom_fiber f) (ho : p.obj e₂ = p.obj ψ.1.right) :
  hom_lift p φ ψ.1.hom (eq_to_hom ho) ≃ (mk_hom_fiber p φ hf ⟶ ψ) :=
{ to_fun := λ χ, ⟨under.hom_mk χ.1 χ.2.1,
    by { ext, convert χ.2.2, rw ← under.forget_map, apply eq_to_hom_map }⟩,
  inv_fun := λ χ, ⟨χ.1.right, under.w χ.1,
    by { convert congr_arg (functor.map (under.forget _)) χ.2, symmetry, apply eq_to_hom_map }⟩,
  left_inv := λ χ, by simp,
  right_inv := λ χ, by { ext, simp } }

def wcocartesian_equiv_initial :
  wcocartesian p φ ≃ limits.is_initial (mk_hom_fiber p φ hf) :=
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


def mk_structured_under : p.structured_under f :=
⟨punit.star, under.mk φ, under.hom_mk (𝟙 _)⟩
 --eq_to_hom (by { dsimp, congr, exact hf.symm })⟩

def hom_lift_equiv_hom' (ψ : p.structured_under f) :
  hom_lift p φ ψ.right.hom ψ.hom.right ≃ (mk_structured_under p φ hf ⟶ ψ) :=
{ to_fun := λ χ, structured_arrow.hom_mk (under.hom_mk χ.1 χ.2.1)
    (by { ext, dsimp, convert χ.2.2, apply category.id_comp }),
  inv_fun := λ χ, ⟨χ.right.right, under.w χ.right,
    by { convert congr_arg comma_morphism.right χ.w.symm using 1;
      { dsimp, erw category.id_comp } }⟩,
  left_inv := λ χ, by simp,
  right_inv := λ χ, by { ext, simp } }

def cocartesian_equiv_initial :
  cocartesian p φ ≃ limits.is_initial (mk_structured_under p φ hf) :=
{ to_fun :=

}

omit hf

lemma subsingleton_hom_of_cocartesian (h : cocartesian p φ) (ψ : under e₁) :
  subsingleton (under.mk φ ⟶ ψ) :=
⟨λ χ₁ χ₂, by { ext, }⟩


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
  (h₁ : wcocartesian p φ₁) (h₂ : wcocartesian p φ₂) : e₁ ≅ e₂ :=
{ hom := (h₁ φ₂ ho (by simp [hm])).some,
  inv := (h₂ φ₁ ho.symm hm).some,
  hom_inv_id' := ,
  inv_hom_id' := }

-- prefibered only needs map_id, not map_comp!?
-- no need of pseudofunctor, lax functor enough to get wcartesian
-- need slightly different definition of the factorization through, but equal to the general case when inv of map_comp exists

-- isomorphic to (w)cartesian in under category -> itself (w)cartesian
-- have one wcartesian lift, then the other lift is wcartesian iff isomorphic to it through morphism that projects to eq_to_hom
-- isomorphism clearly cocartesian, hence wcocartesian

-- transfer fibration across equivalence of total category ..?
-- composition of fibration is fibration, but equivalence may not be fibration ..




-- one cocartesian lift -> another lift is cocartesian iff it's isomorphic in under category
-- cocartesian <-> initial in under category / structured arrow of under cat?
-- adjunction between under in C and under in D, given by chosen cocartesians ..

end fibration

-- opfibration_cleavage

open fibration

def pre_opfibration :=
  ∀ {e : E} {b : B} (f : p.obj e ⟶ b),
  { φ : p.hom_fiber f // nonempty (wcocartesian p φ.1.hom) }
  --∃ (e' : E) (φ : e ⟶ e') (h : b = p.obj e'),
  --is_wcocartesian p φ ∧ p.map φ = f ≫ eq_to_hom h

def opfibration :=
  ∀ {e : E} {b : B} (f : p.obj e ⟶ b),
  { φ : p.hom_fiber f // nonempty (cocartesian p φ.1.hom) }

variables {e : E} {b : B} (f : p.obj e ⟶ b) (h : opfibration p) {p}

lemma proj_obj_eq : p.obj (h f).1.1.right = b := congr_arg comma.right (h f).1.2

lemma under.congr_hom {f g : under e} (h : f = g) : f.hom = g.hom ≫ eq_to_hom (by rw h) :=
by { subst h, simp }

@[simp]
lemma proj_map_eq : p.map (h f).1.1.hom = f ≫ eq_to_hom (eq.symm (by apply proj_obj_eq)) :=
under.congr_hom (h f).1.2

noncomputable def lift_under {e : E} {f₁ f₂ : under (p.obj e)} (g : f₁ ⟶ f₂) :=
(h f₁.hom).2.some (h f₂.hom).1.1.hom
  (eq_to_hom (by apply proj_obj_eq) ≫ g.right ≫ eq_to_hom (eq.symm (by apply proj_obj_eq)))
  (by simp [under.w g])

noncomputable def cleavage (e : E) : under (p.obj e) ⥤ under e :=
{ obj := λ f, (h f.hom).1.1,
  map := λ f₁ f₂ g, let χ := (lift_under @h g).default in under.hom_mk χ.1 χ.2.1,
  map_id' := λ f, by { rw ← (lift_under @h (𝟙 f)).2 ⟨𝟙 _, by simp⟩, refl },
  map_comp' := λ f₁ f₂ f₃ g₁ g₂, by { ext,
    have h₁ := (lift_under @h g₁).default.2, have h₂ := (lift_under @h g₂).default.2,
    rw ← ((lift_under @h (g₁ ≫ g₂)).2 ⟨_,_,_⟩), refl,
    erw [← category.assoc, h₁.1, h₂.1],
    { erw [p.map_comp, h₁.2, h₂.2], simp } } }

noncomputable def lift_proj_self {e : E} (f : under e) :=
(h (p.map f.hom)).2.some f.hom (eq_to_hom (by apply proj_obj_eq)) (by simp)

def cleavage_forget_counit (e : E) : under.post p ⋙ cleavage @h e ⟶ 𝟭 (under e) :=
{ app := λ f, let χ := (lift_proj_self @h f).default in under.hom_mk χ.1 χ.2.1,
  naturality' := λ f₁ f₂ g, by { ext, dsimp, have := (lift_proj_self @h f₁).default.2, } }

noncomputable def cleavage_forget_adjunction (e : E) : cleavage @h e ⊣ under.post p :=
adjunction.mk_of_unit_counit
{ unit := eq_to_hom (functor.ext (by {rintro ⟨⟨_⟩,_,f⟩, erw (h f).1.2, dsimp, congr})
    (by {intros, ext, dsimp, erw (lift_under @h f).default.2.2, simp})),
  counit := ,

}


lemma cocartesian_of_w_of_fibration (hf : opfibration p) {φ : e₁ ⟶ e₂}
  (hw : wcocartesian p φ) : cocartesian p φ :=
begin

end

def wcocartesian_comp :=
  ∀ {e₁ e₂ e₃} {φ₁ : e₁ ⟶ e₂} {φ₂ : e₂ ⟶ e₃}
  (h₁ : wcocartesian p φ₁) (h₂ : wcocartesian p φ₂), wcocartesian p (φ₁ ≫ φ₂)



end category_theory
