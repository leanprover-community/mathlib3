import category_theory.examples.topological_spaces
import category_theory.opposites
import category_theory.yoneda
import category_theory.limits

open category_theory

universes u u₁ u₂ v v₁ v₂ w w₁ w₂

-- namespace category_theory.limits
-- variables {C : Type u₁} [𝒞 : category.{u₁ u₂} C]
-- include 𝒞

-- variables [has_coequalizers.{u₁ u₂} C] {Y Z : C} (f g : Y ⟶ Z)

-- def coequalizer.cofork := has_coequalizers.coequalizer.{u₁ u₂} f g
-- def coequalizer := (coequalizer.cofork f g).X
-- def coequalizer.π : Z ⟶ (coequalizer f g) := (coequalizer.cofork f g).π
-- @[search] def coequalizer.w : f ≫ (coequalizer.π f g) = g ≫ (coequalizer.π f g) := (coequalizer.cofork f g).w
-- def coequalizer.universal_property : is_coequalizer (coequalizer.cofork f g) :=
-- has_coequalizers.is_coequalizer.{u₁ u₂} C f g

-- def coequalizer.desc (P : C) (h : Z ⟶ P) (w : f ≫ h = g ≫ h) : coequalizer f g ⟶ P :=
-- (coequalizer.universal_property f g).desc { X := P, π := h, w := w }

-- @[extensionality] lemma coequalizer.hom_ext {Y Z : C} {f g : Y ⟶ Z} {X : C}
-- (h k : coequalizer f g ⟶ X) (w : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) : h = k :=
-- begin
--   let s : cofork f g := ⟨ ⟨ X ⟩, coequalizer.π f g ≫ h ⟩,
--   have q := (coequalizer.universal_property f g).uniq s h,
--   have p := (coequalizer.universal_property f g).uniq s k,
--   rw [q, ←p],
--   solve_by_elim, refl
-- end

-- end category_theory.limits

section presheaf
open category_theory.limits
variables (X : Type u₁) [𝒳 : category.{u₁ v₁} X] (C : Type u₂) [𝒞 : category.{u₂ v₂} C]
include 𝒳 𝒞

def presheaf := Xᵒᵖ ⥤ C

variables {X} {C}

instance : category (presheaf X C) := by unfold presheaf; apply_instance

omit 𝒞
instance presheaf.has_coequalizers : @has_coequalizers (presheaf X (Type v₁)) presheaf.category_theory.category := sorry
instance presheaf.has_coproducts : @has_coproducts (presheaf X (Type v₁)) presheaf.category_theory.category := sorry
instance presheaf.has_pullbacks : @has_pullbacks (presheaf X (Type v₁)) presheaf.category_theory.category := sorry

end presheaf

-- todo should this be done as a subfunctor?
structure covering_family {X : Type u₁} [category.{u₁ v₁} X] (U : X) :=
(index : Type v₁)
(obj : index → X)
(map : Π (i : index), obj i ⟶ U)

namespace covering_family
open category_theory.limits
variables {X : Type u₁} [𝒳 : category.{u₁ v₁} X]
include 𝒳

variables {U : X}

def sieve (f : covering_family U) : presheaf X (Type v₁) :=
let CP := (((yoneda X) : X → presheaf X (Type v₁)) ∘ f.obj) in
coequalizer
  (sigma.desc (λ p : (f.index × f.index), (sigma.ι CP p.1) ∘ (pullback.π₁ ((yoneda X).map (f.map p.1)) ((yoneda X).map (f.map p.2)))))
  (sigma.desc (λ p : (f.index × f.index), (sigma.ι CP p.2) ∘ (pullback.π₂ ((yoneda X).map (f.map p.1)) ((yoneda X).map (f.map p.2)))))

def sheaf_condition (f : (covering_family U)) {C : Type u₂} [category.{u₂ v₂} C] (F : presheaf X C) : Prop := sorry

end covering_family

structure coverage {X : Type u₁} [category.{u₁ u₂} X] :=
(covers   : Π (U : X), set (covering_family U))
(property : ∀ {U V : X} (g : V ⟶ U) (f : (covering_family U)),
            ∃ h : (covering_family V), ∀ j : h.index, ∃ {i : f.index} {k : h.obj j ⟶ f.obj i},
            h.map j ≫ g = k ≫ f.map i)

class site (X : Type u₁) extends category.{u₁ u₂} X :=
(coverage : @coverage X (by assumption))

namespace site
variables {X : Type u₁} [𝒳 : site.{u₁ v₁} X]

definition covers := coverage.covers 𝒳.coverage

end site

section sheaf
variables (X : Type u₁) [𝒳 : site.{u₁ v₁} X] (C : Type u₂) [𝒞 : category.{u₂ v₂} C]
include 𝒳 𝒞

structure sheaf :=
(presheaf : presheaf X C)
(sheaf_condition : ∀ {U : X} (f ∈ site.covers U), f.sheaf_condition presheaf)

end sheaf


namespace topological_space

variables {X : Type u} [topological_space X]

instance : site (opens X) :=
{ coverage :=
  { covers := λ U, λ Us, begin sorry -- the union of the Ui should be U
    end,
    property := sorry } }

end topological_space