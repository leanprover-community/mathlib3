/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Ring.limits
import algebra.category.Module.change_of_rings

/-!
# The category of ring-module pair

`RingModPair` is the category of pairs of the shape `(R, M)` where `R` is
a ring and `M` is an `R`-module. A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map).
-/

namespace category_theory

open category_theory.Module category_theory.limits

section

universes u v

/--
A ring-module pair is a pair `(R, M)` such that `R : Ring` and `M` is an `R`-module.
-/
@[nolint check_univs]
structure RingModPair : Type (max (v+1) (u+1)) :=
(ring : Ring.{u})
(mod : Module.{v u} ring)

/--
A commutative-ring-module pair is a pair `(R, M)` such that `R : CommRing` and `M` is an `R`-module.
-/
@[nolint check_univs]
structure CommRingModPair : Type (max (v+1) (u+1)) :=
(ring : CommRing.{u})
(mod : Module.{v u} ring)

instance : inhabited RingModPair :=
{ default := ⟨⟨punit⟩, ⟨punit⟩⟩ }

instance : inhabited CommRingModPair := ⟨⟨⟨punit⟩, ⟨punit⟩⟩⟩

namespace RingModPair

/--
A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map)
-/
def hom (P Q : RingModPair) : Type (max v u) :=
Σ (ring_hom : P.ring ⟶ Q.ring),
  P.mod ⟶ (category_theory.Module.restrict_scalars ring_hom).obj Q.mod

instance : category RingModPair :=
{ hom := hom,
  id := λ P, sigma.mk (𝟙 _)
  { to_fun := λ x, x,
    map_add' := λ _ _, rfl,
    map_smul' := λ _ _, rfl },
  comp := λ X Y Z f g, sigma.mk (f.1 ≫ g.1)
  { to_fun := λ x, g.2 $ f.2 x,
    map_add' := λ x y, by simp only [map_add],
    map_smul' := λ r x,
      by simp only [map_smul, ring_hom.id_apply, restrict_scalars.smul_def, comp_apply] },
  id_comp' := λ X Y ⟨f, g⟩, sigma.ext (category.id_comp _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  comp_id' := λ X Y ⟨f, g⟩, sigma.ext (category.comp_id _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  assoc' := λ A B C D ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, sigma.ext (category.assoc _ _ _) $ heq_of_eq $
    linear_map.ext $ λ x, rfl }

instance (P : RingModPair) : inhabited (hom P P) :=
{ default := 𝟙 P }

/--
The underlying ring homomorphism of a morphism between two ring-module pairs.
-/
def hom.ring_hom {P Q : RingModPair} (f : P ⟶ Q) : P.ring ⟶ Q.ring := f.1
/--
The underlying module homomorphism of a morphism between two ring-module pairs.
-/
def hom.mod_hom {P Q : RingModPair} (f : P ⟶ Q) :
  P.mod ⟶ (category_theory.Module.restrict_scalars f.ring_hom).obj Q.mod := f.2

@[ext] lemma hom.ext {P Q : RingModPair} (f g : P ⟶ Q) :
  f = g ↔ (∀ (x : P.ring), f.1 x = g.1 x) ∧ ∀ (x : P.mod), f.2 x = g.2 x :=
⟨λ h, h ▸ ⟨λ x, rfl, λ x, rfl⟩, λ h, begin
  rcases f with ⟨f1, f2⟩,
  rcases g with ⟨g1, g2⟩,
  have eq1 : f1 = g1 := fun_like.ext _ _ h.1,
  subst eq1,
  have eq2 : f2 = g2 := fun_like.ext _ _ h.2,
  subst eq2,
end⟩

@[simp] lemma hom.comp_fst {A B C : RingModPair} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] lemma hom.comp_snd_apply {A B C : RingModPair} (f : A ⟶ B) (g : B ⟶ C) (x) :
  (f ≫ g).2 x = g.2 (f.2 x) := rfl

/--
The canonical functor sending a ring-module pair to its underlying ring
-/
def forget_to_Ring : RingModPair ⥤ Ring :=
{ obj := λ P, P.ring,
  map := λ _ _ f, f.ring_hom,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

/--
The canonical functor sending a ring-module pair to its underlying abelian group
-/
def forget_to_Ab : RingModPair ⥤ AddCommGroup :=
{ obj := λ P, ⟨P.mod⟩,
  map := λ _ _ f, f.mod_hom.to_add_monoid_hom,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

end RingModPair

namespace CommRingModPair

/--
A morphism between `M1 = (R, M)`
and `M2 = (S, N)` is a pair of morphism `(f, g)` where `f : R ⟶ S` is a ring
homomorphism and `g : M ⟶ f* N` is a module homomorphism (linear map)
-/
def hom (P Q : CommRingModPair) : Type (max v u) :=
Σ (ring_hom : P.ring ⟶ Q.ring),
  P.mod ⟶ (category_theory.Module.restrict_scalars ring_hom).obj Q.mod

instance : category CommRingModPair :=
{ hom := hom,
  id := λ P, sigma.mk (𝟙 _)
  { to_fun := λ x, x,
    map_add' := λ _ _, rfl,
    map_smul' := λ _ _, rfl },
  comp := λ X Y Z f g, sigma.mk (f.1 ≫ g.1)
  { to_fun := λ x, g.2 $ f.2 x,
    map_add' := λ x y, by simp only [map_add],
    map_smul' := λ r x,
      by simp only [map_smul, ring_hom.id_apply, restrict_scalars.smul_def, comp_apply] },
  id_comp' := λ X Y ⟨f, g⟩, sigma.ext (category.id_comp _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  comp_id' := λ X Y ⟨f, g⟩, sigma.ext (category.comp_id _) $ heq_of_eq $ linear_map.ext $ λ x, rfl,
  assoc' := λ A B C D ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩, sigma.ext (category.assoc _ _ _) $ heq_of_eq $
    linear_map.ext $ λ x, rfl }

instance (P : CommRingModPair) : inhabited (hom P P) :=
{ default := 𝟙 P }

/--
The underlying ring homomorphism of a morphism between two ring-module pairs.
-/
def hom.ring_hom {P Q : CommRingModPair} (f : P ⟶ Q) : P.ring ⟶ Q.ring := f.1
/--
The underlying module homomorphism of a morphism between two ring-module pairs.
-/
def hom.mod_hom {P Q : CommRingModPair} (f : P ⟶ Q) :
  P.mod ⟶ (category_theory.Module.restrict_scalars f.ring_hom).obj Q.mod := f.2

@[ext] lemma hom.ext {P Q : CommRingModPair} (f g : P ⟶ Q) :
  f = g ↔ (∀ (x : P.ring), f.1 x = g.1 x) ∧ ∀ (x : P.mod), f.2 x = g.2 x :=
⟨λ h, h ▸ ⟨λ x, rfl, λ x, rfl⟩, λ h, begin
  rcases f with ⟨f1, f2⟩,
  rcases g with ⟨g1, g2⟩,
  have eq1 : f1 = g1 := fun_like.ext _ _ h.1,
  subst eq1,
  have eq2 : f2 = g2 := fun_like.ext _ _ h.2,
  subst eq2,
end⟩

@[simp] lemma hom.comp_fst {A B C : CommRingModPair} (f : A ⟶ B) (g : B ⟶ C) :
  (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] lemma hom.comp_snd_apply {A B C : CommRingModPair} (f : A ⟶ B) (g : B ⟶ C) (x) :
  (f ≫ g).2 x = g.2 (f.2 x) := rfl

def forget_to_RingModPair : CommRingModPair ⥤ RingModPair :=
{ obj := λ P, ⟨⟨P.ring⟩, P.mod⟩,
  map := λ _ _ f, f,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

lemma forget_to_RingModPair.faithful : faithful forget_to_RingModPair :=
{ map_injective' := λ _ _ _ _, id }

def forget_to_RingModPair.full : full forget_to_RingModPair :=
{ preimage := λ X Y f, f,
  witness' := λ X Y f, rfl }

def forget_to_CommRing : CommRingModPair ⥤ CommRing :=
{ obj := λ P, P.ring,
  map := λ X Y f, f.ring_hom,
  map_id' := λ _, rfl,
  map_comp' := λ X Y Z _ _, rfl }

def forget_to_Ab : CommRingModPair ⥤ AddCommGroup :=
{ obj := λ P, ⟨P.mod⟩,
  map := λ X Y f, f.mod_hom.to_add_monoid_hom,
  map_id' := λ X, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

end CommRingModPair

end

end category_theory
