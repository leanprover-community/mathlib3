/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import category_theory.over
import category_theory.limits.shapes.finite_limits
import category_theory.yoneda
import order.complete_lattice
import data.set.lattice

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/

universes v u
namespace category_theory

/-
For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
which is closed under left-composition.
In practice it seems easier to work with this if left-composition is stated by
quantifying over objects `Y` and arrows `Y ⟶ X` rather than quantifying over `over X`.
-/
structure sieve {C : Type u} [category.{v} C] (X : C) :=
(arrows : set (over X))
(subs : ∀ {Y Z : C} {f : Y ⟶ X} (g : Z ⟶ Y), over.mk f ∈ arrows → over.mk (g ≫ f) ∈ arrows)

namespace sieve

variables {C : Type u} [category.{v} C]

variables {X Y Z : C} {S R : sieve X}

@[simp, priority 100]
lemma downward_closed (S : sieve X) {f : Y ⟶ X} (Hf : over.mk f ∈ S.arrows) (g : Z ⟶ Y) :
  over.mk (g ≫ f) ∈ S.arrows :=
S.subs g Hf

lemma arrows_ext : Π {R S : sieve X}, R.arrows = S.arrows → R = S
| ⟨Ra, _⟩ ⟨Sa, _⟩ rfl := rfl

@[ext] lemma ext {R S : sieve X}
  (h : ∀ {Y} (f : Y ⟶ X), over.mk f ∈ R.arrows ↔ over.mk f ∈ S.arrows) :
  R = S :=
begin
  apply arrows_ext,
  ext ⟨_, _, f'⟩,
  convert h f';
  apply subsingleton.elim,
end

lemma ext_iff {R S : sieve X} :
  R = S ↔ (∀ {Y} (f : Y ⟶ X), over.mk f ∈ R.arrows ↔ over.mk f ∈ S.arrows) :=
⟨λ h Y f, h ▸ iff.rfl, sieve.ext⟩

open lattice

/-- The supremum of a collection of sieves: just the union of them all. -/
protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := {f | ∃ S ∈ 𝒮, f ∈ sieve.arrows S},
  subs := λ Y Z f g, by { rintro ⟨S, hS, hf⟩, exact ⟨S, hS, S.downward_closed hf _⟩ } }

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def Inf (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := {f | ∀ S ∈ 𝒮, f ∈ sieve.arrows S},
  subs := λ Y Z f g hf S H, S.downward_closed (hf S H) g }

/-- The union of two sieves is a sieve. -/
protected def union (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∪ R.arrows,
  subs := by { rintros Y Z f g (h | h); simp [h] } }

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : sieve X) : sieve X :=
{ arrows := S.arrows ∩ R.arrows,
  subs := by { rintros Y Z f g ⟨h₁, h₂⟩; simp [h₁, h₂] } }

/--
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional
properties.
-/
instance : complete_lattice (sieve X) :=
{ le           := λ S R, ∀ Y (f : Y ⟶ X), over.mk f ∈ S.arrows → over.mk f ∈ R.arrows,
  le_refl      := λ S f q, id,
  le_trans     := λ S₁ S₂ S₃ S₁₂ S₂₃ Y f h, S₂₃ _ _ (S₁₂ _ _ h),
  le_antisymm  := λ S R p q, sieve.ext (λ Y f, ⟨p _ _, q _ _⟩),
  top          := { arrows := set.univ, subs := λ Y Z f g h, ⟨⟩ },
  bot          := { arrows := ∅, subs := λ _ _ _ _, false.elim },
  sup          := sieve.union,
  inf          := sieve.inter,
  Sup          := sieve.Sup,
  Inf          := sieve.Inf,
  le_Sup       := λ 𝒮 S hS Y f hf, ⟨S, hS, hf⟩,
  Sup_le       := λ ℰ S hS Y f, by { rintro ⟨R, hR, hf⟩, apply hS R hR _ _ hf },
  Inf_le       := λ _ _ hS _ _ h, h _ hS,
  le_Inf       := λ _ _ hS _ _ hf _ hR, hS _ hR _ _ hf,
  le_sup_left  := λ _ _ _ _, or.inl,
  le_sup_right := λ _ _ _ _, or.inr,
  sup_le       := λ _ _ _ a b _ _ hf, hf.elim (a _ _) (b _ _),
  inf_le_left  := λ _ _ _ _, and.left,
  inf_le_right := λ _ _ _ _, and.right,
  le_inf       := λ _ _ _ p q _ _ z, ⟨p _ _ z, q _ _ z⟩,
  le_top       := λ _ _ _ _, trivial,
  bot_le       := λ _ _ _, false.elim }

instance : inhabited (sieve X) := ⟨⊤⟩

@[simp]
lemma mem_Inf {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (Inf Ss).arrows ↔ ∀ S ∈ Ss, over.mk f ∈ sieve.arrows S :=
iff.rfl

@[simp]
lemma mem_Sup {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (Sup Ss).arrows ↔ ∃ S ∈ Ss, over.mk f ∈ sieve.arrows S :=
iff.rfl

@[simp]
lemma mem_inter {R S : sieve X} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (R ⊓ S).arrows ↔ over.mk f ∈ R.arrows ∧ over.mk f ∈ S.arrows :=
iff.rfl

@[simp]
lemma mem_union {R S : sieve X} {Y} (f : Y ⟶ X) :
  over.mk f ∈ (R ⊔ S).arrows ↔ over.mk f ∈ R.arrows ∨ over.mk f ∈ S.arrows :=
iff.rfl

@[simp]
lemma mem_top (f : Y ⟶ X) : over.mk f ∈ (⊤ : sieve X).arrows := trivial

/-- Take the downward-closure of a set of morphisms to `X`. -/
inductive generate_sets (𝒢 : set (over X)) : set (over X)
| basic : Π {f : over X}, f ∈ 𝒢 → generate_sets f
| subs  : Π {Y Z} {f : Y ⟶ X} (g : Z ⟶ Y), generate_sets (over.mk f) → generate_sets (over.mk (g ≫ f))

/-- Generate the smallest sieve containing the given set of arrows. -/
def generate (𝒢 : set (over X)) : sieve X :=
{ arrows := generate_sets 𝒢,
  subs   := λ _ _ _, generate_sets.subs }

open order lattice

lemma sets_iff_generate {𝒢 : set (over X)} : generate 𝒢 ≤ S ↔ 𝒢 ⊆ S.arrows :=
iff.intro
  (λ H g hg,
    begin
      have : over.mk g.hom = g,
        cases g, dsimp [over.mk],
        congr' 1, apply subsingleton.elim,
      rw ← this at *,
      exact H _ g.hom (generate_sets.basic hg),
    end )
  (λ ss Y f hf,
    begin
      induction hf,
      case basic : f hf { exact ss hf },
      case subs : Y Z f g hf₁ hf₂ { exact downward_closed S hf₂ _  }
    end)

/-- Show that there is a galois insertion (generate, .arrows). -/
def gi_generate :
  @galois_insertion (set (over X)) (sieve X) (by apply_instance) _ generate sieve.arrows :=
  { gc        := λ _ _, sets_iff_generate,
    choice    := λ 𝒢 _, generate 𝒢,
    choice_eq := λ _ _, rfl,
    le_l_u    := λ _ _ _, generate_sets.basic }

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
def pullback (S : sieve X) (h : Y ⟶ X) : sieve Y :=
{ arrows := {sl | over.mk (sl.hom ≫ h) ∈ S.arrows },
  subs := λ f hf Z g k, by { dsimp at k, simp [k] } }

@[simp] lemma mem_pullback (h : Y ⟶ X) {f : Z ⟶ Y} :
  over.mk f ∈ (pullback S h).arrows ↔ over.mk (f ≫ h) ∈ S.arrows := iff.rfl

/--
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X`
is in the sieve if `gf` factors through some `g : Z ⟶ Y` which is in `R`.
-/
def comp (R : sieve Y) (f : Y ⟶ X) : sieve X :=
{ arrows := λ gf, ∃ (g : gf.left ⟶ Y), over.mk g ∈ R.arrows ∧ g ≫ f = gf.hom,
  subs :=
  begin
    rintros Z₁ Z₂ g h ⟨j, k, z⟩,
    exact ⟨h ≫ j, by simp [k], by simp [z]⟩,
  end }

/-- Pullback is monotonic -/
lemma pullback_le_map {S R : sieve X} (Hss : S ≤ R) (f : Y ⟶ X) : pullback S f ≤ pullback R f :=
λ Z H, Hss _ _

lemma pullback_top {f : Y ⟶ X} : pullback ⊤ f = ⊤ :=
top_unique (λ _ g, id)

lemma pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g :=
by simp [sieve.ext_iff]

lemma pullback_inter {f : Y ⟶ X} (S R : sieve X) : (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f :=
by simp [sieve.ext_iff]

lemma le_pullback_comp {R : sieve Y} {f : Y ⟶ X} :
  R ≤ pullback (comp R f) f :=
begin rintros Z g b, refine ⟨_, _, rfl⟩, simpa end

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
lemma id_mem_iff_eq_top : over.mk (𝟙 X) ∈ S.arrows ↔ S = ⊤ :=
⟨λ h, top_unique
begin
  rintros Y f ⟨⟩,
  suffices : over.mk (f ≫ (𝟙 _)) ∈ S.arrows,
    simpa using this,
  apply downward_closed _ h,
end,
λ h, h.symm ▸ trivial ⟩

lemma pullback_eq_top_iff_mem (f : Y ⟶ X) : over.mk f ∈ S.arrows ↔ S.pullback f = ⊤ :=
by rw [← id_mem_iff_eq_top, mem_pullback, category.id_comp]

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : sieve X) : Cᵒᵖ ⥤ Type v :=
{ obj := λ Y, {g : Y.unop ⟶ X // over.mk g ∈ S.arrows},
  map := λ Y Z f g, ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩ }

/--
If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def le_functor {S T : sieve X} (h : S ≤ T) : S.functor ⟶ T.functor :=
{ app := λ Y f, ⟨f.1, h _ _ f.2⟩ }.

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functor_inclusion (S : sieve X) : S.functor ⟶ yoneda.obj X :=
{ app := λ Y f, f.1 }.

lemma le_functor_comm {S T : sieve X} (h : S ≤ T) :
  le_functor h ≫ functor_inclusion _ = functor_inclusion _ :=
by { ext c t, refl }

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functor_inclusion_is_mono : mono (functor_inclusion S) :=
⟨λ Z f g h, begin
  ext Y y,
  have : (f ≫ functor_inclusion S).app Y y = (g ≫ functor_inclusion S).app Y y,
    rw h,
  exact this
end⟩

end sieve
end category_theory
