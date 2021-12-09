/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.exact
import category_theory.over

/-!
# Pseudoelements in abelian categories

A *pseudoelement* of an object `X` in an abelian category `C` is an equivalence class of arrows
ending in `X`, where two arrows are considered equivalent if we can find two epimorphisms with a
common domain making a commutative square with the two arrows. While the construction shows that
pseudoelements are actually subobjects of `X` rather than "elements", it is possible to chase these
pseudoelements through commutative diagrams in an abelian category to prove exactness properties.
This is done using some "diagram-chasing metatheorems" proved in this file. In many cases, a proof
in the category of abelian groups can more or less directly be converted into a proof using
pseudoelements.

A classic application of pseudoelements are diagram lemmas like the four lemma or the snake lemma.

Pseudoelements are in some ways weaker than actual elements in a concrete category. The most
important limitation is that there is no extensionality principle: If `f g : X ⟶ Y`, then
`∀ x ∈ X, f x = g x` does not necessarily imply that `f = g` (however, if `f = 0` or `g = 0`,
it does). A corollary of this is that we can not define arrows in abelian categories by dictating
their action on pseudoelements. Thus, a usual style of proofs in abelian categories is this:
First, we construct some morphism using universal properties, and then we use diagram chasing
of pseudoelements to verify that is has some desirable property such as exactness.

It should be noted that the Freyd-Mitchell embedding theorem gives a vastly stronger notion of
pseudoelement (in particular one that gives extensionality). However, this theorem is quite
difficult to prove and probably out of reach for a formal proof for the time being.

## Main results

We define the type of pseudoelements of an object and, in particular, the zero pseudoelement.

We prove that every morphism maps the zero pseudoelement to the zero pseudoelement (`apply_zero`)
and that a zero morphism maps every pseudoelement to the zero pseudoelement (`zero_apply`)

Here are the metatheorems we provide:
* A morphism `f` is zero if and only if it is the zero function on pseudoelements.
* A morphism `f` is an epimorphism if and only if it is surjective on pseudoelements.
* A morphism `f` is a monomorphism if and only if it is injective on pseudoelements
  if and only if `∀ a, f a = 0 → f = 0`.
* A sequence `f, g` of morphisms is exact if and only if
  `∀ a, g (f a) = 0` and `∀ b, g b = 0 → ∃ a, f a = b`.
* If `f` is a morphism and `a, a'` are such that `f a = f a'`, then there is some
  pseudoelement `a''` such that `f a'' = 0` and for every `g` we have
  `g a' = 0 → g a = g a''`. We can think of `a''` as `a - a'`, but don't get too carried away
  by that: pseudoelements of an object do not form an abelian group.

## Notations

We introduce coercions from an object of an abelian category to the set of its pseudoelements
and from a morphism to the function it induces on pseudoelements.

These coercions must be explicitly enabled via local instances:
`local attribute [instance] object_to_sort hom_to_fun`

## Implementation notes

It appears that sometimes the coercion from morphisms to functions does not work, i.e.,
writing `g a` raises a "function expected" error. This error can be fixed by writing
`(g : X ⟶ Y) a`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

open category_theory
open category_theory.limits
open category_theory.abelian
open category_theory.preadditive

universes v u

namespace category_theory.abelian

variables {C : Type u} [category.{v} C]

local attribute [instance] over.coe_from_hom

/-- This is just composition of morphisms in `C`. Another way to express this would be
    `(over.map f).obj a`, but our definition has nicer definitional properties. -/
def app {P Q : C} (f : P ⟶ Q) (a : over P) : over Q :=
a.hom ≫ f

@[simp] lemma app_hom {P Q : C} (f : P ⟶ Q) (a : over P) : (app f a).hom = a.hom ≫ f := rfl

/-- Two arrows `f : X ⟶ P` and `g : Y ⟶ P` are called pseudo-equal if there is some object
    `R` and epimorphisms `p : R ⟶ X` and `q : R ⟶ Y` such that `p ≫ f = q ≫ g`. -/
def pseudo_equal (P : C) (f g : over P) : Prop :=
∃ (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : epi p) (_ : epi q), p ≫ f.hom = q ≫ g.hom

lemma pseudo_equal_refl {P : C} : reflexive (pseudo_equal P) :=
λ f, ⟨f.1, 𝟙 f.1, 𝟙 f.1, by apply_instance, by apply_instance, by simp⟩

lemma pseudo_equal_symm {P : C} : symmetric (pseudo_equal P) :=
λ f g ⟨R, p, q, ep, eq, comm⟩, ⟨R, q, p, eq, ep, comm.symm⟩

variables [abelian.{v} C]

section

/-- Pseudoequality is transitive: Just take the pullback. The pullback morphisms will
    be epimorphisms since in an abelian category, pullbacks of epimorphisms are epimorphisms. -/
lemma pseudo_equal_trans {P : C} : transitive (pseudo_equal P) :=
λ f g h ⟨R, p, q, ep, eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩,
begin
  refine ⟨pullback q p', pullback.fst ≫ p, pullback.snd ≫ q', _, _, _⟩,
  { resetI, exact epi_comp _ _ },
  { resetI, exact epi_comp _ _ },
  { rw [category.assoc, comm, ←category.assoc, pullback.condition,
      category.assoc, comm', category.assoc] }
end

end

/-- The arrows with codomain `P` equipped with the equivalence relation of being pseudo-equal. -/
def pseudoelement.setoid (P : C) : setoid (over P) :=
⟨_, ⟨pseudo_equal_refl, pseudo_equal_symm, pseudo_equal_trans⟩⟩

local attribute [instance] pseudoelement.setoid

/-- A `pseudoelement` of `P` is just an equivalence class of arrows ending in `P` by being
    pseudo-equal. -/
def pseudoelement (P : C) : Type (max u v) := quotient (pseudoelement.setoid P)

namespace pseudoelement

/-- A coercion from an object of an abelian category to its pseudoelements. -/
def object_to_sort : has_coe_to_sort C (Type (max u v)) :=
⟨λ P, pseudoelement P⟩

local attribute [instance] object_to_sort

/-- A coercion from an arrow with codomain `P` to its associated pseudoelement. -/
def over_to_sort {P : C} : has_coe (over P) (pseudoelement P) :=
⟨quot.mk (pseudo_equal P)⟩

local attribute [instance] over_to_sort

lemma over_coe_def {P Q : C} (a : Q ⟶ P) : (a : pseudoelement P) = ⟦a⟧ := rfl

/-- If two elements are pseudo-equal, then their composition with a morphism is, too. -/
lemma pseudo_apply_aux {P Q : C} (f : P ⟶ Q) (a b : over P) :
  a ≈ b → app f a ≈ app f b :=
λ ⟨R, p, q, ep, eq, comm⟩,
  ⟨R, p, q, ep, eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f, by rw reassoc_of comm⟩

/-- A morphism `f` induces a function `pseudo_apply f` on pseudoelements. -/
def pseudo_apply {P Q : C} (f : P ⟶ Q) : P → Q :=
quotient.map (λ (g : over P), app f g) (pseudo_apply_aux f)

/-- A coercion from morphisms to functions on pseudoelements -/
def hom_to_fun {P Q : C} : has_coe_to_fun (P ⟶ Q) (λ _, P → Q) := ⟨pseudo_apply⟩

local attribute [instance] hom_to_fun

lemma pseudo_apply_mk {P Q : C} (f : P ⟶ Q) (a : over P) : f ⟦a⟧ = ⟦a.hom ≫ f⟧ :=
rfl

/-- Applying a pseudoelement to a composition of morphisms is the same as composing
    with each morphism. Sadly, this is not a definitional equality, but at least it is
    true. -/
theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
quotient.induction_on a $ λ x, quotient.sound $
by { unfold app, rw [←category.assoc, over.coe_hom] }

/-- Composition of functions on pseudoelements is composition of morphisms. -/
theorem comp_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : g ∘ f = f ≫ g :=
funext $ λ x, (comp_apply _ _ _).symm

section zero
/-!
In this section we prove that for every `P` there is an equivalence class that contains
precisely all the zero morphisms ending in `P` and use this to define *the* zero
pseudoelement.
-/

section
local attribute [instance] has_binary_biproducts.of_has_binary_products

/-- The arrows pseudo-equal to a zero morphism are precisely the zero morphisms -/
lemma pseudo_zero_aux {P : C} (Q : C) (f : over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0 :=
⟨λ ⟨R, p, q, ep, eq, comm⟩, by exactI zero_of_epi_comp p (by simp [comm]),
  λ hf, ⟨biprod f.1 Q, biprod.fst, biprod.snd, by apply_instance, by apply_instance,
    by rw [hf, over.coe_hom, has_zero_morphisms.comp_zero, has_zero_morphisms.comp_zero]⟩⟩

end

lemma zero_eq_zero' {P Q R : C} :
  ⟦((0 : Q ⟶ P) : over P)⟧ = ⟦((0 : R ⟶ P) : over P)⟧ :=
quotient.sound $ (pseudo_zero_aux R _).2 rfl

/-- The zero pseudoelement is the class of a zero morphism -/
def pseudo_zero {P : C} : P := ⟦(0 : P ⟶ P)⟧

/--
We can not use `pseudo_zero` as a global `has_zero` instance,
as it would trigger on any type class search for `has_zero` applied to a `coe_sort`.
This would be too expensive.
-/
def has_zero {P : C} : has_zero P := ⟨pseudo_zero⟩
localized "attribute [instance] category_theory.abelian.pseudoelement.has_zero" in pseudoelement

instance {P : C} : inhabited (pseudoelement P) := ⟨0⟩

lemma pseudo_zero_def {P : C} : (0 : pseudoelement P) = ⟦(0 : P ⟶ P)⟧ := rfl
@[simp] lemma zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : over P)⟧ = (0 : pseudoelement P) :=
zero_eq_zero'

/-- The pseudoelement induced by an arrow is zero precisely when that arrow is zero -/
lemma pseudo_zero_iff {P : C} (a : over P) : (a : P) = 0 ↔ a.hom = 0 :=
by { rw ←pseudo_zero_aux P a, exact quotient.eq }

end zero

open_locale pseudoelement

/-- Morphisms map the zero pseudoelement to the zero pseudoelement -/
@[simp] theorem apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 :=
by { rw [pseudo_zero_def, pseudo_apply_mk], simp }

/-- The zero morphism maps every pseudoelement to 0. -/
@[simp] theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
quotient.induction_on a $ λ a',
  by { rw [pseudo_zero_def, pseudo_apply_mk], simp }

/-- An extensionality lemma for being the zero arrow. -/
@[ext] theorem zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → f = 0 :=
λ h, by { rw ←category.id_comp f, exact (pseudo_zero_iff ((𝟙 P ≫ f) : over Q)).1 (h (𝟙 P)) }

@[ext] theorem zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → 0 = f :=
eq.symm ∘ zero_morphism_ext f

theorem eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ a, f a = 0 :=
⟨λ h a, by simp [h], zero_morphism_ext _⟩

/-- A monomorphism is injective on pseudoelements. -/
theorem pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [mono f] : function.injective f :=
λ abar abar', quotient.induction_on₂ abar abar' $ λ a a' ha, quotient.sound $
  have ⟦(a.hom ≫ f : over Q)⟧ = ⟦a'.hom ≫ f⟧, by convert ha,
  match quotient.exact this with ⟨R, p, q, ep, eq, comm⟩ :=
    ⟨R, p, q, ep, eq, (cancel_mono f).1 $ by { simp only [category.assoc], exact comm }⟩
  end

/-- A morphism that is injective on pseudoelements only maps the zero element to zero. -/
lemma zero_of_map_zero {P Q : C} (f : P ⟶ Q) : function.injective f → ∀ a, f a = 0 → a = 0 :=
λ h a ha, by { rw ←apply_zero f at ha, exact h ha }

/-- A morphism that only maps the zero pseudoelement to zero is a monomorphism. -/
theorem mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0 → a = 0) → mono f :=
λ h, (mono_iff_cancel_zero _).2 $ λ R g hg, (pseudo_zero_iff (g : over P)).1 $ h _ $
  show f g = 0, from (pseudo_zero_iff (g ≫ f : over Q)).2 hg

section

/-- An epimorphism is surjective on pseudoelements. -/
theorem pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [epi f] : function.surjective f :=
λ qbar, quotient.induction_on qbar $ λ q, ⟨((pullback.fst : pullback f q.hom ⟶ P) : over P),
  quotient.sound $ ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd, by apply_instance,
    by apply_instance, by rw [category.id_comp, ←pullback.condition, app_hom, over.coe_hom]⟩⟩

end

/-- A morphism that is surjective on pseudoelements is an epimorphism. -/
theorem epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : function.surjective f → epi f :=
λ h, match h (𝟙 Q) with ⟨pbar, hpbar⟩ :=
  match quotient.exists_rep pbar with ⟨p, hp⟩ :=
    have ⟦(p.hom ≫ f : over Q)⟧ = ⟦𝟙 Q⟧, by { rw ←hp at hpbar, exact hpbar },
    match quotient.exact this with ⟨R, x, y, ex, ey, comm⟩ :=
      @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f y ey $
        by { dsimp at comm, rw [category.assoc, comm], apply category.comp_id }
    end
  end
end

section

/-- Two morphisms in an exact sequence are exact on pseudoelements. -/
theorem pseudo_exact_of_exact {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} [exact f g] :
  (∀ a, g (f a) = 0) ∧ (∀ b, g b = 0 → ∃ a, f a = b) :=
⟨λ a, by { rw [←comp_apply, exact.w], exact zero_apply _ _ },
  λ b', quotient.induction_on b' $ λ b hb,
    have hb' : b.hom ≫ g = 0, from (pseudo_zero_iff _).1 hb,
    begin
      -- By exactness, b factors through im f = ker g via some c
      obtain ⟨c, hc⟩ := kernel_fork.is_limit.lift' (is_limit_image f g) _ hb',

      -- We compute the pullback of the map into the image and c.
      -- The pseudoelement induced by the first pullback map will be our preimage.
      use (pullback.fst : pullback (images.factor_thru_image f) c ⟶ P),

      -- It remains to show that the image of this element under f is pseudo-equal to b.
      apply quotient.sound,

      -- pullback.snd is an epimorphism because the map onto the image is!
      refine ⟨pullback (images.factor_thru_image f) c, 𝟙 _, pullback.snd,
        by apply_instance, by apply_instance, _⟩,

      -- Now we can verify that the diagram commutes.
      calc 𝟙 (pullback (images.factor_thru_image f) c) ≫ pullback.fst ≫ f = pullback.fst ≫ f
                : category.id_comp _
        ... = pullback.fst ≫ images.factor_thru_image f ≫ kernel.ι (cokernel.π f)
                : by rw images.image.fac
        ... = (pullback.snd ≫ c) ≫ kernel.ι (cokernel.π f)
                : by rw [←category.assoc, pullback.condition]
        ... = pullback.snd ≫ b.hom
                : by { rw category.assoc, congr' }
    end⟩

end

lemma apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → f a = 0 :=
λ h, by simp [over_coe_def, pseudo_apply_mk, over.coe_hom, h]

section

/-- If two morphisms are exact on pseudoelements, they are exact. -/
theorem exact_of_pseudo_exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
  (∀ a, g (f a) = 0) ∧ (∀ b, g b = 0 → ∃ a, f a = b) → exact f g :=
λ ⟨h₁, h₂⟩, (abelian.exact_iff _ _).2 ⟨zero_morphism_ext _ $ λ a, by rw [comp_apply, h₁ a],
begin
  -- If we apply g to the pseudoelement induced by its kernel, we get 0 (of course!).
  have : g (kernel.ι g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _),

  -- By pseudo-exactness, we get a preimage.
  obtain ⟨a', ha⟩ := h₂ _ this,
  obtain ⟨a, ha'⟩ := quotient.exists_rep a',
  rw ←ha' at ha,
  obtain ⟨Z, r, q, er, eq, comm⟩ := quotient.exact ha,

  -- Consider the pullback of kernel.ι (cokernel.π f) and kernel.ι g.
  -- The commutative diagram given by the pseudo-equality f a = b induces
  -- a cone over this pullback, so we get a factorization z.
  obtain ⟨z, hz₁, hz₂⟩ := @pullback.lift' _ _ _ _ _ _ (kernel.ι (cokernel.π f)) (kernel.ι g) _
    (r ≫ a.hom ≫ images.factor_thru_image f) q
      (by { simp only [category.assoc, images.image.fac], exact comm }),

  -- Let's give a name to the second pullback morphism.
  let j : pullback (kernel.ι (cokernel.π f)) (kernel.ι g) ⟶ kernel g := pullback.snd,

  -- Since q is an epimorphism, in particular this means that j is an epimorphism.
  haveI pe : epi j := by exactI epi_of_epi_fac hz₂,

  -- But is is also a monomorphism, because kernel.ι (cokernel.π f) is: A kernel is
  -- always a monomorphism and the pullback of a monomorphism is a monomorphism.
  -- But mono + epi = iso, so j is an isomorphism.
  haveI : is_iso j := is_iso_of_mono_of_epi _,

  -- But then kernel.ι g can be expressed using all of the maps of the pullback square, and we
  -- are done.
  rw (iso.eq_inv_comp (as_iso j)).2 pullback.condition.symm,
  simp only [category.assoc, kernel.condition, has_zero_morphisms.comp_zero]
end⟩

end

/-- If two pseudoelements `x` and `y` have the same image under some morphism `f`, then we can form
    their "difference" `z`. This pseudoelement has the properties that `f z = 0` and for all
    morphisms `g`, if `g y = 0` then `g z = g x`. -/
theorem sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) : f x = f y →
  ∃ z, f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 → g z = g x :=
quotient.induction_on₂ x y $ λ a a' h,
match quotient.exact h with ⟨R, p, q, ep, eq, comm⟩ :=
  let a'' : R ⟶ P := p ≫ a.hom - q ≫ a'.hom in ⟨a'',
    ⟨show ⟦((p ≫ a.hom - q ≫ a'.hom) ≫ f : over Q)⟧ = ⟦(0 : Q ⟶ Q)⟧,
      by { dsimp at comm, simp [sub_eq_zero.2 comm] },
      λ Z g hh,
      begin
        obtain ⟨X, p', q', ep', eq', comm'⟩ := quotient.exact hh,

        have : a'.hom ≫ g = 0,
        { apply (epi_iff_cancel_zero _).1 ep' _ (a'.hom ≫ g),
          simpa using comm' },

        apply quotient.sound,

        -- Can we prevent quotient.sound from giving us this weird `coe_b` thingy?
        change app g (a'' : over P) ≈ app g a,

        exact ⟨R, 𝟙 R, p, by apply_instance, ep, by simp [sub_eq_add_neg, this]⟩
      end⟩⟩
end

variable [limits.has_pullbacks C]
/-- If `f : P ⟶ R` and `g : Q ⟶ R` are morphisms and `p : P` and `q : Q` are pseudoelements such
    that `f p = g q`, then there is some `s : pullback f g` such that `fst s = p` and `snd s = q`.

    Remark: Borceux claims that `s` is unique. I was unable to transform his proof sketch into
    a pen-and-paper proof of this fact, so naturally I was not able to formalize the proof. -/
theorem pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} : f p = g q →
  ∃ s, (pullback.fst : pullback f g ⟶ P) s = p ∧ (pullback.snd : pullback f g ⟶ Q) s = q :=
quotient.induction_on₂ p q $ λ x y h,
begin
  obtain ⟨Z, a, b, ea, eb, comm⟩ := quotient.exact h,

  obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom)
    (by { simp only [category.assoc], exact comm }),

  exact ⟨l, ⟨quotient.sound ⟨Z, 𝟙 Z, a, by apply_instance, ea, by rwa category.id_comp⟩,
    quotient.sound ⟨Z, 𝟙 Z, b, by apply_instance, eb, by rwa category.id_comp⟩⟩⟩
end

end pseudoelement
end category_theory.abelian
