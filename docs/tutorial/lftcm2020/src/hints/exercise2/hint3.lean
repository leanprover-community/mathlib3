import algebra.category.CommRing.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map :=
  begin
    -- The goal is `Π {X Y : Ring}, (X ⟶ Y) → (Ring.of (polynomial ↥X) ⟶ Ring.of (polynomial ↥Y))`
    -- so we need to:
    intros R S f,
    -- The goal is now to provide a morphism in `Ring`
    -- from `Ring.of (polynomial R)` to `Ring.of (polynomial S)`.
    -- By definition this is a `ring_hom (polynomial R) (polynomial S)`,
    -- which can also be written `polynomial R →+* polynomial S`.

    -- The hint suggested looked at `polynomial.map`.
    -- If you type `#print polynomial.map` above, you'll see that it just provides a "bare function"
    -- `polynomial R → polynomial S`, rather than an actual `ring_hom`.
    -- That's unfortunate, and will probably be fixed some as we refactor the polynomial library.

    -- In the meantime, we can hope that someone has already provided a `is_ring_hom` instance
    -- for this function, and so we can construct the `ring_hom` of `ring_hom.of`.

    -- Unfortunately just typing
    --   apply ring_hom.of
    -- fails with `failed to synthesize type class instance`.

    -- Instead we can use
    apply @ring_hom.of _ _ _ _ _ _, -- I just kept typing underscores until the error went away!
    -- to say that we want to provide all the arguments ourselves, even the typeclass arguments.

    -- Now it's "downhill": for each goal, we just tell Lean what we want to use:
    apply polynomial.map,
    apply f,
    apply_instance,

    -- With the goals completed, you should now try to "golf" this proof to a term mode proof.
    -- The next hint file walks you through doing this.
  end, }

def CommRing.polynomial : CommRing ⥤ CommRing :=
sorry

open category_theory

def commutes :
  (forget₂ CommRing Ring) ⋙ Ring.polynomial ≅ CommRing.polynomial ⋙ (forget₂ CommRing Ring) :=
sorry
