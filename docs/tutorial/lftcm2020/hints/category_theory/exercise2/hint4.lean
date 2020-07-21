import algebra.category.CommRing.basic
import data.polynomial

noncomputable theory -- the default implementation of polynomials is noncomputable

local attribute [irreducible] polynomial.eval₂

-- In the previous hint, we constructed a "tactic mode" construction of the `map` field:
def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map :=
  begin
    intros R S f,
    apply @ring_hom.of _ _ _ _ _ _,
    apply polynomial.map,
    apply f,
    apply_instance,
  end, }

-- In this file, I'll walk you through the process of condensing this into a term-mode proof.

-- Our first step is to notice that the `begin ... end` block beings with `intros ...`,
-- which we can turn into `λ ...,` outside the `begin .. end` block:

def Ring.polynomial_2 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f,
  begin
    apply @ring_hom.of _ _ _ _ _ _,
    apply polynomial.map,
    apply f,
    apply_instance,
  end, }

-- Usually I would say that since the first step of the tactic block is an `apply`,
-- we should convert that into a function application outside the block.
-- However because of the `@`, this is a little more complicated, so let's get rid of the `@` first.

-- If you hover over `@ring_hom.of`, you'll see it has six arguments:
--    Π {α β : Type (max u_1 u_2)} [rα : semiring α] [rβ : semiring β] (f : α → β) [_inst_1 : is_semiring_hom f], α →+* β
-- corresponding to the six underscores above. It's the second last two that we've solved explicitly.

def Ring.polynomial_3 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f,
  begin
    apply @ring_hom.of _ _ _ _ (polynomial.map f) _,
    -- apply_instance, -- suddenly this isn't even necessary!
  end, }

def Ring.polynomial_4 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f,
  begin
    apply ring_hom.of (polynomial.map f),
  end, }

def Ring.polynomial_5 : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, ring_hom.of (polynomial.map f), }

-- 🎉
