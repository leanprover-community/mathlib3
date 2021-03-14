/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.adjunction

universe variables u

namespace sSet

/-- A simplicial type `X` is a Kan complex if every map `horn n i ⟶ X`
can be extended (along `horn_inclusion n i` to a map `standard_simplex n ⟶ X`. -/
def kan_complex (X : sSet) : Prop :=
Π (n i) (f : horn n i ⟶ X), ∃ g : standard_simplex.obj n ⟶ X, horn_inclusion n i ≫ g = f

end sSet

section
open Top sSet

lemma singular_is_kan_complex (X : Top) : kan_complex (singular.obj X) :=
begin
  intros n i f,
  let a : realization ⊣ singular := adjunction_realization_singular,
  let f' := (a.hom_equiv (horn n i) X).symm f,
  sorry,
end

end
