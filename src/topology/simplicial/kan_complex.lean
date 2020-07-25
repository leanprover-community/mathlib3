/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.basic

namespace sType

/-- A simplicial type `X` is a Kan complex if every map `horn n i ⟶ X`
can be extended (along `horn_inclusion n i` to a map `standard_simplex n ⟶ X`. -/
def kan_complex (X : sType) : Prop :=
Π (n i) (f : horn n i ⟶ X), ∃ g : standard_simplex.obj n ⟶ X, horn_inclusion n i ≫ g = f

end sType
