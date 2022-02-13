
import data.polynomial.default
import data.fintype.basic


noncomputable theory

open finsupp finset

namespace polynomial
open_locale polynomial
universes u
variables {F : Type u} {a b : F}

section field
variables [field F] {p q r : F[X]}

lemma schwartz_zippel (S : finset F) (hs : p.degree ≤ S.card ) (hp : ∀ s ∈ S, p.eval s = 0) :
  p.eval a = 0 :=
begin
  sorry,
end


end field

end polynomial
