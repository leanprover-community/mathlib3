import algebra.direct_sum
import ring_theory.subsemiring

variables
  {A : Type*} [semiring A]
  {ι : Type*} [add_comm_monoid ι] [decidable_eq ι]

namespace direct_sum

class semiring_add_gradation (carriers : ι → subsemiring A) :=
(one_mem : (1 : A) ∈ carriers 0)
(mul_mem : ∀ {i j} (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j))

variables (carriers : ι → subsemiring A) [semiring_add_gradation carriers]


open_locale direct_sum

@[simps apply]
def mul_def (i j) : carriers i →+ carriers j →+ carriers (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, ⟨(a * b : A), semiring_add_gradation.mul_mem a b⟩,
    map_add' := λ _ _, subtype.ext (mul_add _ _ _),
    map_zero' := subtype.ext (mul_zero _), },
  map_add' := λ _ _, add_monoid_hom.ext $ λ _, subtype.ext (add_mul _ _ _),
  map_zero' := add_monoid_hom.ext $ λ _, subtype.ext (zero_mul _),}

instance : has_mul (⨁ i, carriers i) := {
  mul :=
    λ a b, direct_sum.to_add_monoid (λ i,
      direct_sum.to_add_monoid (λ j,
        sorry
      ) b
    ) a
}

#check dfinsupp.lift_add_hom

end direct_sum
