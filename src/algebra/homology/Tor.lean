import algebra.homology.homology
import algebra.category.Module.abelian
import linear_algebra.prod
/-

# The `Tor` groups `Torₙᴿ(A,B)`

Let `A` and `B` be `R`-modules (surely we need `A` and `B` abelian groups here, not just monoids)
We define abelian groups `Tor R n A B` as a magical type. If `R` is furthermore commutative,
we give `Tor R n A B` the structure of an `R` module.

## TODO

* `Tor R n A B : Type` and ab_group and  R-module structure

`comm : Tor R n A B ≃+[R] Tor R n B A` -- some symmetry of the bifunctor `Tor R n`

`theorem comm_thing : Tor.comm R n A B (t R n A B) = t R n B A := sorry`

R-mod x R-mod --(some functor t) -> ab gp

[swap ↓]

R-mod x R-mod --()

More defs :
-/

-- that's the functor (fix typeclasses later)
constant Tor (R : Type) [comm_ring R] (n : ℕ) (A B : Type) [add_comm_group A] [add_comm_group B]
[module R A] [module R B] : Type

namespace Tor

variables (R : Type) [comm_ring R] (n : ℕ) (A B : Type) [add_comm_group A] [add_comm_group B]
[module R A] [module R B]

instance : add_comm_group (Tor R n A B) := sorry

instance : module R (Tor R n A B) := sorry

def comm : Tor R n A B ≃ₗ[R] Tor R n B A := sorry

--apparently we should just coerce comm to get : Tor R n A B →ₗ[R] Tor R n B A := sorry

variable (t : Π (R n A B) [comm_ring R] [add_comm_group A] [add_comm_group B]
[module R A] [module R B], Tor R n A B)

#check comm

-- what is a symmetric bifunctor? -- did we prove this was one?
theorem comm_thing : Tor.comm R n A B (t R n A B) = t R n B A := sorry

end Tor

section theorems

-- fix variables latr, this is just stubbing it out
variables {R : Type} [ring R] {A B C : Type} [add_comm_group A] [add_comm_group B]
[add_comm_group C] [module R A] [module R B] [module R C] (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C)

#check linear_map.prod

-- #check ψ.comp φ

structure is_short_exact (φ : A →ₗ[R] B) (ψ : B →ₗ[R] C) : Prop :=
(injective : function.injective φ)
(surjective : function.surjective ψ)
(is_exact : φ.range = ψ.ker)

lemma is_short_exact.to_set (h : is_short_exact φ ψ) (b : B) : (∃ a, φ a = b) ↔ ψ b = 0 :=
begin
  sorry
end

/-

## Theorem: Long exact sequence in first argument.

-/

-- Apparently Amelia would rather have projective resolutions.


-- how to say long exact sequence? use the lean-liquid way or use the mathlib way,
-- e.g. `differential_object` def.
theorem goal_one (h : is_short_exact φ ψ) : sorry := sorry

end theorems
