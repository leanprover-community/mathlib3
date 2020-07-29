import algebra.category.CommRing
import category_theory.yoneda
import data.polynomial.algebra_map

noncomputable theory

open category_theory
open opposite
open polynomial

/-!
It would be nice to use `polynomial.aeval`, which produces an algebra homomorphism,
and then convert that use `.to_ring_hom`.

However we get a mysterious error message:
-/
/- def CommRing_forget_representable : Σ (R : CommRing), (forget CommRing) ≅ coyoneda.obj (op R) :=
⟨CommRing.of (polynomial ℤ),
 { hom :=
   { app := λ R r, (polynomial.aeval ℤ R r).to_ring_hom, },
   inv :=
   { app := λ R f, by { dsimp at f, exact f X, }, }, }⟩ -/

/-!
If you turn on `set_option pp.all true` above that definition, you'll get a more detailed message:
```
synthesized type class instance is not definitionally equal to expression inferred by typing rules,
synthesized
  @polynomial.algebra'.{0 0} int int.comm_semiring int (@comm_semiring.to_semiring.{0} int int.comm_semiring)
    (@algebra_int.{0} int int.ring)
inferred
  @polynomial.algebra'.{0 0} int int.comm_semiring int (@comm_semiring.to_semiring.{0} int int.comm_semiring)
    (@algebra.id.{0} int int.comm_semiring)
```

The difference here is that Lean has found two different ways to consider `ℤ` as an `ℤ`-algebra,
via `(@algebra_int.{0} int int.ring)` and via `(@algebra.id.{0} int int.comm_semiring)`.

The elaborator is not clever enough to see these are the same, even though there is actually
a `subsingleton (algebra ℤ R)` instance available.

At present, the work-around I know of is to use
`polynomial.eval₂_ring_hom (algebra_map ℤ R) r` instead of `(polynomial.aeval ℤ R r).to_ring_hom`.

If you find something better, let me know!
-/
