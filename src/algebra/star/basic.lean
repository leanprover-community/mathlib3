import tactic.apply_fun
import algebra.algebra.basic
import algebra.ordered_ring

/-!
# star_monoid, star_ring, star_algebra

We introduce the basic algebraic notions of star monoids, star rings, and star algebras.

These are implemented as "mixin" typeclasses, so to summon a star ring (for example)
one needs to write `(R : Type) [ring R] [star_ring R]`.
This avoids difficulties with diamond inheritance.

For now we simply do not introduce notations,
as different users are expected to feel strongly about the relative merits of
`r^*`, `r†`, `rᘁ`, and so on.

Our star rings are actually star semirings, but of course we can prove
`star_neg : star (-r) = - star r` when the underlying semiring is a ring.
-/


universes u v

/--
Notation typeclass (with no default notation!) for an algebraic structure with a star operation.
-/
class has_star (R : Type u) :=
(star : R → R)

variables {R : Type u}

/--
A star operation (e.g. complex conjugate).
-/
def star [has_star R] (r : R) : R := has_star.star r

/--
Typeclass for a star operation with is involutive.
-/
class star_involutive (R : Type u) extends has_star R :=
(star_star : ∀ r : R, star (star r) = r)

@[simp] lemma star_star [star_involutive R] (r : R) : star (star r) = r :=
star_involutive.star_star _

lemma star_injective [star_involutive R] : function.injective (star : R → R) :=
begin
  intros x y h,
  apply_fun star at h,
  simpa using h,
end

/--
A *-monoid is a monoid `R` with an involutive operations `star`
so `star (r * s) = star s * star r`.
-/
class star_monoid (R : Type u) [monoid R] extends star_involutive R :=
(star_mul : ∀ r s : R, star (r * s) = star s * star r)

@[simp] lemma star_mul [monoid R] [star_monoid R] (r s : R) : star (r * s) = star s * star r :=
star_monoid.star_mul r s

@[simp] lemma star_one [monoid R] [star_monoid R] : star (1 : R) = 1 :=
begin
  have w : ∀ r, (star 1 : R) * r = r,
  { intro r, apply star_injective, simp, },
  simpa using w 1,
end

/--
A *-ring `R` is a (semi)ring with an involutive `star` operation which is additive
which makes `R` with its multiplicative structure into a *-monoid
(i.e. `star (r * s) = star s * star r`).
-/
class star_ring (R : Type u) [semiring R] extends star_monoid R :=
(star_zero : star 0 = 0)
(star_add : ∀ r s : R, star (r + s) = star r + star s)

@[simp] lemma star_zero [semiring R] [star_ring R] : star (0 : R) = 0 :=
star_ring.star_zero

@[simp] lemma star_add [semiring R] [star_ring R] (r s : R) : star (r + s) = star r + star s :=
star_ring.star_add r s

@[simp] lemma star_neg [ring R] [star_ring R] (r : R) : star (-r) = - star r :=
begin
  apply (add_left_inj (star r)).1,
  apply star_injective,
  simp,
end

/--
An ordered *-ring is a ring which is both an ordered ring and a *-star,
and `0 ≤ star r * r` for every `r`.

(In a Banach algebra, the natural ordering is given by the positive cone
which is the closure of the sums of elements `star r * r`.
This ordering makes the Banach algebra an ordered *-ring.)
-/
class star_ordered_ring (R : Type u) [ordered_semiring R] extends star_ring R :=
(star_mul_self_nonneg : ∀ r : R, 0 ≤ star r * r)

lemma star_mul_self_nonneg [ordered_semiring R] [star_ordered_ring R] {r : R} : 0 ≤ star r * r :=
star_ordered_ring.star_mul_self_nonneg r

/--
A star algebra `A` over a star ring `R` is an algebra which is a star ring,
and the two star structures are compatible in the sense
`star (r • a) = star r • star a`.
-/
class star_algebra (R : Type u) (A : Type v)
  [comm_semiring R] [star_ring R] [semiring A] [algebra R A] extends star_ring A :=
(star_smul : ∀ (r : R) (a : A), star (r • a) = (@has_star.star R _ r) • star a)

variables {A : Type v}

@[simp] lemma star_smul
  [comm_semiring R] [star_ring R] [semiring A] [algebra R A] [star_algebra R A] (r : R) (a : A) :
  star (r • a) = star r • star a :=
star_algebra.star_smul r a
