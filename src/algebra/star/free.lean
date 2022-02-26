/-
Copyright (c) 2020 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Weiser
-/
import algebra.star.basic
import algebra.free_algebra

/-!
# A *-algebra structure on the free algebra.

Reversing words gives a *-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `algebra.free_monoid` and `algebra.free_algebra`,
to avoid importing `algebra.star.basic` into the entire hierarchy.
-/

namespace free_monoid
variables {α : Type*}

instance : star_monoid (free_monoid α) :=
{ star := list.reverse,
  star_involutive := list.reverse_reverse,
  star_mul := list.reverse_append, }

@[simp]
lemma star_of (x : α) : star (of x) = of x := rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
lemma star_one : star (1 : free_monoid α) = 1 := rfl

end free_monoid

namespace free_algebra
variables {R : Type*} [comm_semiring R] {X : Type*}

/-- The star ring formed by reversing the elements of products -/
instance : star_ring (free_algebra R X) :=
{ star := mul_opposite.unop ∘ lift R (mul_opposite.op ∘ ι R),
  star_involutive := λ x, by
  { unfold has_star.star,
    simp only [function.comp_apply],
    refine free_algebra.induction R X _ _ _ _ x; intros; simp [*] },
  star_mul := λ a b, by simp,
  star_add := λ a b, by simp }

@[simp]
lemma star_ι (x : X) : star (ι R x) = (ι R x) :=
by simp [star, has_star.star]

@[simp]
lemma star_algebra_map (r : R) : star (algebra_map R (free_algebra R X) r) = (algebra_map R _ r) :=
by simp [star, has_star.star]

/-- `star` as an `alg_equiv` -/
def star_hom : free_algebra R X ≃ₐ[R] (free_algebra R X)ᵐᵒᵖ :=
{ commutes' := λ r, by simp [star_algebra_map],
  ..star_ring_equiv }

end free_algebra
