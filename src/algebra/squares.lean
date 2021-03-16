/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.algebra.basic
import linear_algebra.finsupp
import algebra.algebra.tower

/-!
#  Squares

Let `R` be a Type with `has_mul R`.

We introduce the predicate `is_square` on elements `r ∈ R`, asserting existence of an element
`s ∈ R`, such that the equality `r = s * s` holds.

Progressively assuming more of the type `R` we
* introduce the subtype `square R` of squares in `R`;
* introduce sums of squares, when `R` is an additive commutative monoid;
* prove an instance of `comm_semigroup` for `squares R`, if `R` is a `comm_semigroup`;
* prove an instance of `comm_monoid` for `squares R`, if `R` is a `comm_monoid`;
* prove an instance of `comm_semiring` for `sums_of_square R`, if `R` is a `comm_semiring`.
-/
variables {R : Type*}

section is_square

section has_mul

variables (R) [has_mul R]

/--  The predicate `is_square` on `r : R` is the assertion that there exists an element
`s : R` such that `r = s * s`. -/
def is_square (r : R) : Prop :=
∃ s : R, r = s * s

/--  The squares of a Type `R` with `has_mul` is the subtype of the elements of the form `s * s`,
for some `s : R`. -/
def squares : Type* := subtype (is_square R)

/--  The sums of squares of an `add_comm_monoid R` is the `ℕ`-submodule spanned by the squares. -/
def sums_of_squares [add_comm_monoid R] : submodule ℕ R :=
submodule.span ℕ { r : R | is_square R r }

namespace is_square

variables {R}

/-- The product of an element with itself is a square. -/
@[simp] lemma mul_self (r : R) : is_square R (r * r) :=
⟨_, rfl⟩

instance : has_coe (squares R) R := { coe := λ s, s.1 }

/--  The squaring function `R → squares R`, sending `r ↦ r * r`. -/
def squaring : R → squares R := λ r, ⟨_, mul_self r⟩

/-- The product of an element with itself is a sum of squares. -/
lemma mul_self_mem [add_comm_monoid R] (a : R) : a * a ∈ sums_of_squares R :=
submodule.mem_span.mpr (λ r hr, hr (mul_self _))

/-- A square is a sum of squares. -/
lemma squares_mem [add_comm_monoid R] (a : squares R) : (a : R) ∈ sums_of_squares R :=
begin
  refine submodule.mem_span.mpr (λ _ h, _),
  apply set.mem_of_mem_of_subset _ h,
  exact a.2,
end

end is_square

noncomputable instance squares_inhabited [nontrivial R] : inhabited (squares R) :=
⟨is_square.squaring (classical.arbitrary R)⟩

end has_mul

namespace is_square

section monoid

variable [monoid R]

/-- One is a square. -/
@[simp] lemma one : is_square R (1 : R) := ⟨_, (mul_one _).symm⟩

instance : has_one (squares R) := { one := ⟨_, one⟩ }

instance : inhabited (squares R) := ⟨1⟩

/-- The image of a square under a multiplicative map is a square. -/
lemma image {S : Type*} [monoid S] (f : R →* S) {a : R} (ha : is_square R a) :
  is_square S (f a) :=
by { rcases ha with ⟨a, rfl⟩, exact ⟨(f a), f.map_mul a a⟩ }

@[simp] lemma sq (a : R) : is_square R (a ^ 2) := ⟨a, pow_two _⟩

end monoid

section monoid_with_zero

variables [monoid_with_zero R]

instance : has_zero (squares R) := { zero := ⟨0, ⟨0, (zero_mul 0).symm⟩⟩ }

end monoid_with_zero

section comm_semigroup

variable [comm_semigroup R]

lemma mul_mem {a b : R} (as : a ∈ { r | is_square R r }) (bs : b ∈ { r | is_square R r }) :
  a * b ∈ { r | is_square R r } :=
begin
  rcases as with ⟨a, rfl⟩,
  rcases bs with ⟨b, rfl⟩,
  simp only [mul_mul_mul_comm a a b b, mul_self, set.mem_set_of_eq],
end

instance : has_mul (squares R) := { mul := λ a b, ⟨_, mul_mem a.2 b.2⟩ }

instance : comm_semigroup (squares R) :=
{ mul_assoc := λ a b c, subtype.ext (mul_assoc _ _ _),
  mul_comm := λ a b, subtype.ext (mul_comm _ _),
  ..(infer_instance : has_mul (squares R)) }

end comm_semigroup

section comm_monoid

variables [comm_monoid R]

/--  The set of squares in a commutative monoid `R` is a submonoid of `R`. -/
def squares.to_submonoid : submonoid R :=
{ carrier := { r | is_square R r },
  one_mem' := one,
  mul_mem' := λ a b ha hb, mul_mem ha hb }

instance : comm_monoid (squares R) :=
{ one_mul := λ a, subtype.ext (one_mul _),
  mul_one := λ a, subtype.ext (mul_one _),
  ..(infer_instance : comm_semigroup (squares R)),
  ..(infer_instance : has_one (squares R)) }

/--  The squaring map, as a multiplicative homomorphism. -/
def ring_hom.sq : R →* squares R :=
{ to_fun := squaring,
  map_one' := by simpa only [squaring, mul_one],
  map_mul' := λ a b, subtype.ext (mul_mul_mul_comm a b a b) }

/--  The product of two squares is a square. -/
lemma sq_mul_sq_mem (a b : R) : is_square R (a ^ 2 * b ^ 2) :=
begin
  refine ⟨a * b, _⟩,
  repeat { rw pow_two },
  exact mul_mul_mul_comm a a b b,
end

end comm_monoid

namespace sums_of_squares

section monoid

variables [add_comm_monoid R] [monoid R]

/-- One is a sum of squares. -/
@[simp] lemma one : (1 : R) ∈ sums_of_squares R :=
submodule.mem_span.mpr (λ p hp, hp one)

instance : has_one (sums_of_squares R) := { one := ⟨1, one⟩}

lemma nat {n : ℕ} : n • (1 : R) ∈ sums_of_squares R :=
begin
  induction n with n hn,
  { simp only [zero_smul, submodule.zero_mem] },
  { simp only [n.succ_eq_add_one, add_smul, hn, submodule.add_mem, one, one_smul] }
end

lemma sq_mem (a : R) : a ^ 2 ∈ sums_of_squares R :=
by { rw pow_two, exact mul_self_mem a }

lemma squares_mem (a : squares R) : (a : R) ∈ sums_of_squares R :=
begin
  refine submodule.mem_span.mpr (λ _ h, _),
  apply set.mem_of_mem_of_subset _ h,
  exact a.2,
end

lemma squares_subset_sums_of_squares {r : R} (hr : is_square R r) :
  r ∈ sums_of_squares R :=
begin
  rintros - ⟨H, rfl⟩,
  rintros - ⟨Hs, rfl⟩,
  rcases hr with ⟨r, rfl⟩,
  exact Hs (mul_self r)
end

lemma add_mem {a b : R} (ha : a ∈ sums_of_squares R) (hb : b ∈ sums_of_squares R) :
  a + b ∈ sums_of_squares R :=
submodule.add_mem (sums_of_squares R) ha hb

end monoid

section comm_semiring

variables [comm_semiring R] {a b : R}

lemma mul_mul_self_mem (ha : a ∈ sums_of_squares R) :
  a * (b * b) ∈ sums_of_squares R :=
begin
  rcases mem_span_set.mp ha with ⟨d, dsup, rfl⟩,
  simp_rw [finsupp.sum_mul, ← smul_eq_mul, smul_assoc],
  refine submodule.sum_mem _ (λ r rd, _),
  refine submodule.smul_mem _ (d r) _,
  rcases dsup rd with ⟨r, rfl⟩,
  rw [smul_eq_mul, smul_eq_mul, mul_mul_mul_comm r r b b],
  exact mul_self_mem (r * b),
end

lemma mul_sq_mem (ha : a ∈ sums_of_squares R) :
  a * b ^ 2 ∈ sums_of_squares R :=
by simp [pow_two, mul_mul_self_mem ha]

lemma of_mul_one (ab : a * b = 1) (as : a ∈ sums_of_squares R) :
  b ∈ sums_of_squares R :=
by { rw [← one_mul b, ← ab, mul_assoc, ← pow_two], exact mul_sq_mem as }

lemma iff_mul_one (ab : a * b = 1) :
  a ∈ sums_of_squares R ↔  b ∈ sums_of_squares R :=
⟨λ h, of_mul_one ab h, λ h, of_mul_one ((mul_comm _ _).trans ab) h⟩

lemma mul_mem (as : a ∈ sums_of_squares R) (hb : b ∈ sums_of_squares R) :
  a * b ∈ sums_of_squares R :=
begin
  rcases mem_span_set.mp hb with ⟨c, csup, rfl⟩,
  conv_lhs
  { rw finsupp.mul_sum,
    congr,
    skip,
    funext,
    rw [← smul_eq_mul, smul_comm, smul_eq_mul] },
  refine submodule.sum_mem (sums_of_squares R) (λ d hd, submodule.smul_mem _ (c d) _),
  rcases csup hd with ⟨d, rfl⟩,
  exact mul_mul_self_mem as,
end

instance : has_mul (sums_of_squares R) := { mul := λ a b, ⟨_, mul_mem a.2 b.2⟩ }

instance : comm_semiring (sums_of_squares R) :=
subtype.coe_injective.comm_semiring _ rfl rfl (λ ⟨x, hx⟩ y, rfl) (λ ⟨x, hx⟩ y, rfl)

end comm_semiring

end sums_of_squares

end is_square

end is_square
