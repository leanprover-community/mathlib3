/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
import algebra.group_power.lemmas
import algebra.hom.group_instances

/-!
# Centroid homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `A` be a (non unital, non associative) algebra. The centroid of `A` is the set of linear maps
`T` on `A` such that `T` commutes with left and right multiplication, that is to say, for all `a`
and `b` in `A`,
$$
T(ab) = (Ta)b, T(ab) = a(Tb).
$$
In mathlib we call elements of the centroid "centroid homomorphisms" (`centroid_hom`) in keeping
with `add_monoid_hom` etc.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `centroid_hom`: Maps which preserve left and right multiplication.

## Typeclasses

* `centroid_hom_class`

## References

* [Jacobson, Structure of Rings][Jacobson1956]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

## Tags

centroid
-/

open function

variables {F α : Type*}

-- Making `centroid_hom` an old structure will allow the lemma `to_add_monoid_hom_eq_coe`
-- to be true by `rfl`. After upgrading to Lean 4, this should no longer be needed
-- because eta for structures should provide the same result.
set_option old_structure_cmd true

/-- The type of centroid homomorphisms from `α` to `α`. -/
structure centroid_hom (α : Type*) [non_unital_non_assoc_semiring α] extends α →+ α :=
(map_mul_left' (a b : α) : to_fun (a * b) = a * to_fun b)
(map_mul_right' (a b : α) : to_fun (a * b) = to_fun a * b)

attribute [nolint doc_blame] centroid_hom.to_add_monoid_hom

/-- `centroid_hom_class F α` states that `F` is a type of centroid homomorphisms.

You should extend this class when you extend `centroid_hom`. -/
class centroid_hom_class (F : Type*) (α : out_param $ Type*) [non_unital_non_assoc_semiring α]
  extends add_monoid_hom_class F α α :=
(map_mul_left (f : F) (a b : α) : f (a * b) = a * f b)
(map_mul_right (f : F) (a b : α) : f (a * b) = f a * b)

export centroid_hom_class (map_mul_left map_mul_right)

instance [non_unital_non_assoc_semiring α] [centroid_hom_class F α] :
  has_coe_t F (centroid_hom α) :=
⟨λ f, { to_fun := f, map_mul_left' := map_mul_left f, map_mul_right' := map_mul_right f,
  ..(f : α →+ α) }⟩

/-! ### Centroid homomorphisms -/

namespace centroid_hom

section non_unital_non_assoc_semiring

variables [non_unital_non_assoc_semiring α]

instance : centroid_hom_class (centroid_hom α) α :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_zero := λ f, f.map_zero',
  map_add := λ f, f.map_add',
  map_mul_left := λ f, f.map_mul_left',
  map_mul_right := λ f, f.map_mul_right' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (centroid_hom α) (λ _, α → α) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : centroid_hom α} : f.to_fun = (f : α → α) := rfl

@[ext] lemma ext {f g : centroid_hom α} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

@[simp, norm_cast] lemma coe_to_add_monoid_hom (f : centroid_hom α) : ⇑(f : α →+ α) = f := rfl
@[simp] lemma to_add_monoid_hom_eq_coe (f : centroid_hom α) : f.to_add_monoid_hom = f := rfl

lemma coe_to_add_monoid_hom_injective : injective (coe : centroid_hom α → α →+ α) :=
λ f g h, ext $ λ a, by { have := fun_like.congr_fun h a, exact this }

/-- Turn a centroid homomorphism into an additive monoid endomorphism. -/
def to_End (f : centroid_hom α) : add_monoid.End α := (f : α →+ α)

lemma to_End_injective : injective (centroid_hom.to_End : centroid_hom α → add_monoid.End α) :=
coe_to_add_monoid_hom_injective

/-- Copy of a `centroid_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : centroid_hom α) (f' : α → α) (h : f' = f) :
  centroid_hom α :=
{ to_fun := f',
  map_mul_left' := λ a b, by simp_rw [h, map_mul_left],
  map_mul_right' := λ a b, by simp_rw [h, map_mul_right],
  ..f.to_add_monoid_hom.copy f' $ by exact h }

@[simp] lemma coe_copy (f : centroid_hom α) (f' : α → α) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl

lemma copy_eq (f : centroid_hom α) (f' : α → α) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

variables (α)

/-- `id` as a `centroid_hom`. -/
protected def id : centroid_hom α :=
{ map_mul_left' := λ _ _, rfl,
  map_mul_right' := λ _ _, rfl,
  .. add_monoid_hom.id α }

instance : inhabited (centroid_hom α) := ⟨centroid_hom.id α⟩

@[simp, norm_cast] lemma coe_id : ⇑(centroid_hom.id α) = id := rfl

@[simp, norm_cast] lemma coe_to_add_monoid_hom_id :
  (centroid_hom.id α : α →+ α) = add_monoid_hom.id α := rfl

variables {α}

@[simp] lemma id_apply (a : α) : centroid_hom.id α a = a := rfl

/-- Composition of `centroid_hom`s as a `centroid_hom`. -/
def comp (g f : centroid_hom α) : centroid_hom α :=
{ map_mul_left' := λ a b, (congr_arg g $ f.map_mul_left' _ _).trans $ g.map_mul_left' _ _,
  map_mul_right' := λ a b, (congr_arg g $ f.map_mul_right' _ _).trans $ g.map_mul_right' _ _,
  .. g.to_add_monoid_hom.comp f.to_add_monoid_hom }

@[simp, norm_cast] lemma coe_comp (g f : centroid_hom α) : ⇑(g.comp f) = g ∘ f := rfl
@[simp] lemma comp_apply (g f : centroid_hom α) (a : α) : g.comp f a = g (f a) := rfl
@[simp, norm_cast] lemma coe_comp_add_monoid_hom (g f : centroid_hom α) :
  (g.comp f : α →+ α) = (g : α →+ α).comp f := rfl
@[simp] lemma comp_assoc (h g f : centroid_hom α) : (h.comp g).comp f = h.comp (g.comp f) := rfl
@[simp] lemma comp_id (f : centroid_hom α) : f.comp (centroid_hom.id α) = f := ext $ λ a, rfl
@[simp] lemma id_comp (f : centroid_hom α) : (centroid_hom.id α).comp f = f := ext $ λ a, rfl

lemma cancel_right {g₁ g₂ f : centroid_hom α} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g f₁ f₂ : centroid_hom α} (hg : injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ a, hg $ by rw [←comp_apply, h, comp_apply], congr_arg _⟩

instance : has_zero (centroid_hom α) :=
⟨{ map_mul_left' := λ a b, (mul_zero _).symm,
  map_mul_right' := λ a b, (zero_mul _).symm,
  ..(0 : α →+ α) }⟩

instance : has_one (centroid_hom α) := ⟨centroid_hom.id α⟩

instance : has_add (centroid_hom α) :=
⟨λ f g,
  { map_mul_left' := λ a b, by simp [map_mul_left, mul_add],
    map_mul_right' := λ a b, by simp [map_mul_right, add_mul],
    ..(f + g : α →+ α) } ⟩

instance : has_mul (centroid_hom α) := ⟨comp⟩

instance has_nsmul : has_smul ℕ (centroid_hom α) :=
⟨λ n f,
  { map_mul_left' := λ a b,
      by { change n • f (a * b) = a * n • f b, rw [map_mul_left f, ←mul_smul_comm] },
    map_mul_right' := λ a b,
      by { change n • f (a * b) = n • f a * b, rw [map_mul_right f, ←smul_mul_assoc] },
    .. (n • f : α →+ α) }⟩

instance has_npow_nat : has_pow (centroid_hom α) ℕ :=
⟨λ f n,
{  map_mul_left' := λ a b, begin
    induction n with n ih,
    { simp },
    { rw pow_succ,
      exact (congr_arg f.to_End ih).trans (f.map_mul_left' _ _) }
  end,
  map_mul_right' := λ a b, begin
    induction n with n ih,
    { simp },
    { rw pow_succ,
      exact (congr_arg f.to_End ih).trans (f.map_mul_right' _ _) }
  end,
  ..(f.to_End ^ n : add_monoid.End α) }⟩

@[simp, norm_cast] lemma coe_zero : ⇑(0 : centroid_hom α) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ⇑(1 : centroid_hom α) = id := rfl
@[simp, norm_cast] lemma coe_add (f g : centroid_hom α) : ⇑(f + g) = f + g := rfl
@[simp, norm_cast] lemma coe_mul (f g : centroid_hom α) : ⇑(f * g) = f ∘ g := rfl
-- Eligible for `dsimp`
@[simp, norm_cast, nolint simp_nf] lemma coe_nsmul (f : centroid_hom α) (n : ℕ) :
  ⇑(n • f) = n • f := rfl

@[simp] lemma zero_apply (a : α) : (0 : centroid_hom α) a = 0 := rfl
@[simp] lemma one_apply (a : α) : (1 : centroid_hom α) a = a := rfl
@[simp] lemma add_apply (f g : centroid_hom α) (a : α) : (f + g) a = f a + g a := rfl
@[simp] lemma mul_apply (f g : centroid_hom α) (a : α) : (f * g) a = f (g a) := rfl
-- Eligible for `dsimp`
@[simp, nolint simp_nf]
lemma nsmul_apply (f : centroid_hom α) (n : ℕ) (a : α) : (n • f) a = n • f a := rfl

@[simp] lemma to_End_zero : (0 : centroid_hom α).to_End = 0 := rfl
@[simp] lemma to_End_add (x y : centroid_hom α) : (x + y).to_End = x.to_End + y.to_End := rfl
lemma to_End_nsmul (x : centroid_hom α) (n : ℕ) : (n • x).to_End = n • x.to_End := rfl

-- cf.`add_monoid_hom.add_comm_monoid`
instance : add_comm_monoid (centroid_hom α) :=
coe_to_add_monoid_hom_injective.add_comm_monoid _ to_End_zero to_End_add to_End_nsmul

instance : has_nat_cast (centroid_hom α) :=
{ nat_cast := λ n, n • 1 }

@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : ⇑(n : centroid_hom α) = n • id := rfl

lemma nat_cast_apply (n : ℕ) (m : α):
  (n : centroid_hom α) m = n • m := rfl

@[simp] lemma to_End_one : (1 : centroid_hom α).to_End = 1 := rfl
@[simp] lemma to_End_mul (x y : centroid_hom α) : (x * y).to_End = x.to_End * y.to_End := rfl
@[simp] lemma to_End_pow (x : centroid_hom α) (n : ℕ) : (x ^ n).to_End = x.to_End ^ n :=
by { ext, refl }
@[simp, norm_cast] lemma to_End_nat_cast (n : ℕ) : (n : centroid_hom α).to_End = ↑n := rfl

-- cf `add_monoid.End.semiring`
instance : semiring (centroid_hom α) :=
to_End_injective.semiring _ to_End_zero to_End_one to_End_add to_End_mul
  to_End_nsmul to_End_pow to_End_nat_cast

lemma comp_mul_comm (T S : centroid_hom α) (a b : α) : (T ∘ S) (a * b) = (S ∘ T) (a * b) :=
by rw [comp_app, map_mul_right, map_mul_left, ←map_mul_right, ←map_mul_left]

end non_unital_non_assoc_semiring

section non_unital_non_assoc_ring
variables [non_unital_non_assoc_ring α]

/-- Negation of `centroid_hom`s as a `centroid_hom`. -/
instance : has_neg (centroid_hom α) :=
⟨λ f,
  { map_mul_left' := by simp [map_mul_left],
    map_mul_right' := by simp [map_mul_right],
    .. (-f : α →+ α) }⟩
instance : has_sub (centroid_hom α) :=
⟨λ f g,
{ map_mul_left' := λ a b, by simp [map_mul_left, mul_sub],
  map_mul_right' := λ a b, by simp [map_mul_right, sub_mul],
  .. (f - g : α →+ α) }⟩

instance has_zsmul : has_smul ℤ (centroid_hom α) :=
⟨λ n f,
  { map_mul_left' := λ a b,
      by { change n • f (a * b) = a * n • f b, rw [map_mul_left f, ←mul_smul_comm] },
    map_mul_right' := λ a b,
      by { change n • f (a * b) = n • f a * b, rw [map_mul_right f, ←smul_mul_assoc] },
    .. (n • f : α →+ α) }⟩

instance : has_int_cast (centroid_hom α) :=
{ int_cast := λ z, z • 1 }

@[simp, norm_cast] lemma coe_int_cast (z : ℤ) : ⇑(z : centroid_hom α) = z • id := rfl

lemma int_cast_apply (z : ℤ) (m : α) :
  (z : centroid_hom α) m = z • m := rfl

@[simp] lemma to_End_neg (x : centroid_hom α) : (-x).to_End = -x.to_End := rfl
@[simp] lemma to_End_sub (x y : centroid_hom α) : (x - y).to_End = x.to_End - y.to_End := rfl
lemma to_End_zsmul (x : centroid_hom α) (n : ℤ) : (n • x).to_End = n • x.to_End := rfl

instance : add_comm_group (centroid_hom α) :=
to_End_injective.add_comm_group _ to_End_zero to_End_add to_End_neg to_End_sub
  to_End_nsmul to_End_zsmul


@[simp, norm_cast] lemma coe_neg (f : centroid_hom α) : ⇑(-f) = -f := rfl
@[simp, norm_cast] lemma coe_sub (f g : centroid_hom α) : ⇑(f - g) = f - g := rfl

@[simp] lemma neg_apply (f : centroid_hom α) (a : α) : (-f) a = - f a := rfl
@[simp] lemma sub_apply (f g : centroid_hom α) (a : α) : (f - g) a = f a - g a := rfl

@[simp, norm_cast] lemma to_End_int_cast (z : ℤ) : (z : centroid_hom α).to_End = ↑z := rfl

instance : ring (centroid_hom α) := to_End_injective.ring _ to_End_zero to_End_one
  to_End_add to_End_mul to_End_neg to_End_sub to_End_nsmul to_End_zsmul
  to_End_pow to_End_nat_cast to_End_int_cast

end non_unital_non_assoc_ring

section non_unital_ring
variables [non_unital_ring α]

/-- A prime associative ring has commutative centroid. -/
@[reducible] -- See note [reducible non instances]
def comm_ring (h : ∀ a b : α, (∀ r : α, a * r * b = 0) → a = 0 ∨ b = 0) :
  comm_ring (centroid_hom α) :=
{ mul_comm := λ f g, begin
    ext,
    refine sub_eq_zero.1 ((or_self _).1 $ h _ _ $ λ r, _),
    rw [mul_assoc, sub_mul, sub_eq_zero, ← map_mul_right, ← map_mul_right, coe_mul, coe_mul,
      comp_mul_comm],
  end,
  ..centroid_hom.ring }

end non_unital_ring
end centroid_hom
