/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.algebra.equiv
import linear_algebra.finrank
import linear_algebra.free_module.basic
import linear_algebra.free_module.finite.basic
import set_theory.cardinal.ordinal
import tactic.ring_exp

/-!
# Quaternions

In this file we define quaternions `ℍ[R]` over a commutative ring `R`, and define some
algebraic structures on `ℍ[R]`.

## Main definitions

* `quaternion_algebra R a b`, `ℍ[R, a, b]` :
  [quaternion algebra](https://en.wikipedia.org/wiki/Quaternion_algebra) with coefficients `a`, `b`
* `quaternion R`, `ℍ[R]` : the space of quaternions, a.k.a. `quaternion_algebra R (-1) (-1)`;
* `quaternion.norm_sq` : square of the norm of a quaternion;
* `quaternion.conj` : conjugate of a quaternion;

We also define the following algebraic structures on `ℍ[R]`:

* `ring ℍ[R, a, b]` and `algebra R ℍ[R, a, b]` : for any commutative ring `R`;
* `ring ℍ[R]` and `algebra R ℍ[R]` : for any commutative ring `R`;
* `domain ℍ[R]` : for a linear ordered commutative ring `R`;
* `division_algebra ℍ[R]` : for a linear ordered field `R`.

## Notation

The following notation is available with `open_locale quaternion`.

* `ℍ[R, c₁, c₂]` : `quaternion_algebra R  c₁ c₂`
* `ℍ[R]` : quaternions over `R`.

## Implementation notes

We define quaternions over any ring `R`, not just `ℝ` to be able to deal with, e.g., integer
or rational quaternions without using real numbers. In particular, all definitions in this file
are computable.

## Tags

quaternion
-/

/-- Quaternion algebra over a type with fixed coefficients $a=i^2$ and $b=j^2$.
Implemented as a structure with four fields: `re`, `im_i`, `im_j`, and `im_k`. -/
@[nolint unused_arguments, ext]
structure quaternion_algebra (R : Type*) (a b : R) :=
mk {} :: (re : R) (im_i : R) (im_j : R) (im_k : R)

localized "notation (name := quaternion_algebra) `ℍ[` R`,` a`,` b `]` :=
  quaternion_algebra R a b" in quaternion

namespace quaternion_algebra

/-- The equivalence between a quaternion algebra over R and R × R × R × R. -/
@[simps]
def equiv_prod {R : Type*} (c₁ c₂ : R) : ℍ[R, c₁, c₂] ≃ R × R × R × R :=
{ to_fun := λ a, ⟨a.1, a.2, a.3, a.4⟩,
  inv_fun := λ a, ⟨a.1, a.2.1, a.2.2.1, a.2.2.2⟩,
  left_inv := λ ⟨a₁, a₂, a₃, a₄⟩, rfl,
  right_inv := λ ⟨a₁, a₂, a₃, a₄⟩, rfl }

/-- The equivalence between a quaternion algebra over `R` and `fin 4 → R`. -/
@[simps symm_apply]
def equiv_tuple {R : Type*} (c₁ c₂ : R) : ℍ[R, c₁, c₂] ≃ (fin 4 → R) :=
{ to_fun := λ a, ![a.1, a.2, a.3, a.4],
  inv_fun := λ a, ⟨a 0, a 1, a 2, a 3⟩,
  left_inv := λ ⟨a₁, a₂, a₃, a₄⟩, rfl,
  right_inv := λ f, by ext ⟨_, _|_|_|_|_|⟨⟩⟩; refl }

@[simp] lemma equiv_tuple_apply {R : Type*} (c₁ c₂ : R) (x : ℍ[R, c₁, c₂]) :
  equiv_tuple c₁ c₂ x = ![x.re, x.im_i, x.im_j, x.im_k] := rfl

@[simp] lemma mk.eta {R : Type*} {c₁ c₂} : ∀ a : ℍ[R, c₁, c₂], mk a.1 a.2 a.3 a.4 = a
| ⟨a₁, a₂, a₃, a₄⟩ := rfl

variables {S T R : Type*} [comm_ring R] {c₁ c₂ : R} (r x y z : R) (a b c : ℍ[R, c₁, c₂])

/-- The imaginary part of a quaternion. -/
def im (x : ℍ[R, c₁, c₂]) : ℍ[R, c₁, c₂] := ⟨0, x.im_i, x.im_j, x.im_k⟩

@[simp] lemma im_re : a.im.re = 0 := rfl
@[simp] lemma im_im_i : a.im.im_i = a.im_i := rfl
@[simp] lemma im_im_j : a.im.im_j = a.im_j := rfl
@[simp] lemma im_im_k : a.im.im_k = a.im_k := rfl
@[simp] lemma im_idem : a.im.im = a.im := rfl

instance : has_coe_t R (ℍ[R, c₁, c₂]) := ⟨λ x, ⟨x, 0, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_re : (x : ℍ[R, c₁, c₂]).re = x := rfl
@[simp, norm_cast] lemma coe_im_i : (x : ℍ[R, c₁, c₂]).im_i = 0 := rfl
@[simp, norm_cast] lemma coe_im_j : (x : ℍ[R, c₁, c₂]).im_j = 0 := rfl
@[simp, norm_cast] lemma coe_im_k : (x : ℍ[R, c₁, c₂]).im_k = 0 := rfl

lemma coe_injective : function.injective (coe : R → ℍ[R, c₁, c₂]) :=
λ x y h, congr_arg re h

@[simp] lemma coe_inj {x y : R} : (x : ℍ[R, c₁, c₂]) = y ↔ x = y := coe_injective.eq_iff

@[simps] instance : has_zero ℍ[R, c₁, c₂] := ⟨⟨0, 0, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_zero : ((0 : R) : ℍ[R, c₁, c₂]) = 0 := rfl

instance : inhabited ℍ[R, c₁, c₂] := ⟨0⟩

@[simps] instance : has_one ℍ[R, c₁, c₂] := ⟨⟨1, 0, 0, 0⟩⟩

@[simp, norm_cast] lemma coe_one : ((1 : R) : ℍ[R, c₁, c₂]) = 1 := rfl

@[simps] instance : has_add ℍ[R, c₁, c₂] :=
⟨λ a b, ⟨a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4⟩⟩

@[simp] lemma mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) + mk b₁ b₂ b₃ b₄ = mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) :=
rfl

@[norm_cast, simp] lemma coe_add : ((x + y : R) : ℍ[R, c₁, c₂]) = x + y :=
by ext; simp

@[simps] instance : has_neg ℍ[R, c₁, c₂] := ⟨λ a, ⟨-a.1, -a.2, -a.3, -a.4⟩⟩

@[simp] lemma neg_mk (a₁ a₂ a₃ a₄ : R) : -(mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) = ⟨-a₁, -a₂, -a₃, -a₄⟩ :=
rfl

@[norm_cast, simp] lemma coe_neg : ((-x : R) : ℍ[R, c₁, c₂]) = -x :=
by ext; simp

@[simps] instance : has_sub ℍ[R, c₁, c₂] :=
⟨λ a b, ⟨a.1 - b.1, a.2 - b.2, a.3 - b.3, a.4 - b.4⟩⟩

@[simp] lemma mk_sub_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) - mk b₁ b₂ b₃ b₄ = mk (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) (a₄ - b₄) :=
rfl

@[simp, norm_cast] lemma coe_im : (x : ℍ[R, c₁, c₂]).im = 0 := rfl

@[simp] lemma re_add_im : ↑a.re + a.im = a :=
ext _ _ (add_zero _) (zero_add _) (zero_add _) (zero_add _)

@[simp] lemma sub_self_im : a - a.im = a.re :=
ext _ _ (sub_zero _) (sub_self _) (sub_self _) (sub_self _)

@[simp] lemma sub_self_re : a - a.re = a.im :=
ext _ _ (sub_self _) (sub_zero _) (sub_zero _) (sub_zero _)

/-- Multiplication is given by

* `1 * x = x * 1 = x`;
* `i * i = c₁`;
* `j * j = c₂`;
* `i * j = k`, `j * i = -k`;
* `k * k = -c₁ * c₂`;
* `i * k = c₁ * j`, `k * i = `-c₁ * j`;
* `j * k = -c₂ * i`, `k * j = c₂ * i`.  -/
@[simps] instance : has_mul ℍ[R, c₁, c₂] := ⟨λ a b,
  ⟨a.1 * b.1 + c₁ * a.2 * b.2 + c₂ * a.3 * b.3 - c₁ * c₂ * a.4 * b.4,
   a.1 * b.2 + a.2 * b.1 - c₂ * a.3 * b.4 + c₂ * a.4 * b.3,
   a.1 * b.3 + c₁ * a.2 * b.4 + a.3 * b.1 - c₁ *  a.4 * b.2,
   a.1 * b.4 + a.2 * b.3 - a.3 * b.2 + a.4 * b.1⟩⟩

@[simp] lemma mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
  (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) * mk b₁ b₂ b₃ b₄ =
    ⟨a₁ * b₁ + c₁ * a₂ * b₂ + c₂ * a₃ * b₃ - c₁ * c₂ * a₄ * b₄,
     a₁ * b₂ + a₂ * b₁ - c₂ * a₃ * b₄ + c₂ * a₄ * b₃,
     a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ - c₁ *  a₄ * b₂,
     a₁ * b₄ + a₂ * b₃ - a₃ * b₂ + a₄ * b₁⟩ := rfl

section
variables [has_smul S R] [has_smul T R] (s : S)

/-
The `ring R` argument is not used, but it's also much stronger than the other definitions in this
file need; for instance `quaternion_algebra.has_zero` only really needs `has_zero R`. For
simplicity we just keep things consistent.
-/
@[nolint unused_arguments]
instance : has_smul S ℍ[R, c₁, c₂] :=
{ smul := λ s a, ⟨s • a.1, s • a.2, s • a.3, s • a.4⟩ }

instance [has_smul S T] [is_scalar_tower S T R] : is_scalar_tower S T ℍ[R, c₁, c₂] :=
{ smul_assoc := λ s t x, by ext; exact smul_assoc _ _ _ }

instance [smul_comm_class S T R] : smul_comm_class S T ℍ[R, c₁, c₂] :=
{ smul_comm := λ s t x, by ext; exact smul_comm _ _ _ }

@[simp] lemma smul_re : (s • a).re = s • a.re := rfl
@[simp] lemma smul_im_i : (s • a).im_i = s • a.im_i := rfl
@[simp] lemma smul_im_j : (s • a).im_j = s • a.im_j := rfl
@[simp] lemma smul_im_k : (s • a).im_k = s • a.im_k := rfl

@[simp] lemma smul_mk (re im_i im_j im_k : R) :
  s • (⟨re, im_i, im_j, im_k⟩ : ℍ[R, c₁, c₂]) = ⟨s • re, s • im_i, s • im_j, s • im_k⟩ := rfl

end

@[simp, norm_cast] lemma coe_smul [smul_zero_class S R] (s : S) (r : R) :
  (↑(s • r) : ℍ[R, c₁, c₂]) = s • ↑r :=
ext _ _ rfl (smul_zero s).symm (smul_zero s).symm (smul_zero s).symm

instance : add_comm_group ℍ[R, c₁, c₂] :=
by refine_struct
  { add := (+),
    neg := has_neg.neg,
    sub := has_sub.sub,
    zero := (0 : ℍ[R, c₁, c₂]),
    nsmul := (•),
    zsmul := (•), };
  intros; try { refl }; ext; simp; ring_exp

instance : add_group_with_one ℍ[R, c₁, c₂] :=
{ nat_cast := λ n, ((n : R) : ℍ[R, c₁, c₂]),
  nat_cast_zero := by simp,
  nat_cast_succ := by simp,
  int_cast := λ n, ((n : R) : ℍ[R, c₁, c₂]),
  int_cast_of_nat := λ _, congr_arg coe (int.cast_of_nat _),
  int_cast_neg_succ_of_nat := λ n,
    show ↑↑_ = -↑↑_, by rw [int.cast_neg, int.cast_coe_nat, coe_neg],
  one := 1,
  .. quaternion_algebra.add_comm_group }

@[simp, norm_cast] lemma nat_cast_re (n : ℕ) : (n : ℍ[R, c₁, c₂]).re = n := rfl
@[simp, norm_cast] lemma nat_cast_im_i (n : ℕ) : (n : ℍ[R, c₁, c₂]).im_i = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im_j (n : ℕ) : (n : ℍ[R, c₁, c₂]).im_j = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im_k (n : ℕ) : (n : ℍ[R, c₁, c₂]).im_k = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im (n : ℕ) : (n : ℍ[R, c₁, c₂]).im = 0 := rfl
@[norm_cast] lemma coe_nat_cast (n : ℕ) : ↑(n : R) = (n : ℍ[R, c₁, c₂]) := rfl

@[simp, norm_cast] lemma int_cast_re (z : ℤ) : (z : ℍ[R, c₁, c₂]).re = z := rfl
@[simp, norm_cast] lemma int_cast_im_i (z : ℤ) : (z : ℍ[R, c₁, c₂]).im_i = 0 := rfl
@[simp, norm_cast] lemma int_cast_im_j (z : ℤ) : (z : ℍ[R, c₁, c₂]).im_j = 0 := rfl
@[simp, norm_cast] lemma int_cast_im_k (z : ℤ) : (z : ℍ[R, c₁, c₂]).im_k = 0 := rfl
@[simp, norm_cast] lemma int_cast_im (z : ℤ) : (z : ℍ[R, c₁, c₂]).im = 0 := rfl
@[norm_cast] lemma coe_int_cast (z : ℤ) : ↑(z : R) = (z : ℍ[R, c₁, c₂]) := rfl

instance : ring ℍ[R, c₁, c₂] :=
by refine_struct
  { add := (+),
    mul := (*),
    one := 1,
    npow := @npow_rec _ ⟨(1 : ℍ[R, c₁, c₂])⟩ ⟨(*)⟩,
    .. quaternion_algebra.add_group_with_one,
    .. quaternion_algebra.add_comm_group };
  intros; try { refl }; ext; simp; ring_exp

@[norm_cast, simp] lemma coe_mul : ((x * y : R) : ℍ[R, c₁, c₂]) = x * y :=
by ext; simp

-- TODO: add weaker `mul_action`, `distrib_mul_action`, and `module` instances (and repeat them
-- for `ℍ[R]`)
instance [comm_semiring S] [algebra S R] : algebra S ℍ[R, c₁, c₂] :=
{ smul := (•),
  to_fun := λ s, coe (algebra_map S R s),
  map_one' := by simpa only [map_one],
  map_zero' := by simpa only [map_zero],
  map_mul' := λ x y, by rw [map_mul, coe_mul],
  map_add' := λ x y, by rw [map_add, coe_add],
  smul_def' := λ s x, by ext; simp [algebra.smul_def],
  commutes' := λ s x, by ext; simp [algebra.commutes] }

lemma algebra_map_eq (r : R) : algebra_map R ℍ[R,c₁,c₂] r = ⟨r, 0, 0, 0⟩ := rfl

section
variables (c₁ c₂)

/-- `quaternion_algebra.re` as a `linear_map`-/
@[simps] def re_lm : ℍ[R, c₁, c₂] →ₗ[R] R :=
{ to_fun := re, map_add' := λ x y, rfl, map_smul' := λ r x, rfl }

/-- `quaternion_algebra.im_i` as a `linear_map`-/
@[simps] def im_i_lm : ℍ[R, c₁, c₂] →ₗ[R] R :=
{ to_fun := im_i, map_add' := λ x y, rfl, map_smul' := λ r x, rfl }

/-- `quaternion_algebra.im_j` as a `linear_map`-/
@[simps] def im_j_lm : ℍ[R, c₁, c₂] →ₗ[R] R :=
{ to_fun := im_j, map_add' := λ x y, rfl, map_smul' := λ r x, rfl }

/-- `quaternion_algebra.im_k` as a `linear_map`-/
@[simps] def im_k_lm : ℍ[R, c₁, c₂] →ₗ[R] R :=
{ to_fun := im_k, map_add' := λ x y, rfl, map_smul' := λ r x, rfl }

/-- `quaternion_algebra.equiv_tuple` as a linear equivalence. -/
def linear_equiv_tuple : ℍ[R,c₁,c₂] ≃ₗ[R] (fin 4 → R) :=
linear_equiv.symm  -- proofs are not `rfl` in the forward direction
  { to_fun := (equiv_tuple c₁ c₂).symm,
    inv_fun := equiv_tuple c₁ c₂,
    map_add' := λ v₁ v₂, rfl,
    map_smul' := λ v₁ v₂, rfl,
    .. (equiv_tuple c₁ c₂).symm }

@[simp] lemma coe_linear_equiv_tuple : ⇑(linear_equiv_tuple c₁ c₂) = equiv_tuple c₁ c₂ := rfl
@[simp] lemma coe_linear_equiv_tuple_symm :
  ⇑(linear_equiv_tuple c₁ c₂).symm = (equiv_tuple c₁ c₂).symm := rfl

/-- `ℍ[R, c₁, c₂]` has a basis over `R` given by `1`, `i`, `j`, and `k`. -/
noncomputable def basis_one_i_j_k : basis (fin 4) R ℍ[R, c₁, c₂] :=
basis.of_equiv_fun $ linear_equiv_tuple c₁ c₂

@[simp] lemma coe_basis_one_i_j_k_repr (q : ℍ[R, c₁, c₂]) :
  ⇑((basis_one_i_j_k c₁ c₂).repr q) = ![q.re, q.im_i, q.im_j, q.im_k] := rfl

instance : module.finite R ℍ[R, c₁, c₂] := module.finite.of_basis (basis_one_i_j_k c₁ c₂)
instance : module.free R ℍ[R, c₁, c₂] := module.free.of_basis (basis_one_i_j_k c₁ c₂)

lemma dim_eq_four [strong_rank_condition R] : module.rank R ℍ[R, c₁, c₂] = 4 :=
by { rw [dim_eq_card_basis (basis_one_i_j_k c₁ c₂), fintype.card_fin], norm_num }

lemma finrank_eq_four [strong_rank_condition R] : finite_dimensional.finrank R ℍ[R, c₁, c₂] = 4 :=
have cardinal.to_nat 4 = 4,
  by rw [←cardinal.to_nat_cast 4, nat.cast_bit0, nat.cast_bit0, nat.cast_one],
by rw [finite_dimensional.finrank, dim_eq_four, this]

end

@[norm_cast, simp] lemma coe_sub : ((x - y : R) : ℍ[R, c₁, c₂]) = x - y :=
(algebra_map R ℍ[R, c₁, c₂]).map_sub x y

@[norm_cast, simp] lemma coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R, c₁, c₂]) = ↑x ^ n :=
(algebra_map R ℍ[R, c₁, c₂]).map_pow x n

lemma coe_commutes : ↑r * a = a * r := algebra.commutes r a

lemma coe_commute : commute ↑r a := coe_commutes r a

lemma coe_mul_eq_smul : ↑r * a = r • a := (algebra.smul_def r a).symm

lemma mul_coe_eq_smul : a * r = r • a :=
by rw [← coe_commutes, coe_mul_eq_smul]

@[norm_cast, simp] lemma coe_algebra_map : ⇑(algebra_map R ℍ[R, c₁, c₂]) = coe := rfl

lemma smul_coe : x • (y : ℍ[R, c₁, c₂]) = ↑(x * y) := by rw [coe_mul, coe_mul_eq_smul]

/-- Quaternion conjugate. -/
def conj : ℍ[R, c₁, c₂] ≃ₗ[R] ℍ[R, c₁, c₂] :=
linear_equiv.of_involutive
{ to_fun := λ a, ⟨a.1, -a.2, -a.3, -a.4⟩,
  map_add' := λ a b, by ext; simp [neg_add],
  map_smul' := λ r a, by ext; simp } $
λ a, by simp

@[simp] lemma re_conj : (conj a).re = a.re := rfl
@[simp] lemma im_i_conj : (conj a).im_i = - a.im_i := rfl
@[simp] lemma im_j_conj : (conj a).im_j = - a.im_j := rfl
@[simp] lemma im_k_conj : (conj a).im_k = - a.im_k := rfl
@[simp] lemma im_conj : (conj a).im = - a.im := ext _ _ neg_zero.symm rfl rfl rfl

@[simp] lemma conj_mk (a₁ a₂ a₃ a₄ : R) :
  conj (mk a₁ a₂ a₃ a₄ : ℍ[R, c₁, c₂]) = ⟨a₁, -a₂, -a₃, -a₄⟩ :=
rfl

@[simp] lemma conj_conj : a.conj.conj = a := ext _ _ rfl (neg_neg _) (neg_neg _) (neg_neg _)

lemma conj_add : (a + b).conj = a.conj + b.conj := conj.map_add a b

@[simp] lemma conj_mul : (a * b).conj = b.conj * a.conj := by ext; simp; ring_exp

lemma conj_conj_mul : (a.conj * b).conj = b.conj * a :=
by rw [conj_mul, conj_conj]

lemma conj_mul_conj : (a * b.conj).conj = b * a.conj :=
by rw [conj_mul, conj_conj]

lemma self_add_conj' : a + a.conj = ↑(2 * a.re) := by ext; simp [two_mul]

lemma self_add_conj : a + a.conj = 2 * a.re :=
by simp only [self_add_conj', two_mul, coe_add]

lemma conj_add_self' : a.conj + a = ↑(2 * a.re) := by rw [add_comm, self_add_conj']

lemma conj_add_self : a.conj + a = 2 * a.re := by rw [add_comm, self_add_conj]

lemma conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a := eq_sub_iff_add_eq.2 a.conj_add_self'

lemma commute_conj_self : commute a.conj a :=
begin
  rw [a.conj_eq_two_re_sub],
  exact (coe_commute (2 * a.re) a).sub_left (commute.refl a)
end

lemma commute_self_conj : commute a a.conj :=
a.commute_conj_self.symm

lemma commute_conj_conj {a b : ℍ[R, c₁, c₂]} (h : commute a b) : commute a.conj b.conj :=
calc a.conj * b.conj = (b * a).conj    : (conj_mul b a).symm
                 ... = (a * b).conj    : by rw h.eq
                 ... = b.conj * a.conj : conj_mul a b

@[simp, norm_cast] lemma conj_coe : conj (x : ℍ[R, c₁, c₂]) = x := by ext; simp

@[simp] lemma conj_im : conj a.im = - a.im := im_conj _

@[simp, norm_cast] lemma conj_nat_cast (n : ℕ) : conj (n : ℍ[R, c₁, c₂]) = n :=
by rw [←coe_nat_cast, conj_coe]
@[simp, norm_cast] lemma conj_int_cast (z : ℤ) : conj (z : ℍ[R, c₁, c₂]) = z :=
by rw [←coe_int_cast, conj_coe]

@[simp] lemma conj_smul [monoid S] [distrib_mul_action S R] (s : S) (a : ℍ[R, c₁, c₂]) :
  conj (s • a) = s • conj a :=
ext _ _ rfl (smul_neg _ _).symm (smul_neg _ _).symm (smul_neg _ _).symm

@[simp] lemma conj_one : conj (1 : ℍ[R, c₁, c₂]) = 1 := conj_coe 1

lemma eq_re_of_eq_coe {a : ℍ[R, c₁, c₂]} {x : R} (h : a = x) : a = a.re :=
by rw [h, coe_re]

lemma eq_re_iff_mem_range_coe {a : ℍ[R, c₁, c₂]} :
  a = a.re ↔ a ∈ set.range (coe : R → ℍ[R, c₁, c₂]) :=
⟨λ h, ⟨a.re, h.symm⟩, λ ⟨x, h⟩, eq_re_of_eq_coe h.symm⟩

@[simp]
lemma conj_fixed {R : Type*} [comm_ring R] [no_zero_divisors R] [char_zero R]
  {c₁ c₂ : R} {a : ℍ[R, c₁, c₂]} :
  conj a = a ↔ a = a.re :=
by simp [ext_iff, neg_eq_iff_add_eq_zero, add_self_eq_zero]

-- Can't use `rw ← conj_fixed` in the proof without additional assumptions

lemma conj_mul_eq_coe : conj a * a = (conj a * a).re := by ext; simp; ring_exp

lemma mul_conj_eq_coe : a * conj a = (a * conj a).re :=
by { rw a.commute_self_conj.eq, exact a.conj_mul_eq_coe }

lemma conj_zero : conj (0 : ℍ[R, c₁, c₂]) = 0 := conj.map_zero

lemma conj_neg : (-a).conj = -a.conj := (conj : ℍ[R, c₁, c₂] ≃ₗ[R] _).map_neg a

lemma conj_sub : (a - b).conj = a.conj - b.conj := (conj : ℍ[R, c₁, c₂] ≃ₗ[R] _).map_sub a b

instance : star_ring ℍ[R, c₁, c₂] :=
{ star := conj,
  star_involutive := conj_conj,
  star_add := conj_add,
  star_mul := conj_mul }

@[simp] lemma star_def (a : ℍ[R, c₁, c₂]) : star a = conj a := rfl

@[simp] lemma conj_pow (n : ℕ) : (a ^ n).conj = a.conj ^ n := star_pow _ _

open mul_opposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_ae : ℍ[R, c₁, c₂] ≃ₐ[R] (ℍ[R, c₁, c₂]ᵐᵒᵖ) :=
{ to_fun := op ∘ conj,
  inv_fun := conj ∘ unop,
  map_mul' := λ x y, by simp,
  commutes' := λ r, by simp,
  .. conj.to_add_equiv.trans op_add_equiv }

@[simp] lemma coe_conj_ae : ⇑(conj_ae : ℍ[R, c₁, c₂] ≃ₐ[R] _) = op ∘ conj := rfl

end quaternion_algebra

/-- Space of quaternions over a type. Implemented as a structure with four fields:
`re`, `im_i`, `im_j`, and `im_k`. -/
def quaternion (R : Type*) [has_one R] [has_neg R] := quaternion_algebra R (-1) (-1)

localized "notation (name := quaternion) `ℍ[` R `]` := quaternion R" in quaternion

/-- The equivalence between the quaternions over `R` and `R × R × R × R`. -/
@[simps]
def quaternion.equiv_prod (R : Type*) [has_one R] [has_neg R] : ℍ[R] ≃ R × R × R × R :=
quaternion_algebra.equiv_prod _ _

/-- The equivalence between the quaternions over `R` and `fin 4 → R`. -/
@[simps symm_apply]
def quaternion.equiv_tuple (R : Type*) [has_one R] [has_neg R] : ℍ[R] ≃ (fin 4 → R) :=
quaternion_algebra.equiv_tuple _ _

@[simp] lemma quaternion.equiv_tuple_apply (R : Type*) [has_one R] [has_neg R] (x : ℍ[R]) :
  quaternion.equiv_tuple R x = ![x.re, x.im_i, x.im_j, x.im_k] := rfl

namespace quaternion

variables {S T R : Type*} [comm_ring R] (r x y z : R) (a b c : ℍ[R])

export quaternion_algebra (re im_i im_j im_k)

instance : has_coe_t R ℍ[R] := quaternion_algebra.has_coe_t
instance : ring ℍ[R] := quaternion_algebra.ring
instance : inhabited ℍ[R] := quaternion_algebra.inhabited
instance [has_smul S R] : has_smul S ℍ[R] := quaternion_algebra.has_smul
instance [has_smul S T] [has_smul S R] [has_smul T R] [is_scalar_tower S T R] :
  is_scalar_tower S T ℍ[R] := quaternion_algebra.is_scalar_tower
instance [has_smul S R] [has_smul T R] [smul_comm_class S T R] :
  smul_comm_class S T ℍ[R] := quaternion_algebra.smul_comm_class
instance [comm_semiring S] [algebra S R] : algebra S ℍ[R] := quaternion_algebra.algebra
instance : star_ring ℍ[R] := quaternion_algebra.star_ring

@[ext] lemma ext : a.re = b.re → a.im_i = b.im_i → a.im_j = b.im_j → a.im_k = b.im_k → a = b :=
quaternion_algebra.ext a b

lemma ext_iff {a b : ℍ[R]} :
  a = b ↔ a.re = b.re ∧ a.im_i = b.im_i ∧ a.im_j = b.im_j ∧ a.im_k = b.im_k :=
quaternion_algebra.ext_iff a b

/-- The imaginary part of a quaternion. -/
def im (x : ℍ[R]) : ℍ[R] := x.im

@[simp] lemma im_re : a.im.re = 0 := rfl
@[simp] lemma im_im_i : a.im.im_i = a.im_i := rfl
@[simp] lemma im_im_j : a.im.im_j = a.im_j := rfl
@[simp] lemma im_im_k : a.im.im_k = a.im_k := rfl
@[simp] lemma im_idem : a.im.im = a.im := rfl

@[simp] lemma re_add_im : ↑a.re + a.im = a := a.re_add_im
@[simp] lemma sub_self_im : a - a.im = a.re := a.sub_self_im
@[simp] lemma sub_self_re : a - a.re = a.im := a.sub_self_re

@[simp, norm_cast] lemma coe_re : (x : ℍ[R]).re = x := rfl
@[simp, norm_cast] lemma coe_im_i : (x : ℍ[R]).im_i = 0 := rfl
@[simp, norm_cast] lemma coe_im_j : (x : ℍ[R]).im_j = 0 := rfl
@[simp, norm_cast] lemma coe_im_k : (x : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma coe_im : (x : ℍ[R]).im = 0 := rfl

@[simp] lemma zero_re : (0 : ℍ[R]).re = 0 := rfl
@[simp] lemma zero_im_i : (0 : ℍ[R]).im_i = 0 := rfl
@[simp] lemma zero_im_j : (0 : ℍ[R]).im_j = 0 := rfl
@[simp] lemma zero_im_k : (0 : ℍ[R]).im_k = 0 := rfl
@[simp] lemma zero_im : (0 : ℍ[R]).im = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : R) : ℍ[R]) = 0 := rfl

@[simp] lemma one_re : (1 : ℍ[R]).re = 1 := rfl
@[simp] lemma one_im_i : (1 : ℍ[R]).im_i = 0 := rfl
@[simp] lemma one_im_j : (1 : ℍ[R]).im_j = 0 := rfl
@[simp] lemma one_im_k : (1 : ℍ[R]).im_k = 0 := rfl
@[simp] lemma one_im : (1 : ℍ[R]).im = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : R) : ℍ[R]) = 1 := rfl

@[simp] lemma add_re : (a + b).re = a.re + b.re := rfl
@[simp] lemma add_im_i : (a + b).im_i = a.im_i + b.im_i := rfl
@[simp] lemma add_im_j : (a + b).im_j = a.im_j + b.im_j := rfl
@[simp] lemma add_im_k : (a + b).im_k = a.im_k + b.im_k := rfl
@[simp] lemma add_im : (a + b).im = a.im + b.im := ext _ _ (add_zero _).symm rfl rfl rfl
@[simp, norm_cast] lemma coe_add : ((x + y : R) : ℍ[R]) = x + y := quaternion_algebra.coe_add x y

@[simp] lemma neg_re : (-a).re = -a.re := rfl
@[simp] lemma neg_im_i : (-a).im_i = -a.im_i := rfl
@[simp] lemma neg_im_j : (-a).im_j = -a.im_j := rfl
@[simp] lemma neg_im_k : (-a).im_k = -a.im_k := rfl
@[simp] lemma neg_im : (-a).im = -a.im := ext _ _ neg_zero.symm rfl rfl rfl
@[simp, norm_cast] lemma coe_neg : ((-x : R) : ℍ[R]) = -x := quaternion_algebra.coe_neg x

@[simp] lemma sub_re : (a - b).re = a.re - b.re := rfl
@[simp] lemma sub_im_i : (a - b).im_i = a.im_i - b.im_i := rfl
@[simp] lemma sub_im_j : (a - b).im_j = a.im_j - b.im_j := rfl
@[simp] lemma sub_im_k : (a - b).im_k = a.im_k - b.im_k := rfl
@[simp] lemma sub_im : (a - b).im = a.im - b.im := ext _ _ (sub_zero _).symm rfl rfl rfl
@[simp, norm_cast] lemma coe_sub : ((x - y : R) : ℍ[R]) = x - y := quaternion_algebra.coe_sub x y

@[simp] lemma mul_re :
  (a * b).re = a.re * b.re - a.im_i * b.im_i - a.im_j * b.im_j - a.im_k * b.im_k :=
(quaternion_algebra.has_mul_mul_re a b).trans $
  by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_i :
  (a * b).im_i = a.re * b.im_i + a.im_i * b.re + a.im_j * b.im_k - a.im_k * b.im_j :=
(quaternion_algebra.has_mul_mul_im_i a b).trans $
  by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_j :
  (a * b).im_j = a.re * b.im_j - a.im_i * b.im_k + a.im_j * b.re + a.im_k * b.im_i :=
(quaternion_algebra.has_mul_mul_im_j a b).trans $
  by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp] lemma mul_im_k :
  (a * b).im_k = a.re * b.im_k + a.im_i * b.im_j - a.im_j * b.im_i + a.im_k * b.re :=
(quaternion_algebra.has_mul_mul_im_k a b).trans $
  by simp only [one_mul, neg_mul, sub_eq_add_neg, neg_neg]

@[simp, norm_cast] lemma coe_mul : ((x * y : R) : ℍ[R]) = x * y := quaternion_algebra.coe_mul x y

@[norm_cast, simp] lemma coe_pow (n : ℕ) : (↑(x ^ n) : ℍ[R]) = ↑x ^ n :=
quaternion_algebra.coe_pow x n

@[simp, norm_cast] lemma nat_cast_re (n : ℕ) : (n : ℍ[R]).re = n := rfl
@[simp, norm_cast] lemma nat_cast_im_i (n : ℕ) : (n : ℍ[R]).im_i = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im_j (n : ℕ) : (n : ℍ[R]).im_j = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im_k (n : ℕ) : (n : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma nat_cast_im (n : ℕ) : (n : ℍ[R]).im = 0 := rfl
@[norm_cast] lemma coe_nat_cast (n : ℕ) : ↑(n : R) = (n : ℍ[R]) := rfl

@[simp, norm_cast] lemma int_cast_re (z : ℤ) : (z : ℍ[R]).re = z := rfl
@[simp, norm_cast] lemma int_cast_im_i (z : ℤ) : (z : ℍ[R]).im_i = 0 := rfl
@[simp, norm_cast] lemma int_cast_im_j (z : ℤ) : (z : ℍ[R]).im_j = 0 := rfl
@[simp, norm_cast] lemma int_cast_im_k (z : ℤ) : (z : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma int_cast_im (z : ℤ) : (z : ℍ[R]).im = 0 := rfl
@[norm_cast] lemma coe_int_cast (z : ℤ) : ↑(z : R) = (z : ℍ[R]) := rfl

lemma coe_injective : function.injective (coe : R → ℍ[R]) := quaternion_algebra.coe_injective

@[simp] lemma coe_inj {x y : R} : (x : ℍ[R]) = y ↔ x = y := coe_injective.eq_iff

@[simp] lemma smul_re [has_smul S R] (s : S) : (s • a).re = s • a.re := rfl
@[simp] lemma smul_im_i [has_smul S R] (s : S) : (s • a).im_i = s • a.im_i := rfl
@[simp] lemma smul_im_j [has_smul S R] (s : S) : (s • a).im_j = s • a.im_j := rfl
@[simp] lemma smul_im_k [has_smul S R] (s : S) : (s • a).im_k = s • a.im_k := rfl
@[simp] lemma smul_im [smul_zero_class S R] (s : S) : (s • a).im = s • a.im :=
ext _ _ (smul_zero _).symm rfl rfl rfl

@[simp, norm_cast] lemma coe_smul [smul_zero_class S R] (s : S) (r : R) :
  (↑(s • r) : ℍ[R]) = s • ↑r :=
quaternion_algebra.coe_smul _ _

lemma coe_commutes : ↑r * a = a * r := quaternion_algebra.coe_commutes r a

lemma coe_commute : commute ↑r a := quaternion_algebra.coe_commute r a

lemma coe_mul_eq_smul : ↑r * a = r • a := quaternion_algebra.coe_mul_eq_smul r a

lemma mul_coe_eq_smul : a * r = r • a := quaternion_algebra.mul_coe_eq_smul r a

@[simp] lemma algebra_map_def : ⇑(algebra_map R ℍ[R]) = coe := rfl

lemma smul_coe : x • (y : ℍ[R]) = ↑(x * y) := quaternion_algebra.smul_coe x y

instance : module.finite R ℍ[R] := quaternion_algebra.module.finite _ _
instance : module.free R ℍ[R] := quaternion_algebra.module.free _ _

lemma dim_eq_four [strong_rank_condition R] : module.rank R ℍ[R] = 4 :=
quaternion_algebra.dim_eq_four _ _

lemma finrank_eq_four [strong_rank_condition R] : finite_dimensional.finrank R ℍ[R] = 4 :=
quaternion_algebra.finrank_eq_four _ _

/-- Quaternion conjugate. -/
def conj : ℍ[R] ≃ₗ[R]  ℍ[R] := quaternion_algebra.conj

@[simp] lemma conj_re : a.conj.re = a.re := rfl
@[simp] lemma conj_im_i : a.conj.im_i = - a.im_i := rfl
@[simp] lemma conj_im_j : a.conj.im_j = - a.im_j := rfl
@[simp] lemma conj_im_k : a.conj.im_k = - a.im_k := rfl
@[simp] lemma conj_im : a.conj.im = - a.im := a.im_conj

@[simp] lemma conj_conj : a.conj.conj = a := a.conj_conj

@[simp] lemma conj_add : (a + b).conj = a.conj + b.conj := a.conj_add b

@[simp] lemma conj_mul : (a * b).conj = b.conj * a.conj := a.conj_mul b

lemma conj_conj_mul : (a.conj * b).conj = b.conj * a := a.conj_conj_mul b

lemma conj_mul_conj : (a * b.conj).conj = b * a.conj := a.conj_mul_conj b

lemma self_add_conj' : a + a.conj = ↑(2 * a.re) := a.self_add_conj'

lemma self_add_conj : a + a.conj = 2 * a.re := a.self_add_conj

lemma conj_add_self' : a.conj + a = ↑(2 * a.re) := a.conj_add_self'

lemma conj_add_self : a.conj + a = 2 * a.re := a.conj_add_self

lemma conj_eq_two_re_sub : a.conj = ↑(2 * a.re) - a := a.conj_eq_two_re_sub

lemma commute_conj_self : commute a.conj a := a.commute_conj_self

lemma commute_self_conj : commute a a.conj := a.commute_self_conj

lemma commute_conj_conj {a b : ℍ[R]} (h : commute a b) : commute a.conj b.conj :=
quaternion_algebra.commute_conj_conj h

alias commute_conj_conj ← commute.quaternion_conj

@[simp, norm_cast] lemma conj_coe : conj (x : ℍ[R]) = x := quaternion_algebra.conj_coe x
@[simp] lemma im_conj : a.im.conj = - a.im := quaternion_algebra.im_conj _

@[simp, norm_cast] lemma conj_nat_cast (n : ℕ) : conj (n : ℍ[R]) = n :=
quaternion_algebra.conj_nat_cast _
@[simp, norm_cast] lemma conj_int_cast (z : ℤ) : conj (z : ℍ[R]) = z :=
quaternion_algebra.conj_int_cast _

@[simp] lemma conj_smul [monoid S] [distrib_mul_action S R] (s : S) (a : ℍ[R]) :
  conj (s • a) = s • conj a := quaternion_algebra.conj_smul _ _

@[simp] lemma conj_one : conj (1 : ℍ[R]) = 1 := conj_coe 1

lemma eq_re_of_eq_coe {a : ℍ[R]} {x : R} (h : a = x) : a = a.re :=
quaternion_algebra.eq_re_of_eq_coe h

lemma eq_re_iff_mem_range_coe {a : ℍ[R]} : a = a.re ↔ a ∈ set.range (coe : R → ℍ[R]) :=
quaternion_algebra.eq_re_iff_mem_range_coe

@[simp] lemma conj_fixed {R : Type*} [comm_ring R] [no_zero_divisors R] [char_zero R] {a : ℍ[R]} :
  conj a = a ↔ a = a.re :=
quaternion_algebra.conj_fixed

lemma conj_mul_eq_coe : conj a * a = (conj a * a).re := a.conj_mul_eq_coe

lemma mul_conj_eq_coe : a * conj a = (a * conj a).re := a.mul_conj_eq_coe

@[simp] lemma conj_zero : conj (0:ℍ[R]) = 0 := quaternion_algebra.conj_zero

@[simp] lemma conj_neg : (-a).conj = -a.conj := a.conj_neg

@[simp] lemma conj_sub : (a - b).conj = a.conj - b.conj := a.conj_sub b

@[simp] lemma conj_pow (n : ℕ) : conj (a ^ n) = conj a ^ n := a.conj_pow n

open mul_opposite

/-- Quaternion conjugate as an `alg_equiv` to the opposite ring. -/
def conj_ae : ℍ[R] ≃ₐ[R] (ℍ[R]ᵐᵒᵖ) := quaternion_algebra.conj_ae

@[simp] lemma coe_conj_ae : ⇑(conj_ae : ℍ[R] ≃ₐ[R] ℍ[R]ᵐᵒᵖ) = op ∘ conj := rfl

/-- Square of the norm. -/
def norm_sq : ℍ[R] →*₀ R :=
{ to_fun := λ a, (a * a.conj).re,
  map_zero' := by rw [conj_zero, zero_mul, zero_re],
  map_one' := by rw [conj_one, one_mul, one_re],
  map_mul' := λ x y, coe_injective $ by conv_lhs { rw [← mul_conj_eq_coe, conj_mul, mul_assoc,
    ← mul_assoc y, y.mul_conj_eq_coe, coe_commutes, ← mul_assoc, x.mul_conj_eq_coe, ← coe_mul] } }

lemma norm_sq_def : norm_sq a = (a * a.conj).re := rfl

lemma norm_sq_def' : norm_sq a = a.1^2 + a.2^2 + a.3^2 + a.4^2 :=
by simp only [norm_sq_def, sq, mul_neg, sub_neg_eq_add,
  mul_re, conj_re, conj_im_i, conj_im_j, conj_im_k]

lemma norm_sq_coe : norm_sq (x : ℍ[R]) = x^2 :=
by rw [norm_sq_def, conj_coe, ← coe_mul, coe_re, sq]

@[simp] lemma norm_sq_conj : norm_sq (conj a) = norm_sq a := by simp [norm_sq_def']

@[norm_cast] lemma norm_sq_nat_cast (n : ℕ) : norm_sq (n : ℍ[R]) = n^2 :=
by rw [←coe_nat_cast, norm_sq_coe]

@[norm_cast] lemma norm_sq_int_cast (z : ℤ) : norm_sq (z : ℍ[R]) = z^2 :=
by rw [←coe_int_cast, norm_sq_coe]

@[simp] lemma norm_sq_neg : norm_sq (-a) = norm_sq a :=
by simp only [norm_sq_def, conj_neg, neg_mul_neg]

lemma self_mul_conj : a * a.conj = norm_sq a := by rw [mul_conj_eq_coe, norm_sq_def]

lemma conj_mul_self : a.conj * a = norm_sq a := by rw [← a.commute_self_conj.eq, self_mul_conj]

lemma im_sq : a.im^2 = -norm_sq a.im :=
by simp_rw [sq, ←conj_mul_self, im_conj, neg_mul, neg_neg]

lemma coe_norm_sq_add :
  (norm_sq (a + b) : ℍ[R]) = norm_sq a + a * b.conj + b * a.conj + norm_sq b :=
by simp [← self_mul_conj, mul_add, add_mul, add_assoc]

end quaternion

namespace quaternion

variables {R : Type*}

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring R] {a : ℍ[R]}

@[simp] lemma norm_sq_eq_zero : norm_sq a = 0 ↔ a = 0 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ norm_sq.map_zero⟩,
  rw [norm_sq_def', add_eq_zero_iff', add_eq_zero_iff', add_eq_zero_iff'] at h,
  exact ext a 0 (pow_eq_zero h.1.1.1) (pow_eq_zero h.1.1.2) (pow_eq_zero h.1.2) (pow_eq_zero h.2),
  all_goals { apply_rules [sq_nonneg, add_nonneg] }
end

lemma norm_sq_ne_zero : norm_sq a ≠ 0 ↔ a ≠ 0 := not_congr norm_sq_eq_zero

@[simp] lemma norm_sq_nonneg : 0 ≤ norm_sq a :=
by { rw norm_sq_def', apply_rules [sq_nonneg, add_nonneg] }

@[simp] lemma norm_sq_le_zero : norm_sq a ≤ 0 ↔ a = 0 :=
by simpa only [le_antisymm_iff, norm_sq_nonneg, and_true] using @norm_sq_eq_zero _ _ a

instance : nontrivial ℍ[R] :=
{ exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩, }

instance : no_zero_divisors ℍ[R] :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b hab,
    have norm_sq a * norm_sq b = 0, by rwa [← norm_sq.map_mul, norm_sq_eq_zero],
    (eq_zero_or_eq_zero_of_mul_eq_zero this).imp norm_sq_eq_zero.1 norm_sq_eq_zero.1,
  ..quaternion.nontrivial, }

instance : is_domain ℍ[R] :=
no_zero_divisors.to_is_domain _

end linear_ordered_comm_ring

section field

variables [linear_ordered_field R] (a b : ℍ[R])

@[simps { attrs := [] }] instance : has_inv ℍ[R] := ⟨λ a, (norm_sq a)⁻¹ • a.conj⟩

instance : group_with_zero ℍ[R] :=
{ inv := has_inv.inv,
  inv_zero := by rw [has_inv_inv, conj_zero, smul_zero],
  mul_inv_cancel := λ a ha, by rw [has_inv_inv, algebra.mul_smul_comm, self_mul_conj, smul_coe,
    inv_mul_cancel (norm_sq_ne_zero.2 ha), coe_one],
  .. quaternion.nontrivial,
  .. (by apply_instance : monoid_with_zero ℍ[R]) }

@[norm_cast, simp] lemma coe_inv (x : R) : ((x⁻¹ : R) : ℍ[R]) = x⁻¹ :=
map_inv₀ (algebra_map R ℍ[R]) _

@[norm_cast, simp] lemma coe_div (x y : R) : ((x / y : R) : ℍ[R]) = x / y :=
map_div₀ (algebra_map R ℍ[R]) x y

@[norm_cast, simp] lemma coe_zpow (x : R) (z : ℤ) : ((x ^ z : R) : ℍ[R]) = x ^ z :=
map_zpow₀ (algebra_map R ℍ[R]) x z

instance : division_ring ℍ[R] :=
{ rat_cast := λ q, ↑(q : R),
  rat_cast_mk := λ n d hd h, by rw [rat.cast_mk', coe_mul, coe_int_cast, coe_inv, coe_nat_cast],
  qsmul := (•),
  qsmul_eq_mul' := λ q x, begin
    rw coe_mul_eq_smul,
    ext; exact division_ring.qsmul_eq_mul' _ _,
  end,
  .. quaternion.group_with_zero,
  .. quaternion.ring }

@[simp, norm_cast] lemma rat_cast_re (q : ℚ) : (q : ℍ[R]).re = q := rfl
@[simp, norm_cast] lemma rat_cast_im_i (q : ℚ) : (q : ℍ[R]).im_i = 0 := rfl
@[simp, norm_cast] lemma rat_cast_im_j (q : ℚ) : (q : ℍ[R]).im_j = 0 := rfl
@[simp, norm_cast] lemma rat_cast_im_k (q : ℚ) : (q : ℍ[R]).im_k = 0 := rfl
@[simp, norm_cast] lemma rat_cast_im (q : ℚ) : (q : ℍ[R]).im = 0 := rfl
@[norm_cast] lemma coe_rat_cast (q : ℚ) : ↑(q : R) = (q : ℍ[R]) := rfl

lemma conj_inv : conj (a⁻¹) = (conj a)⁻¹ := star_inv' a
lemma conj_zpow (z : ℤ) : conj (a ^ z) = conj a ^ z := star_zpow₀ a z
@[simp, norm_cast] lemma conj_rat_cast (q : ℚ) : conj (q : ℍ[R]) = q := @star_rat_cast ℍ[R] _ _ q

@[simp] lemma norm_sq_inv : norm_sq a⁻¹ = (norm_sq a)⁻¹ := map_inv₀ norm_sq _
@[simp] lemma norm_sq_div : norm_sq (a / b) = norm_sq a / norm_sq b := map_div₀ norm_sq a b
@[simp] lemma norm_sq_zpow (z : ℤ) : norm_sq (a ^ z) = norm_sq a ^ z := map_zpow₀ norm_sq a z
@[norm_cast] lemma norm_sq_rat_cast (q : ℚ) : norm_sq (q : ℍ[R]) = q^2 :=
by rw [←coe_rat_cast, norm_sq_coe]

end field

end quaternion

namespace cardinal

open_locale cardinal quaternion

section quaternion_algebra

variables {R : Type*} (c₁ c₂ : R)

private theorem pow_four [infinite R] : #R ^ 4 = #R :=
power_nat_eq (aleph_0_le_mk R) $ by simp

/-- The cardinality of a quaternion algebra, as a type. -/
lemma mk_quaternion_algebra : #ℍ[R, c₁, c₂] = #R ^ 4 :=
by { rw mk_congr (quaternion_algebra.equiv_prod c₁ c₂), simp only [mk_prod, lift_id], ring }

@[simp] lemma mk_quaternion_algebra_of_infinite [infinite R] : #ℍ[R, c₁, c₂] = #R :=
by rw [mk_quaternion_algebra, pow_four]

/-- The cardinality of a quaternion algebra, as a set. -/
lemma mk_univ_quaternion_algebra : #(set.univ : set ℍ[R, c₁, c₂]) = #R ^ 4 :=
by rw [mk_univ, mk_quaternion_algebra]

@[simp] lemma mk_univ_quaternion_algebra_of_infinite [infinite R] :
  #(set.univ : set ℍ[R, c₁, c₂]) = #R :=
by rw [mk_univ_quaternion_algebra, pow_four]

end quaternion_algebra

section quaternion

variables (R : Type*) [has_one R] [has_neg R]

/-- The cardinality of the quaternions, as a type. -/
@[simp] lemma mk_quaternion : #ℍ[R] = #R ^ 4 :=
mk_quaternion_algebra _ _

@[simp] lemma mk_quaternion_of_infinite [infinite R] : #ℍ[R] = #R :=
by rw [mk_quaternion, pow_four]

/-- The cardinality of the quaternions, as a set. -/
@[simp] lemma mk_univ_quaternion : #(set.univ : set ℍ[R]) = #R ^ 4 :=
mk_univ_quaternion_algebra _ _

@[simp] lemma mk_univ_quaternion_of_infinite [infinite R] : #(set.univ : set ℍ[R]) = #R :=
by rw [mk_univ_quaternion, pow_four]

end quaternion

end cardinal
