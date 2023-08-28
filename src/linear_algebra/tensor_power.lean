/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import linear_algebra.pi_tensor_product
import logic.equiv.fin
import algebra.direct_sum.algebra

/-!
# Tensor power of a semimodule over a commutative semirings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `fin n` of `M`,
`⨂[R] (i : fin n), M`. This is a special case of `pi_tensor_product`.

This file introduces the notation `⨂[R]^n M` for `tensor_power R n M`, which in turn is an
abbreviation for `⨂[R] i : fin n, M`.

## Main definitions:

* `tensor_power.gsemiring`: the tensor powers form a graded semiring.
* `tensor_power.galgebra`: the tensor powers form a graded algebra.

## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `graded_monoid` should be preferred.
-/

open_locale tensor_product

/-- Homogenous tensor powers $M^{\otimes n}$. `⨂[R]^n M` is a shorthand for
`⨂[R] (i : fin n), M`. -/
@[reducible] protected def tensor_power (R : Type*) (n : ℕ) (M : Type*)
  [comm_semiring R] [add_comm_monoid M] [module R M] : Type* :=
⨂[R] i : fin n, M

variables {R : Type*} {M : Type*} [comm_semiring R] [add_comm_monoid M] [module R M]

localized "notation (name := tensor_power)
  `⨂[`:100 R `]^`:80 n:max := tensor_power R n" in tensor_product

namespace pi_tensor_product

/-- Two dependent pairs of tensor products are equal if their index is equal and the contents
are equal after a canonical reindexing. -/
@[ext]
lemma graded_monoid_eq_of_reindex_cast {ιι : Type*} {ι : ιι → Type*} :
  ∀ {a b : graded_monoid (λ ii, ⨂[R] i : ι ii, M)} (h : a.fst = b.fst),
    reindex R M (equiv.cast $ congr_arg ι h) a.snd = b.snd → a = b
| ⟨ai, a⟩ ⟨bi, b⟩ := λ (hi : ai = bi) (h : reindex R M _ a = b),
begin
  subst hi,
  simpa using h,
end

end pi_tensor_product

namespace tensor_power
open_locale tensor_product direct_sum
open pi_tensor_product

/-- As a graded monoid, `⨂[R]^i M` has a `1 : ⨂[R]^0 M`. -/
instance ghas_one : graded_monoid.ghas_one (λ i, ⨂[R]^i M) :=
{ one := tprod R $ @fin.elim0' M }

local notation `ₜ1` := @graded_monoid.ghas_one.one ℕ (λ i, ⨂[R]^i M) _ _

lemma ghas_one_def : ₜ1 = tprod R (@fin.elim0' M) := rfl

/-- A variant of `pi_tensor_prod.tmul_equiv` with the result indexed by `fin (n + m)`. -/
def mul_equiv {n m : ℕ} : (⨂[R]^n M) ⊗[R] (⨂[R]^m M) ≃ₗ[R] ⨂[R]^(n + m) M :=
(tmul_equiv R M).trans (reindex R M fin_sum_fin_equiv)

/-- As a graded monoid, `⨂[R]^i M` has a `(*) : ⨂[R]^i M → ⨂[R]^j M → ⨂[R]^(i + j) M`. -/
instance ghas_mul : graded_monoid.ghas_mul (λ i, ⨂[R]^i M) :=
{ mul := λ i j a b, (tensor_product.mk R _ _).compr₂ ↑(mul_equiv : _ ≃ₗ[R] ⨂[R]^(i + j) M) a b}

local infix ` ₜ* `:70 := @graded_monoid.ghas_mul.mul ℕ (λ i, ⨂[R]^i M) _ _ _ _

lemma ghas_mul_def {i j} (a : ⨂[R]^i M) (b : ⨂[R]^j M) : a ₜ* b = mul_equiv (a ⊗ₜ b) := rfl

lemma ghas_mul_eq_coe_linear_map {i j} (a : ⨂[R]^i M) (b : ⨂[R]^j M) :
  a ₜ* b =
    ((tensor_product.mk R _ _).compr₂ ↑(mul_equiv : _ ≃ₗ[R] ⨂[R]^(i + j) M)
      : ⨂[R]^i M →ₗ[R] ⨂[R]^j M →ₗ[R] ⨂[R]^(i + j) M) a b := rfl

variables (R M)

/-- Cast between "equal" tensor powers. -/
def cast {i j} (h : i = j) : ⨂[R]^i M ≃ₗ[R] (⨂[R]^j M) :=
reindex R M (fin.cast h).to_equiv

lemma cast_tprod {i j} (h : i = j) (a : fin i → M) :
  cast R M h (tprod R a) = tprod R (a ∘ fin.cast h.symm) :=
reindex_tprod _ _

@[simp] lemma cast_refl {i} (h : i = i) : cast R M h = linear_equiv.refl _ _ :=
(congr_arg (λ f, reindex R M (rel_iso.to_equiv f)) $ fin.cast_refl h).trans reindex_refl

@[simp] lemma cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm := reindex_symm _

@[simp] lemma cast_trans {i j k} (h : i = j) (h' : j = k) :
  (cast R M h).trans (cast R M h') = cast R M (h.trans h') := reindex_trans _ _

variables {R M}

@[simp] lemma cast_cast {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M) :
  cast R M h' (cast R M h a) = cast R M (h.trans h') a := reindex_reindex _ _ _

@[ext]
lemma graded_monoid_eq_of_cast {a b : graded_monoid (λ n, ⨂[R] i : fin n, M)}
  (h : a.fst = b.fst) (h2 : cast R M h a.snd = b.snd) : a = b :=
begin
  refine graded_monoid_eq_of_reindex_cast h _,
  rw cast at h2,
  rw [←fin.cast_to_equiv, ← h2],
end

-- named to match `fin.cast_eq_cast`
lemma cast_eq_cast {i j} (h : i = j) : ⇑(cast R M h) = _root_.cast (congr_arg _ h) :=
begin
  subst h,
  rw [cast_refl],
  refl,
end

variables (R)
include R
lemma tprod_mul_tprod {na nb} (a : fin na → M) (b : fin nb → M) :
  tprod R a ₜ* tprod R b = tprod R (fin.append a b) :=
begin
  dsimp [ghas_mul_def, mul_equiv],
  rw [tmul_equiv_apply R M a b],
  refine (reindex_tprod _ _).trans _,
  congr' 1,
  dsimp only [fin.append, fin_sum_fin_equiv, equiv.coe_fn_symm_mk],
  apply funext,
  apply fin.add_cases; simp,
end
omit R
variables {R}

lemma one_mul {n} (a : ⨂[R]^n M) :
  cast R M (zero_add n) (ₜ1 ₜ* a) = a :=
begin
  rw [ghas_mul_def, ghas_one_def],
  induction a using pi_tensor_product.induction_on with r a x y hx hy,
  { dsimp only at a,
    rw [tensor_product.tmul_smul, linear_equiv.map_smul, linear_equiv.map_smul, ←ghas_mul_def,
      tprod_mul_tprod, cast_tprod],
    congr' 2 with i,
    rw fin.elim0'_append,
    refine congr_arg a (fin.ext _),
    simp },
  { rw [tensor_product.tmul_add, map_add, map_add, hx, hy], },
end

lemma mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a :=
begin
  rw [ghas_mul_def, ghas_one_def],
  induction a using pi_tensor_product.induction_on with r a x y hx hy,
  { dsimp only at a,
    rw [←tensor_product.smul_tmul', linear_equiv.map_smul, linear_equiv.map_smul, ←ghas_mul_def,
      tprod_mul_tprod R a _, cast_tprod],
    congr' 2 with i,
    rw fin.append_elim0',
    refine congr_arg a (fin.ext _),
    simp },
  { rw [tensor_product.add_tmul, map_add, map_add, hx, hy], },
end

lemma mul_assoc {na nb nc} (a : ⨂[R]^na M) (b : ⨂[R]^nb M) (c : ⨂[R]^nc M) :
  cast R M (add_assoc _ _ _) ((a ₜ* b) ₜ* c) = a ₜ* (b  ₜ* c) :=
begin
  let mul : Π (n m : ℕ), (⨂[R]^n M) →ₗ[R] (⨂[R]^m M) →ₗ[R] ⨂[R]^(n + m) M :=
    (λ n m, (tensor_product.mk R _ _).compr₂ ↑(mul_equiv : _ ≃ₗ[R] ⨂[R]^(n + m) M)),
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : ⨂[R]^(na + nb + nc) M ≃ₗ[R] ⨂[R]^(na + (nb + nc)) M := cast R M (add_assoc _ _ _),
  let lhs : (⨂[R]^na M) →ₗ[R] (⨂[R]^nb M) →ₗ[R] (⨂[R]^nc M) →ₗ[R] (⨂[R]^(na + (nb + nc)) M) :=
    (linear_map.llcomp R _ _ _ ((mul _ nc).compr₂ e.to_linear_map)).comp
      (mul na nb),
  have lhs_eq : ∀ a b c, lhs a b c = e ((a ₜ* b) ₜ* c) := λ _ _ _, rfl,
  let rhs : (⨂[R]^na M) →ₗ[R] (⨂[R]^nb M) →ₗ[R] (⨂[R]^nc M) →ₗ[R] (⨂[R]^(na + (nb + nc)) M) :=
    (linear_map.llcomp R _ _ _ (linear_map.lflip R _ _ _) $
      (linear_map.llcomp R _ _ _ (mul na _).flip).comp (mul nb nc)).flip,
  have rhs_eq : ∀ a b c, rhs a b c = (a ₜ* (b ₜ* c)) := λ _ _ _, rfl,
  suffices : lhs = rhs,
  from linear_map.congr_fun (linear_map.congr_fun (linear_map.congr_fun this a) b) c,
  ext a b c,
  -- clean up
  simp only [linear_map.comp_multilinear_map_apply, lhs_eq, rhs_eq, tprod_mul_tprod, e,
    cast_tprod],
  congr' with j,
  rw fin.append_assoc,
  refine congr_arg (fin.append a (fin.append b c)) (fin.ext _),
  rw [fin.coe_cast, fin.coe_cast],
end

-- for now we just use the default for the `gnpow` field as it's easier.
instance gmonoid : graded_monoid.gmonoid (λ i, ⨂[R]^i M) :=
{ one_mul := λ a, graded_monoid_eq_of_cast (zero_add _) (one_mul _),
  mul_one := λ a, graded_monoid_eq_of_cast (add_zero _) (mul_one _),
  mul_assoc := λ a b c, graded_monoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _),
  ..tensor_power.ghas_mul,
  ..tensor_power.ghas_one, }

/-- The canonical map from `R` to `⨂[R]^0 M` corresponding to the algebra_map of the tensor
algebra. -/
def algebra_map₀ : R ≃ₗ[R] ⨂[R]^0 M :=
linear_equiv.symm $ is_empty_equiv (fin 0)

lemma algebra_map₀_eq_smul_one (r : R) :
  (algebra_map₀ r : ⨂[R]^0 M) = r • ₜ1 :=
by { simp [algebra_map₀], congr }

lemma algebra_map₀_one : (algebra_map₀ 1 : ⨂[R]^0 M) = ₜ1 :=
(algebra_map₀_eq_smul_one 1).trans (one_smul _ _)

lemma algebra_map₀_mul {n} (r : R) (a : ⨂[R]^n M) :
  cast R M (zero_add _) (algebra_map₀ r ₜ* a) = r • a :=
by rw [ghas_mul_eq_coe_linear_map, algebra_map₀_eq_smul_one, linear_map.map_smul₂,
  linear_equiv.map_smul,  ←ghas_mul_eq_coe_linear_map, one_mul]

lemma mul_algebra_map₀ {n} (r : R) (a : ⨂[R]^n M) :
  cast R M (add_zero _) (a ₜ* algebra_map₀ r) = r • a :=
by rw [ghas_mul_eq_coe_linear_map, algebra_map₀_eq_smul_one, linear_map.map_smul,
  linear_equiv.map_smul, ←ghas_mul_eq_coe_linear_map, mul_one]

lemma algebra_map₀_mul_algebra_map₀ (r s : R) :
  cast R M (add_zero _) (algebra_map₀ r ₜ* algebra_map₀ s) = algebra_map₀ (r * s) :=
begin
  rw [←smul_eq_mul, linear_equiv.map_smul],
  exact algebra_map₀_mul r (@algebra_map₀ R M _ _ _ s),
end

instance gsemiring : direct_sum.gsemiring (λ i, ⨂[R]^i M) :=
{ mul_zero := λ i j a, linear_map.map_zero _,
  zero_mul := λ i j b, linear_map.map_zero₂ _ _,
  mul_add := λ i j a b₁ b₂, linear_map.map_add _ _ _,
  add_mul := λ i j a₁ a₂ b, linear_map.map_add₂ _ _ _ _,
  nat_cast := λ n, algebra_map₀ (n : R),
  nat_cast_zero := by rw [nat.cast_zero, map_zero],
  nat_cast_succ := λ n, by rw [nat.cast_succ, map_add, algebra_map₀_one],
  ..tensor_power.gmonoid }

example : semiring (⨁ n : ℕ, ⨂[R]^n M) := by apply_instance

/-- The tensor powers form a graded algebra.

Note that this instance implies `algebra R (⨁ n : ℕ, ⨂[R]^n M)` via `direct_sum.algebra`. -/
instance galgebra : direct_sum.galgebra R (λ i, ⨂[R]^i M) :=
{ to_fun := (algebra_map₀ : R ≃ₗ[R] ⨂[R]^0 M).to_linear_map.to_add_monoid_hom,
  map_one := algebra_map₀_one,
  map_mul := λ r s, graded_monoid_eq_of_cast rfl begin
    rw [←linear_equiv.eq_symm_apply],
    have := algebra_map₀_mul_algebra_map₀ r s,
    exact this.symm,
  end,
  commutes := λ r x, graded_monoid_eq_of_cast (add_comm _ _) begin
    have := (algebra_map₀_mul r x.snd).trans (mul_algebra_map₀ r x.snd).symm,
    rw [←linear_equiv.eq_symm_apply, cast_symm],
    rw [←linear_equiv.eq_symm_apply, cast_symm, cast_cast] at this,
    exact this,
  end,
  smul_def := λ r x, graded_monoid_eq_of_cast (zero_add x.fst).symm begin
    rw [←linear_equiv.eq_symm_apply, cast_symm],
    exact (algebra_map₀_mul r x.snd).symm,
  end }

lemma galgebra_to_fun_def (r : R) :
  @direct_sum.galgebra.to_fun ℕ R (λ i, ⨂[R]^i M) _ _ _ _ _ _ _ r = algebra_map₀ r := rfl

example : algebra R (⨁ n : ℕ, ⨂[R]^n M) := by apply_instance

end tensor_power
