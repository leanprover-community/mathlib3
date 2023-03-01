/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import group_theory.subgroup.actions
import linear_algebra.linear_independent

/-!
# Rays in modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines rays in modules.

## Main definitions

* `same_ray`: two vectors belong to the same ray if they are proportional with a nonnegative
  coefficient.

* `module.ray` is a type for the equivalence class of nonzero vectors in a module with some
common positive multiple.
-/

noncomputable theory

open_locale big_operators

section strict_ordered_comm_semiring

variables (R : Type*) [strict_ordered_comm_semiring R]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
variables (ι : Type*) [decidable_eq ι]

/-- Two vectors are in the same ray if either one of them is zero or some positive multiples of them
are equal (in the typical case over a field, this means one of them is a nonnegative multiple of
the other). -/
def same_ray (v₁ v₂ : M) : Prop :=
v₁ = 0 ∨ v₂ = 0 ∨ ∃ (r₁ r₂ : R), 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

variables {R}

namespace same_ray

variables {x y z : M}

@[simp] lemma zero_left (y : M) : same_ray R 0 y := or.inl rfl

@[simp] lemma zero_right (x : M) : same_ray R x 0 := or.inr $ or.inl rfl

@[nontriviality] lemma of_subsingleton [subsingleton M] (x y : M) : same_ray R x y :=
by { rw [subsingleton.elim x 0], exact zero_left _ }

@[nontriviality] lemma of_subsingleton' [subsingleton R] (x y : M) : same_ray R x y :=
by { haveI := module.subsingleton R M, exact of_subsingleton x y }

/-- `same_ray` is reflexive. -/
@[refl] lemma refl (x : M) : same_ray R x x :=
begin
  nontriviality R,
  exact or.inr (or.inr $ ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩)
end

protected lemma rfl : same_ray R x x := refl _

/-- `same_ray` is symmetric. -/
@[symm] lemma symm (h : same_ray R x y) : same_ray R y x :=
(or.left_comm.1 h).imp_right $ or.imp_right $ λ ⟨r₁, r₂, h₁, h₂, h⟩, ⟨r₂, r₁, h₂, h₁, h.symm⟩

/-- If `x` and `y` are nonzero vectors on the same ray, then there exist positive numbers `r₁ r₂`
such that `r₁ • x = r₂ • y`. -/
lemma exists_pos (h : same_ray R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
  ∃ r₁ r₂ : R, 0 < r₁ ∧ 0 < r₂ ∧ r₁ • x = r₂ • y :=
(h.resolve_left hx).resolve_left hy

lemma _root_.same_ray_comm : same_ray R x y ↔ same_ray R y x :=
⟨same_ray.symm, same_ray.symm⟩

/-- `same_ray` is transitive unless the vector in the middle is zero and both other vectors are
nonzero. -/
lemma trans (hxy : same_ray R x y) (hyz : same_ray R y z) (hy : y = 0 → x = 0 ∨ z = 0) :
  same_ray R x z :=
begin
  rcases eq_or_ne x 0 with rfl|hx, { exact zero_left z },
  rcases eq_or_ne z 0 with rfl|hz, { exact zero_right x },
  rcases eq_or_ne y 0 with rfl|hy, { exact (hy rfl).elim (λ h, (hx h).elim) (λ h, (hz h).elim) },
  rcases hxy.exists_pos hx hy with ⟨r₁, r₂, hr₁, hr₂, h₁⟩,
  rcases hyz.exists_pos hy hz with ⟨r₃, r₄, hr₃, hr₄, h₂⟩,
  refine or.inr (or.inr $ ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄, _⟩),
  rw [mul_smul, mul_smul, h₁, ← h₂, smul_comm]
end

/-- A vector is in the same ray as a nonnegative multiple of itself. -/
lemma _root_.same_ray_nonneg_smul_right (v : M) {r : R} (h : 0 ≤ r) : same_ray R v (r • v) :=
or.inr $ h.eq_or_lt.imp (λ h, h ▸ zero_smul R v) $
  λ h, ⟨r, 1, h, by { nontriviality R, exact zero_lt_one }, (one_smul _ _).symm⟩

/-- A vector is in the same ray as a positive multiple of itself. -/
lemma _root_.same_ray_pos_smul_right (v : M) {r : R} (h : 0 < r) : same_ray R v (r • v) :=
same_ray_nonneg_smul_right v h.le

/-- A vector is in the same ray as a nonnegative multiple of one it is in the same ray as. -/
lemma nonneg_smul_right {r : R} (h : same_ray R x y) (hr : 0 ≤ r) : same_ray R x (r • y) :=
h.trans (same_ray_nonneg_smul_right y hr) $ λ hy, or.inr $ by rw [hy, smul_zero]

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
lemma pos_smul_right {r : R} (h : same_ray R x y) (hr : 0 < r) : same_ray R x (r • y) :=
h.nonneg_smul_right hr.le

/-- A nonnegative multiple of a vector is in the same ray as that vector. -/
lemma _root_.same_ray_nonneg_smul_left (v : M) {r : R} (h : 0 ≤ r) : same_ray R (r • v) v :=
(same_ray_nonneg_smul_right v h).symm

/-- A positive multiple of a vector is in the same ray as that vector. -/
lemma _root_.same_ray_pos_smul_left (v : M) {r : R} (h : 0 < r) : same_ray R (r • v) v :=
same_ray_nonneg_smul_left v h.le

/-- A nonnegative multiple of a vector is in the same ray as one it is in the same ray as. -/
lemma nonneg_smul_left {r : R} (h : same_ray R x y) (hr : 0 ≤ r) : same_ray R (r • x) y :=
(h.symm.nonneg_smul_right hr).symm

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
lemma pos_smul_left {r : R} (h : same_ray R x y) (hr : 0 < r) : same_ray R (r • x) y :=
h.nonneg_smul_left hr.le

/-- If two vectors are on the same ray then they remain so after applying a linear map. -/
lemma map (f : M →ₗ[R] N) (h : same_ray R x y) : same_ray R (f x) (f y) :=
h.imp (λ hx, by rw [hx, map_zero]) $ or.imp (λ hy, by rw [hy, map_zero]) $
  λ ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₁, r₂, hr₁, hr₂, by rw [←f.map_smul, ←f.map_smul, h]⟩

/-- The images of two vectors under an injective linear map are on the same ray if and only if the
original vectors are on the same ray. -/
lemma _root_.function.injective.same_ray_map_iff {F : Type*} [linear_map_class F R M N] {f : F}
  (hf : function.injective f) : same_ray R (f x) (f y) ↔ same_ray R x y :=
by simp only [same_ray, map_zero, ← hf.eq_iff, map_smul]

/-- The images of two vectors under a linear equivalence are on the same ray if and only if the
original vectors are on the same ray. -/
@[simp] lemma _root_.same_ray_map_iff (e : M ≃ₗ[R] N) : same_ray R (e x) (e y) ↔ same_ray R x y :=
function.injective.same_ray_map_iff (equiv_like.injective e)

/-- If two vectors are on the same ray then both scaled by the same action are also on the same
ray. -/
lemma smul {S : Type*} [monoid S] [distrib_mul_action S M] [smul_comm_class R S M]
  (h : same_ray R x y) (s : S) : same_ray R (s • x) (s • y) :=
h.map (s • (linear_map.id : M →ₗ[R] M))

/-- If `x` and `y` are on the same ray as `z`, then so is `x + y`. -/
lemma add_left (hx : same_ray R x z) (hy : same_ray R y z) : same_ray R (x + y) z :=
begin
  rcases eq_or_ne x 0 with rfl|hx₀, { rwa zero_add },
  rcases eq_or_ne y 0 with rfl|hy₀, { rwa add_zero },
  rcases eq_or_ne z 0 with rfl|hz₀, { apply zero_right },
  rcases hx.exists_pos hx₀ hz₀ with ⟨rx, rz₁, hrx, hrz₁, Hx⟩,
  rcases hy.exists_pos hy₀ hz₀ with ⟨ry, rz₂, hry, hrz₂, Hy⟩,
  refine or.inr (or.inr ⟨rx * ry, ry * rz₁ + rx * rz₂, mul_pos hrx hry, _, _⟩),
  { apply_rules [add_pos, mul_pos] },
  { simp only [mul_smul, smul_add, add_smul, ← Hx, ← Hy],
    rw smul_comm }
end

/-- If `y` and `z` are on the same ray as `x`, then so is `y + z`. -/
lemma add_right (hy : same_ray R x y) (hz : same_ray R x z) : same_ray R x (y + z) :=
(hy.symm.add_left hz.symm).symm

end same_ray

/-- Nonzero vectors, as used to define rays. This type depends on an unused argument `R` so that
`ray_vector.setoid` can be an instance. -/
@[nolint unused_arguments has_nonempty_instance]
def ray_vector (R M : Type*) [has_zero M] := {v : M // v ≠ 0}

instance ray_vector.has_coe {R M : Type*} [has_zero M] :
  has_coe (ray_vector R M) M := coe_subtype

instance {R M : Type*} [has_zero M] [nontrivial M] : nonempty (ray_vector R M) :=
let ⟨x, hx⟩ := exists_ne (0 : M) in ⟨⟨x, hx⟩⟩

variables (R M)

/-- The setoid of the `same_ray` relation for the subtype of nonzero vectors. -/
instance : setoid (ray_vector R M) :=
{ r := λ x y, same_ray R (x : M) y,
  iseqv := ⟨λ x, same_ray.refl _, λ x y h, h.symm,
    λ x y z hxy hyz, hxy.trans hyz $ λ hy, (y.2 hy).elim⟩ }

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
@[nolint has_nonempty_instance]
def module.ray := quotient (ray_vector.setoid R M)

variables {R M}

/-- Equivalence of nonzero vectors, in terms of same_ray. -/
lemma equiv_iff_same_ray {v₁ v₂ : ray_vector R M} :
  v₁ ≈ v₂ ↔ same_ray R (v₁ : M) v₂ :=
iff.rfl

variables (R)

/-- The ray given by a nonzero vector. -/
protected def ray_of_ne_zero (v : M) (h : v ≠ 0) : module.ray R M := ⟦⟨v, h⟩⟧

/-- An induction principle for `module.ray`, used as `induction x using module.ray.ind`. -/
lemma module.ray.ind {C : module.ray R M → Prop}
  (h : ∀ v (hv : v ≠ 0), C (ray_of_ne_zero R v hv)) (x : module.ray R M) : C x :=
quotient.ind (subtype.rec $ by exact h) x

variable {R}

instance [nontrivial M] : nonempty (module.ray R M) :=
nonempty.map quotient.mk infer_instance

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `same_ray`. -/
lemma ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
  ray_of_ne_zero R _ hv₁ = ray_of_ne_zero R _ hv₂ ↔ same_ray R v₁ v₂ :=
quotient.eq

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp] lemma ray_pos_smul {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r)
  (hrv : r • v ≠ 0) : ray_of_ne_zero R (r • v) hrv = ray_of_ne_zero R v h :=
(ray_eq_iff _ _).2 $ same_ray_pos_smul_left v hr

/-- An equivalence between modules implies an equivalence between ray vectors. -/
def ray_vector.map_linear_equiv (e : M ≃ₗ[R] N) : ray_vector R M ≃ ray_vector R N :=
equiv.subtype_equiv e.to_equiv $ λ _, e.map_ne_zero_iff.symm

/-- An equivalence between modules implies an equivalence between rays. -/
def module.ray.map (e : M ≃ₗ[R] N) : module.ray R M ≃ module.ray R N :=
quotient.congr (ray_vector.map_linear_equiv e) $ λ ⟨a, ha⟩ ⟨b, hb⟩, (same_ray_map_iff _).symm

@[simp] lemma module.ray.map_apply (e : M ≃ₗ[R] N) (v : M) (hv : v ≠ 0) :
  module.ray.map e (ray_of_ne_zero _ v hv) = ray_of_ne_zero _ (e v) (e.map_ne_zero_iff.2 hv) := rfl

@[simp] lemma module.ray.map_refl : (module.ray.map $ linear_equiv.refl R M) = equiv.refl _ :=
equiv.ext $ module.ray.ind R $ λ _ _, rfl

@[simp] lemma module.ray.map_symm (e : M ≃ₗ[R] N) :
  (module.ray.map e).symm = module.ray.map e.symm := rfl

section action
variables {G : Type*} [group G] [distrib_mul_action G M]

/-- Any invertible action preserves the non-zeroness of ray vectors. This is primarily of interest
when `G = Rˣ` -/
instance {R : Type*} : mul_action G (ray_vector R M) :=
{ smul := λ r, (subtype.map ((•) r) $ λ a, (smul_ne_zero_iff_ne _).2),
  mul_smul := λ a b m, subtype.ext $ mul_smul a b _,
  one_smul := λ m, subtype.ext $ one_smul _ _ }

variables [smul_comm_class R G M]

/-- Any invertible action preserves the non-zeroness of rays. This is primarily of interest when
`G = Rˣ` -/
instance : mul_action G (module.ray R M) :=
{ smul := λ r, quotient.map ((•) r) (λ a b h, h.smul _),
  mul_smul := λ a b, quotient.ind $ by exact(λ m, congr_arg quotient.mk $ mul_smul a b _),
  one_smul := quotient.ind $ by exact (λ m, congr_arg quotient.mk $ one_smul _ _), }

/-- The action via `linear_equiv.apply_distrib_mul_action` corresponds to `module.ray.map`. -/
@[simp] lemma module.ray.linear_equiv_smul_eq_map (e : M ≃ₗ[R] M) (v : module.ray R M) :
  e • v = module.ray.map e v := rfl

@[simp] lemma smul_ray_of_ne_zero (g : G) (v : M) (hv) :
  g • ray_of_ne_zero R v hv = ray_of_ne_zero R (g • v) ((smul_ne_zero_iff_ne _).2 hv) := rfl

end action

namespace module.ray

/-- Scaling by a positive unit is a no-op. -/
lemma units_smul_of_pos (u : Rˣ) (hu : 0 < (u : R)) (v : module.ray R M) :
  u • v = v :=
begin
  induction v using module.ray.ind,
  rw [smul_ray_of_ne_zero, ray_eq_iff],
  exact same_ray_pos_smul_left _ hu
end

/-- An arbitrary `ray_vector` giving a ray. -/
def some_ray_vector (x : module.ray R M) : ray_vector R M := quotient.out x

/-- The ray of `some_ray_vector`. -/
@[simp] lemma some_ray_vector_ray (x : module.ray R M) :
  (⟦x.some_ray_vector⟧ : module.ray R M) = x :=
quotient.out_eq _

/-- An arbitrary nonzero vector giving a ray. -/
def some_vector (x : module.ray R M) : M := x.some_ray_vector

/-- `some_vector` is nonzero. -/
@[simp] lemma some_vector_ne_zero (x : module.ray R M) : x.some_vector ≠ 0 :=
x.some_ray_vector.property

/-- The ray of `some_vector`. -/
@[simp] lemma some_vector_ray (x : module.ray R M) :
  ray_of_ne_zero R _ x.some_vector_ne_zero = x :=
(congr_arg _ (subtype.coe_eta _ _) : _).trans x.out_eq

end module.ray

end strict_ordered_comm_semiring

section strict_ordered_comm_ring

variables {R : Type*} [strict_ordered_comm_ring R]
variables {M N : Type*} [add_comm_group M] [add_comm_group N] [module R M] [module R N] {x y : M}

/-- `same_ray.neg` as an `iff`. -/
@[simp] lemma same_ray_neg_iff : same_ray R (-x) (-y) ↔ same_ray R x y :=
by simp only [same_ray, neg_eq_zero, smul_neg, neg_inj]

alias same_ray_neg_iff ↔ same_ray.of_neg same_ray.neg

lemma same_ray_neg_swap : same_ray R (-x) y ↔ same_ray R x (-y) :=
by rw [← same_ray_neg_iff, neg_neg]

lemma eq_zero_of_same_ray_neg_smul_right [no_zero_smul_divisors R M] {r : R} (hr : r < 0)
  (h : same_ray R x (r • x)) :
  x = 0 :=
begin
  rcases h with rfl|h₀|⟨r₁, r₂, hr₁, hr₂, h⟩,
  { refl },
  { simpa [hr.ne] using h₀ },
  { rw [← sub_eq_zero, smul_smul, ← sub_smul, smul_eq_zero] at h,
    refine h.resolve_left (ne_of_gt $ sub_pos.2 _),
    exact (mul_neg_of_pos_of_neg hr₂ hr).trans hr₁ }
end

/-- If a vector is in the same ray as its negation, that vector is zero. -/
lemma eq_zero_of_same_ray_self_neg [no_zero_smul_divisors R M] (h : same_ray R x (-x)) :
  x = 0 :=
begin
  nontriviality M, haveI : nontrivial R := module.nontrivial R M,
  refine eq_zero_of_same_ray_neg_smul_right (neg_lt_zero.2 (zero_lt_one' R)) _,
  rwa [neg_one_smul]
end

namespace ray_vector

/-- Negating a nonzero vector. -/
instance {R : Type*} : has_neg (ray_vector R M) := ⟨λ v, ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast] lemma coe_neg {R : Type*} (v : ray_vector R M) : ↑(-v) = -(v : M) := rfl

/-- Negating a nonzero vector twice produces the original vector. -/
instance {R : Type*} : has_involutive_neg (ray_vector R M) :=
{ neg := has_neg.neg,
  neg_neg := λ v, by rw [subtype.ext_iff, coe_neg, coe_neg, neg_neg] }

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp] lemma equiv_neg_iff {v₁ v₂ : ray_vector R M} : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
same_ray_neg_iff

end ray_vector

variables (R)

/-- Negating a ray. -/
instance : has_neg (module.ray R M) :=
⟨quotient.map (λ v, -v) (λ v₁ v₂, ray_vector.equiv_neg_iff.2)⟩

/-- The ray given by the negation of a nonzero vector. -/
@[simp] lemma neg_ray_of_ne_zero (v : M) (h : v ≠ 0) :
  -(ray_of_ne_zero R _ h) = ray_of_ne_zero R (-v) (neg_ne_zero.2 h) :=
rfl

namespace module.ray

variables {R}

/-- Negating a ray twice produces the original ray. -/
instance : has_involutive_neg (module.ray R M) :=
{ neg := has_neg.neg,
  neg_neg := λ x, quotient.ind (λ a, congr_arg quotient.mk $ neg_neg _) x }

variables {R M}

/-- A ray does not equal its own negation. -/
lemma ne_neg_self [no_zero_smul_divisors R M] (x : module.ray R M) : x ≠ -x :=
begin
  induction x using module.ray.ind with x hx,
  rw [neg_ray_of_ne_zero, ne.def, ray_eq_iff],
  exact mt eq_zero_of_same_ray_self_neg hx
end

lemma neg_units_smul (u : Rˣ) (v : module.ray R M) : (-u) • v = - (u • v) :=
begin
  induction v using module.ray.ind,
  simp only [smul_ray_of_ne_zero, units.smul_def, units.coe_neg, neg_smul, neg_ray_of_ne_zero]
end

/-- Scaling by a negative unit is negation. -/
lemma units_smul_of_neg (u : Rˣ) (hu : (u : R) < 0) (v : module.ray R M) :
  u • v = -v :=
begin
  rw [← neg_inj, neg_neg, ← neg_units_smul, units_smul_of_pos],
  rwa [units.coe_neg, right.neg_pos_iff]
end

@[simp] protected lemma map_neg (f : M ≃ₗ[R] N) (v : module.ray R M) : map f (-v) = - map f v :=
begin
  induction v using module.ray.ind with g hg,
  simp,
end

end module.ray

end strict_ordered_comm_ring

section linear_ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]

/-- `same_ray` follows from membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
lemma same_ray_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ mul_action.orbit (units.pos_subgroup R) v₂) :
  same_ray R v₁ v₂ :=
begin
  rcases h with ⟨⟨r, hr : 0 < (r : R)⟩, (rfl : r • v₂ = v₁)⟩,
  exact same_ray_pos_smul_left _ hr
end

/-- Scaling by an inverse unit is the same as scaling by itself. -/
@[simp] lemma units_inv_smul (u : Rˣ) (v : module.ray R M) :
  u⁻¹ • v = u • v :=
calc u⁻¹ • v = (u * u) • u⁻¹ • v :
  eq.symm $ (u⁻¹ • v).units_smul_of_pos _ $ mul_self_pos.2 u.ne_zero
... = u • v : by rw [mul_smul, smul_inv_smul]

section
variables [no_zero_smul_divisors R M]

@[simp] lemma same_ray_smul_right_iff {v : M} {r : R} :
  same_ray R v (r • v) ↔ 0 ≤ r ∨ v = 0 :=
⟨λ hrv, or_iff_not_imp_left.2 $ λ hr, eq_zero_of_same_ray_neg_smul_right (not_le.1 hr) hrv,
  or_imp_distrib.2 ⟨same_ray_nonneg_smul_right v, λ h, h.symm ▸ same_ray.zero_left _⟩⟩

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
lemma same_ray_smul_right_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
  same_ray R v (r • v) ↔ 0 < r :=
by simp only [same_ray_smul_right_iff, hv, or_false, hr.symm.le_iff_lt]

@[simp] lemma same_ray_smul_left_iff {v : M} {r : R} : same_ray R (r • v) v ↔ 0 ≤ r ∨ v = 0 :=
same_ray_comm.trans same_ray_smul_right_iff

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
lemma same_ray_smul_left_iff_of_ne {v : M} (hv : v ≠ 0) {r : R} (hr : r ≠ 0) :
  same_ray R (r • v) v ↔ 0 < r :=
same_ray_comm.trans (same_ray_smul_right_iff_of_ne hv hr)

@[simp] lemma same_ray_neg_smul_right_iff {v : M} {r : R} :
  same_ray R (-v) (r • v) ↔ r ≤ 0 ∨ v = 0 :=
by rw [← same_ray_neg_iff, neg_neg, ← neg_smul, same_ray_smul_right_iff, neg_nonneg]

lemma same_ray_neg_smul_right_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
  same_ray R (-v) (r • v) ↔ r < 0 :=
by simp only [same_ray_neg_smul_right_iff, hv, or_false, hr.le_iff_lt]

@[simp] lemma same_ray_neg_smul_left_iff {v : M} {r : R} :
  same_ray R (r • v) (-v) ↔ r ≤ 0 ∨ v = 0 :=
same_ray_comm.trans same_ray_neg_smul_right_iff

lemma same_ray_neg_smul_left_iff_of_ne {v : M} {r : R} (hv : v ≠ 0) (hr : r ≠ 0) :
  same_ray R (r • v) (-v) ↔ r < 0 :=
same_ray_comm.trans $ same_ray_neg_smul_right_iff_of_ne hv hr

@[simp] lemma units_smul_eq_self_iff {u : Rˣ} {v : module.ray R M} :
  u • v = v ↔ (0 : R) < u :=
begin
  induction v using module.ray.ind with v hv,
  simp only [smul_ray_of_ne_zero, ray_eq_iff, units.smul_def,
    same_ray_smul_left_iff_of_ne hv u.ne_zero]
end

@[simp] lemma units_smul_eq_neg_iff {u : Rˣ} {v : module.ray R M} :
  u • v = -v ↔ ↑u < (0 : R) :=
by rw [← neg_inj, neg_neg, ← module.ray.neg_units_smul, units_smul_eq_self_iff, units.coe_neg,
  neg_pos]

/-- Two vectors are in the same ray, or the first is in the same ray as the negation of the
second, if and only if they are not linearly independent. -/
lemma same_ray_or_same_ray_neg_iff_not_linear_independent {x y : M} :
  (same_ray R x y ∨ same_ray R x (-y)) ↔ ¬ linear_independent R ![x, y] :=
begin
  by_cases hx : x = 0, { simp [hx, λ h : linear_independent R ![0, y], h.ne_zero 0 rfl] },
  by_cases hy : y = 0, { simp [hy, λ h : linear_independent R ![x, 0], h.ne_zero 1 rfl] },
  simp_rw [fintype.not_linear_independent_iff, fin.sum_univ_two, fin.exists_fin_two],
  refine ⟨λ h, _, λ h, _⟩,
  { rcases h with (hx0|hy0|⟨r₁, r₂, hr₁, hr₂, h⟩)|(hx0|hy0|⟨r₁, r₂, hr₁, hr₂, h⟩),
    { exact false.elim (hx hx0) },
    { exact false.elim (hy hy0) },
    { refine ⟨![r₁, -r₂], _⟩, simp [h, hr₁.ne.symm] },
    { exact false.elim (hx hx0) },
    { exact false.elim (hy (neg_eq_zero.1 hy0)) },
    { refine ⟨![r₁, r₂], _⟩, simp [h, hr₁.ne.symm] } },
  { rcases h with ⟨m, hm, hmne⟩,
    change m 0 • x + m 1 • y = 0 at hm,
    rw add_eq_zero_iff_eq_neg at hm,
    rcases lt_trichotomy (m 0) 0 with hm0|hm0|hm0; rcases lt_trichotomy (m 1) 0 with hm1|hm1|hm1,
    { refine or.inr (or.inr (or.inr ⟨-(m 0), -(m 1), left.neg_pos_iff.2 hm0,
                                     left.neg_pos_iff.2 hm1, _⟩)),
      simp [hm] },
    { exfalso, simpa [hm1, hx, hm0.ne] using hm },
    { refine or.inl (or.inr (or.inr ⟨-(m 0), m 1, left.neg_pos_iff.2 hm0, hm1, _⟩)),
      simp [hm] },
    { exfalso, simpa [hm0, hy, hm1.ne] using hm },
    { refine false.elim (not_and_distrib.2 hmne ⟨hm0, hm1⟩) },
    { exfalso, simpa [hm0, hy, hm1.ne.symm] using hm },
    { refine or.inl (or.inr (or.inr ⟨m 0, -(m 1), hm0, left.neg_pos_iff.2 hm1, _⟩)),
      simp [hm] },
    { exfalso, simpa [hm1, hx, hm0.ne.symm] using hm },
    { refine or.inr (or.inr (or.inr ⟨m 0, m 1, hm0, hm1, _⟩)),
      simp [hm] } }
end

/-- Two vectors are in the same ray, or they are nonzero and the first is in the same ray as the
negation of the second, if and only if they are not linearly independent. -/
lemma same_ray_or_ne_zero_and_same_ray_neg_iff_not_linear_independent {x y : M} :
  (same_ray R x y ∨ x ≠ 0 ∧ y ≠ 0 ∧ same_ray R x (-y)) ↔ ¬ linear_independent R ![x, y] :=
begin
  rw ←same_ray_or_same_ray_neg_iff_not_linear_independent,
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0;
    simp [hx, hy]
end

end

end linear_ordered_comm_ring

namespace same_ray

variables {R : Type*} [linear_ordered_field R]
variables {M : Type*} [add_comm_group M] [module R M] {x y v₁ v₂ : M}

lemma exists_pos_left (h : same_ray R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
  ∃ r : R, 0 < r ∧ r • x = y :=
let ⟨r₁, r₂, hr₁, hr₂, h⟩ := h.exists_pos hx hy in
  ⟨r₂⁻¹ * r₁, mul_pos (inv_pos.2 hr₂) hr₁, by rw [mul_smul, h, inv_smul_smul₀ hr₂.ne']⟩

lemma exists_pos_right (h : same_ray R x y) (hx : x ≠ 0) (hy : y ≠ 0) :
  ∃ r : R, 0 < r ∧ x = r • y :=
(h.symm.exists_pos_left hy hx).imp $ λ _, and.imp_right eq.symm

/-- If a vector `v₂` is on the same ray as a nonzero vector `v₁`, then it is equal to `c • v₁` for
some nonnegative `c`. -/
lemma exists_nonneg_left (h : same_ray R x y) (hx : x ≠ 0) : ∃ r : R, 0 ≤ r ∧ r • x = y :=
begin
  obtain rfl | hy := eq_or_ne y 0,
  { exact ⟨0, le_rfl, zero_smul _ _⟩ },
  { exact (h.exists_pos_left hx hy).imp (λ _, and.imp_left le_of_lt) }
end

/-- If a vector `v₁` is on the same ray as a nonzero vector `v₂`, then it is equal to `c • v₂` for
some nonnegative `c`. -/
lemma exists_nonneg_right (h : same_ray R x y) (hy : y ≠ 0) : ∃ r : R, 0 ≤ r ∧ x = r • y :=
(h.symm.exists_nonneg_left hy).imp $ λ _, and.imp_right eq.symm

/-- If vectors `v₁` and `v₂` are on the same ray, then for some nonnegative `a b`, `a + b = 1`, we
have `v₁ = a • (v₁ + v₂)` and `v₂ = b • (v₁ + v₂)`. -/
lemma exists_eq_smul_add (h : same_ray R v₁ v₂) :
  ∃ a b : R, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • (v₁ + v₂) ∧ v₂ = b • (v₁ + v₂) :=
begin
  rcases h with rfl|rfl|⟨r₁, r₂, h₁, h₂, H⟩,
  { use [0, 1], simp },
  { use [1, 0], simp },
  { have h₁₂ : 0 < r₁ + r₂, from add_pos h₁ h₂,
    refine ⟨r₂ / (r₁ + r₂), r₁ / (r₁ + r₂), div_nonneg h₂.le h₁₂.le, div_nonneg h₁.le h₁₂.le,
      _, _, _⟩,
    { rw [← add_div, add_comm, div_self h₁₂.ne'] },
    { rw [div_eq_inv_mul, mul_smul, smul_add, ← H, ← add_smul, add_comm r₂,
        inv_smul_smul₀ h₁₂.ne'] },
    { rw [div_eq_inv_mul, mul_smul, smul_add, H, ← add_smul, add_comm r₂,
        inv_smul_smul₀ h₁₂.ne'] } }
end

/-- If vectors `v₁` and `v₂` are on the same ray, then they are nonnegative multiples of the same
vector. Actually, this vector can be assumed to be `v₁ + v₂`, see `same_ray.exists_eq_smul_add`. -/
lemma exists_eq_smul (h : same_ray R v₁ v₂) :
  ∃ (u : M) (a b : R), 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ v₁ = a • u ∧ v₂ = b • u :=
⟨v₁ + v₂, h.exists_eq_smul_add⟩

end same_ray

section linear_ordered_field

variables {R : Type*} [linear_ordered_field R]
variables {M : Type*} [add_comm_group M] [module R M] {x y : M}

lemma exists_pos_left_iff_same_ray (hx : x ≠ 0) (hy : y ≠ 0) :
  (∃ r : R, 0 < r ∧ r • x = y) ↔ same_ray R x y :=
begin
  refine ⟨λ h, _, λ h, h.exists_pos_left hx hy⟩,
  rcases h with ⟨r, hr, rfl⟩,
  exact same_ray_pos_smul_right x hr
end

lemma exists_pos_left_iff_same_ray_and_ne_zero (hx : x ≠ 0) :
  (∃ r : R, 0 < r ∧ r • x = y) ↔ (same_ray R x y ∧ y ≠ 0) :=
begin
  split,
  { rintro ⟨r, hr, rfl⟩,
    simp [hx, hr.le, hr.ne'] },
  { rintro ⟨hxy, hy⟩,
    exact (exists_pos_left_iff_same_ray hx hy).2 hxy }
end

lemma exists_nonneg_left_iff_same_ray (hx : x ≠ 0) :
  (∃ r : R, 0 ≤ r ∧ r • x = y) ↔ same_ray R x y :=
begin
  refine ⟨λ h, _, λ h, h.exists_nonneg_left hx⟩,
  rcases h with ⟨r, hr, rfl⟩,
  exact same_ray_nonneg_smul_right x hr
end

lemma exists_pos_right_iff_same_ray (hx : x ≠ 0) (hy : y ≠ 0) :
  (∃ r : R, 0 < r ∧ x = r • y) ↔ same_ray R x y :=
by simpa only [same_ray_comm, eq_comm] using exists_pos_left_iff_same_ray hy hx

lemma exists_pos_right_iff_same_ray_and_ne_zero (hy : y ≠ 0) :
  (∃ r : R, 0 < r ∧ x = r • y) ↔ (same_ray R x y ∧ x ≠ 0) :=
by simpa only [same_ray_comm, eq_comm] using exists_pos_left_iff_same_ray_and_ne_zero hy

lemma exists_nonneg_right_iff_same_ray (hy : y ≠ 0) :
  (∃ r : R, 0 ≤ r ∧ x = r • y) ↔ same_ray R x y :=
by simpa only [same_ray_comm, eq_comm] using exists_nonneg_left_iff_same_ray hy

end linear_ordered_field
