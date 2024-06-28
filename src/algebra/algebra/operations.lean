/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.bilinear
import algebra.algebra.equiv
import algebra.module.submodule.pointwise
import algebra.module.submodule.bilinear
import algebra.module.opposites
import algebra.order.kleene
import data.finset.pointwise
import data.set.semiring
import data.set.pointwise.big_operators
import group_theory.group_action.sub_mul_action.pointwise

/-!
# Multiplication and division of submodules of an algebra.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An interface for multiplication and division of sub-R-modules of an R-algebra A is developed.

## Main definitions

Let `R` be a commutative ring (or semiring) and let `A` be an `R`-algebra.

* `1 : submodule R A`       : the R-submodule R of the R-algebra A
* `has_mul (submodule R A)` : multiplication of two sub-R-modules M and N of A is defined to be
                              the smallest submodule containing all the products `m * n`.
* `has_div (submodule R A)` : `I / J` is defined to be the submodule consisting of all `a : A` such
                              that `a • J ⊆ I`

It is proved that `submodule R A` is a semiring, and also an algebra over `set A`.

Additionally, in the `pointwise` locale we promote `submodule.pointwise_distrib_mul_action` to a
`mul_semiring_action` as `submodule.pointwise_mul_semiring_action`.

## Tags

multiplication of submodules, division of submodules, submodule semiring
-/

universes uι u v

open algebra set mul_opposite
open_locale big_operators
open_locale pointwise

namespace sub_mul_action
variables {R : Type u}  {A : Type v} [comm_semiring R] [semiring A] [algebra R A]

lemma algebra_map_mem (r : R) : algebra_map R A r ∈ (1 : sub_mul_action R A) :=
⟨r, (algebra_map_eq_smul_one r).symm⟩

lemma mem_one' {x : A} : x ∈ (1 : sub_mul_action R A) ↔ ∃ y, algebra_map R A y = x :=
exists_congr $ λ r, by rw algebra_map_eq_smul_one

end sub_mul_action

namespace submodule

variables {ι : Sort uι}
variables {R : Type u} [comm_semiring R]

section ring

variables {A : Type v} [semiring A] [algebra R A]
variables (S T : set A) {M N P Q : submodule R A} {m n : A}

/-- `1 : submodule R A` is the submodule R of A. -/
instance : has_one (submodule R A) :=
⟨(algebra.linear_map R A).range⟩

theorem one_eq_range :
  (1 : submodule R A) = (algebra.linear_map R A).range := rfl

lemma le_one_to_add_submonoid :
  1 ≤ (1 : submodule R A).to_add_submonoid :=
begin
  rintros x ⟨n, rfl⟩,
  exact ⟨n, map_nat_cast (algebra_map R A) n⟩,
end

lemma algebra_map_mem (r : R) : algebra_map R A r ∈ (1 : submodule R A) :=
linear_map.mem_range_self _ _

@[simp] lemma mem_one {x : A} : x ∈ (1 : submodule R A) ↔ ∃ y, algebra_map R A y = x :=
iff.rfl

@[simp] lemma to_sub_mul_action_one : (1 : submodule R A).to_sub_mul_action = 1 :=
set_like.ext $ λ x, mem_one.trans sub_mul_action.mem_one'.symm

theorem one_eq_span : (1 : submodule R A) = R ∙ 1 :=
begin
  apply submodule.ext,
  intro a,
  simp only [mem_one, mem_span_singleton, algebra.smul_def, mul_one]
end

theorem one_eq_span_one_set : (1 : submodule R A) = span R 1 := one_eq_span

theorem one_le : (1 : submodule R A) ≤ P ↔ (1 : A) ∈ P :=
by simpa only [one_eq_span, span_le, set.singleton_subset_iff]

protected lemma map_one {A'} [semiring A'] [algebra R A'] (f : A →ₐ[R] A') :
  map f.to_linear_map (1 : submodule R A) = 1 :=
by { ext, simp }

@[simp] lemma map_op_one :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : submodule R A) = 1 :=
by { ext, induction x using mul_opposite.rec, simp }

@[simp] lemma comap_op_one :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (1 : submodule R Aᵐᵒᵖ) = 1 :=
by { ext, simp }

@[simp] lemma map_unop_one :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : submodule R Aᵐᵒᵖ) = 1 :=
by rw [←comap_equiv_eq_map_symm, comap_op_one]

@[simp] lemma comap_unop_one :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (1 : submodule R A) = 1 :=
by rw [←map_equiv_eq_comap_symm, map_op_one]


/-- Multiplication of sub-R-modules of an R-algebra A. The submodule `M * N` is the
smallest R-submodule of `A` containing the elements `m * n` for `m ∈ M` and `n ∈ N`. -/
instance : has_mul (submodule R A) := ⟨submodule.map₂ $ linear_map.mul R A⟩

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N := apply_mem_map₂ _ hm hn

theorem mul_le : M * N ≤ P ↔ ∀ (m ∈ M) (n ∈ N), m * n ∈ P := map₂_le

lemma mul_to_add_submonoid (M N : submodule R A) :
  (M * N).to_add_submonoid = M.to_add_submonoid * N.to_add_submonoid :=
begin
  dsimp [has_mul.mul],
  simp_rw [←linear_map.mul_left_to_add_monoid_hom R, linear_map.mul_left, ←map_to_add_submonoid _ N,
    map₂],
  rw supr_to_add_submonoid,
  refl,
end

@[elab_as_eliminator] protected theorem mul_induction_on
  {C : A → Prop} {r : A} (hr : r ∈ M * N)
  (hm : ∀ (m ∈ M) (n ∈ N), C (m * n)) (ha : ∀ x y, C x → C y → C (x + y)) : C r :=
begin
  rw [←mem_to_add_submonoid, mul_to_add_submonoid] at hr,
  exact add_submonoid.mul_induction_on hr hm ha,
end

/-- A dependent version of `mul_induction_on`. -/
@[elab_as_eliminator] protected theorem mul_induction_on'
  {C : Π r, r ∈ M * N → Prop}
  (hm : ∀ (m ∈ M) (n ∈ N), C (m * n) (mul_mem_mul ‹_› ‹_›))
  (ha : ∀ x hx y hy, C x hx → C y hy → C (x + y) (add_mem ‹_› ‹_›))
  {r : A} (hr : r ∈ M * N) : C r hr :=
begin
  refine exists.elim _ (λ (hr : r ∈ M * N) (hc : C r hr), hc),
  exact submodule.mul_induction_on hr
    (λ x hx y hy, ⟨_, hm _ hx _ hy⟩) (λ x y ⟨_, hx⟩ ⟨_, hy⟩, ⟨_, ha _ _ _ _ hx hy⟩),
end

variables R
theorem span_mul_span : span R S * span R T = span R (S * T) := map₂_span_span _ _ _ _
variables {R}

variables (M N P Q)

@[simp] theorem mul_bot : M * ⊥ = ⊥ := map₂_bot_right _ _

@[simp] theorem bot_mul : ⊥ * M = ⊥ := map₂_bot_left _ _

@[simp] protected theorem one_mul : (1 : submodule R A) * M = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, one_mul, span_eq] }

@[simp] protected theorem mul_one : M * 1 = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, mul_one, span_eq] }

variables {M N P Q}

@[mono] theorem mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q := map₂_le_map₂ hmp hnq

theorem mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P := map₂_le_map₂_left h

theorem mul_le_mul_right (h : N ≤ P) : M * N ≤ M * P := map₂_le_map₂_right h

variables (M N P)
theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P := map₂_sup_right _ _ _ _

theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P := map₂_sup_left _ _ _ _

lemma mul_subset_mul : (↑M : set A) * (↑N : set A) ⊆ (↑(M * N) : set A) :=
image2_subset_map₂ (algebra.lmul R A).to_linear_map M N

protected lemma map_mul {A'} [semiring A'] [algebra R A'] (f : A →ₐ[R] A') :
  map f.to_linear_map (M * N) = map f.to_linear_map M * map f.to_linear_map N :=
calc map f.to_linear_map (M * N)
    = ⨆ (i : M), (N.map (linear_map.mul R A i)).map f.to_linear_map : map_supr _ _
... = map f.to_linear_map M * map f.to_linear_map N  :
  begin
    apply congr_arg Sup,
    ext S,
    split; rintros ⟨y, hy⟩,
    { use [f y, mem_map.mpr ⟨y.1, y.2, rfl⟩],
      refine trans _ hy,
      ext,
      simp },
    { obtain ⟨y', hy', fy_eq⟩ := mem_map.mp y.2,
      use [y', hy'],
      refine trans _ hy,
      rw f.to_linear_map_apply at fy_eq,
      ext,
      simp [fy_eq] }
end

lemma map_op_mul :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
    map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
      map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M :=
begin
  apply le_antisymm,
  { simp_rw map_le_iff_le_comap,
    refine mul_le.2 (λ m hm n hn, _),
    rw [mem_comap, map_equiv_eq_comap_symm, map_equiv_eq_comap_symm],
    show op n * op m ∈ _,
    exact mul_mem_mul hn hm },
  { refine mul_le.2 (mul_opposite.rec $ λ m hm, mul_opposite.rec $ λ n hn, _),
    rw submodule.mem_map_equiv at ⊢ hm hn,
    exact mul_mem_mul hn hm, }
end

lemma comap_unop_mul :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
    comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
      comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M :=
by simp_rw [←map_equiv_eq_comap_symm, map_op_mul]

lemma map_unop_mul (M N : submodule R Aᵐᵒᵖ) :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M * N) =
    map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) N *
      map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M :=
have function.injective (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) :=
  linear_equiv.injective _,
map_injective_of_injective this $
  by rw [← map_comp, map_op_mul, ←map_comp, ←map_comp, linear_equiv.comp_coe,
         linear_equiv.symm_trans_self, linear_equiv.refl_to_linear_map, map_id, map_id, map_id]

lemma comap_op_mul (M N : submodule R Aᵐᵒᵖ) :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M * N) =
    comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) N *
      comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M :=
by simp_rw [comap_equiv_eq_map_symm, map_unop_mul]

section
open_locale pointwise

/-- `submodule.has_pointwise_neg` distributes over multiplication.

This is available as an instance in the `pointwise` locale. -/
protected def has_distrib_pointwise_neg {A} [ring A] [algebra R A] :
  has_distrib_neg (submodule R A) :=
to_add_submonoid_injective.has_distrib_neg _ neg_to_add_submonoid mul_to_add_submonoid

localized "attribute [instance] submodule.has_distrib_pointwise_neg" in pointwise

end

section decidable_eq

open_locale classical

lemma mem_span_mul_finite_of_mem_span_mul
  {R A} [semiring R] [add_comm_monoid A] [has_mul A] [module R A]
  {S : set A} {S' : set A} {x : A} (hx : x ∈ span R (S * S')) :
  ∃ (T T' : finset A), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ x ∈ span R (T * T' : set A) :=
begin
  obtain ⟨U, h, hU⟩ := mem_span_finite_of_mem_span hx,
  obtain ⟨T, T', hS, hS', h⟩ := finset.subset_mul h,
  use [T, T', hS, hS'],
  have h' : (U : set A) ⊆ T * T', { assumption_mod_cast, },
  have h'' := span_mono h' hU,
  assumption,
end

end decidable_eq

lemma mul_eq_span_mul_set (s t : submodule R A) : s * t = span R ((s : set A) * (t : set A)) :=
map₂_eq_span_image2 _ s t

lemma supr_mul (s : ι → submodule R A) (t : submodule R A) : (⨆ i, s i) * t = ⨆ i, s i * t :=
map₂_supr_left _ s t

lemma mul_supr (t : submodule R A) (s : ι → submodule R A) : t * (⨆ i, s i) = ⨆ i, t * s i :=
map₂_supr_right _ t s

lemma mem_span_mul_finite_of_mem_mul {P Q : submodule R A} {x : A} (hx : x ∈ P * Q) :
  ∃ (T T' : finset A), (T : set A) ⊆ P ∧ (T' : set A) ⊆ Q ∧ x ∈ span R (T * T' : set A) :=
submodule.mem_span_mul_finite_of_mem_span_mul
  (by rwa [← submodule.span_eq P, ← submodule.span_eq Q, submodule.span_mul_span] at hx)

variables {M N P}

lemma mem_span_singleton_mul {x y : A} : x ∈ span R {y} * P ↔ ∃ z ∈ P, y * z = x :=
by { simp_rw [(*), map₂_span_singleton_eq_map, exists_prop], refl }

lemma mem_mul_span_singleton {x y : A} : x ∈ P * span R {y} ↔ ∃ z ∈ P, z * y = x :=
by { simp_rw [(*), map₂_span_singleton_eq_map_flip, exists_prop], refl }

/-- Sub-R-modules of an R-algebra form an idempotent semiring. -/
instance : idem_semiring (submodule R A) :=
{ one_mul       := submodule.one_mul,
  mul_one       := submodule.mul_one,
  zero_mul      := bot_mul,
  mul_zero      := mul_bot,
  left_distrib  := mul_sup,
  right_distrib := sup_mul,
  ..to_add_submonoid_injective.semigroup _ (λ m n : submodule R A, mul_to_add_submonoid m n),
  ..add_monoid_with_one.unary,
  ..submodule.pointwise_add_comm_monoid,
  ..submodule.has_one,
  ..submodule.has_mul,
  ..(by apply_instance : order_bot (submodule R A)),
  ..(by apply_instance : lattice (submodule R A)) }

variable R

def span_singleton : A →*₀ submodule R A :=
{ to_fun := λ x, span R {x},
  map_zero' := span_zero_singleton R,
  map_one' := one_eq_span.symm,
  map_mul' := λ x y, by rw [span_mul_span, set.singleton_mul_singleton] }

variables {R} (M)

lemma span_pow (s : set A) : ∀ n : ℕ, span R s ^ n = span R (s ^ n)
| 0 := by rw [pow_zero, pow_zero, one_eq_span_one_set]
| (n + 1) := by rw [pow_succ, pow_succ, span_pow, span_mul_span]

lemma pow_eq_span_pow_set (n : ℕ) : M ^ n = span R ((M : set A) ^ n) := by rw [←span_pow, span_eq]

lemma pow_subset_pow {n : ℕ} : (↑M : set A)^n ⊆ ↑(M^n : submodule R A) :=
(pow_eq_span_pow_set M n).symm ▸ subset_span

lemma pow_mem_pow {x : A} (hx : x ∈ M) (n : ℕ) : x ^ n ∈ M ^ n :=
pow_subset_pow _ $ set.pow_mem_pow hx _

lemma pow_to_add_submonoid {n : ℕ} (h : n ≠ 0) :
  (M ^ n).to_add_submonoid = M.to_add_submonoid ^ n :=
begin
  induction n with n ih,
  { exact (h rfl).elim },
  { rw [pow_succ, pow_succ, mul_to_add_submonoid],
    cases n,
    { rw [pow_zero, pow_zero, mul_one, ←mul_to_add_submonoid, mul_one] },
    { rw ih n.succ_ne_zero } },
end

lemma le_pow_to_add_submonoid {n : ℕ} :
  M.to_add_submonoid ^ n ≤ (M ^ n).to_add_submonoid :=
begin
  obtain rfl | hn := decidable.eq_or_ne n 0,
  { rw [pow_zero, pow_zero], exact le_one_to_add_submonoid },
  { exact (pow_to_add_submonoid M hn).ge }
end

/-- Dependent version of `submodule.pow_induction_on_left`. -/
@[elab_as_eliminator] protected theorem pow_induction_on_left'
  {C : Π (n : ℕ) x, x ∈ M ^ n → Prop}
  (hr : ∀ r : R, C 0 (algebra_map _ _ r) (algebra_map_mem r))
  (hadd : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
  (hmul : ∀ (m ∈ M) i x hx, C i x hx → C (i.succ) (m * x) (mul_mem_mul H hx))
  {x : A} {n : ℕ} (hx : x ∈ M ^ n) : C n x hx :=
begin
  induction n with n n_ih generalizing x,
  { rw pow_zero at hx,
    obtain ⟨r, rfl⟩ := hx,
    exact hr r, },
  exact submodule.mul_induction_on'
    (λ m hm x ih, hmul _ hm _ _ _ (n_ih ih))
    (λ x hx y hy Cx Cy, hadd _ _ _ _ _ Cx Cy) hx,
end

/-- Dependent version of `submodule.pow_induction_on_right`. -/
@[elab_as_eliminator] protected theorem pow_induction_on_right'
  {C : Π (n : ℕ) x, x ∈ M ^ n → Prop}
  (hr : ∀ r : R, C 0 (algebra_map _ _ r) (algebra_map_mem r))
  (hadd : ∀ x y i hx hy, C i x hx → C i y hy → C i (x + y) (add_mem ‹_› ‹_›))
  (hmul : ∀ i x hx, C i x hx → ∀ m ∈ M,
    C (i.succ) (x * m) ((pow_succ' M i).symm ▸ mul_mem_mul hx H))
  {x : A} {n : ℕ} (hx : x ∈ M ^ n) : C n x hx :=
begin
  induction n with n n_ih generalizing x,
  { rw pow_zero at hx,
    obtain ⟨r, rfl⟩ := hx,
    exact hr r, },
  revert hx,
  simp_rw pow_succ',
  intro hx,
  exact submodule.mul_induction_on'
    (λ m hm x ih, hmul _ _ hm (n_ih _) _ ih)
    (λ x hx y hy Cx Cy, hadd _ _ _ _ _ Cx Cy) hx,
end

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `m * x` where `m ∈ M` and it holds for `x` -/
@[elab_as_eliminator] protected theorem pow_induction_on_left
  {C : A → Prop}
  (hr : ∀ r : R, C (algebra_map _ _ r))
  (hadd : ∀ x y, C x → C y → C (x + y))
  (hmul : ∀ (m ∈ M) x, C x → C (m * x))
  {x : A} {n : ℕ} (hx : x ∈ M ^ n) : C x :=
submodule.pow_induction_on_left' M
  (by exact hr) (λ x y i hx hy, hadd x y) (λ m hm i x hx, hmul _ hm _) hx

/-- To show a property on elements of `M ^ n` holds, it suffices to show that it holds for scalars,
is closed under addition, and holds for `x * m` where `m ∈ M` and it holds for `x` -/
@[elab_as_eliminator] protected theorem pow_induction_on_right
  {C : A → Prop}
  (hr : ∀ r : R, C (algebra_map _ _ r))
  (hadd : ∀ x y, C x → C y → C (x + y))
  (hmul : ∀ x, C x → ∀ (m ∈ M), C (x * m))
  {x : A} {n : ℕ} (hx : x ∈ M ^ n) : C x :=
submodule.pow_induction_on_right' M
  (by exact hr) (λ x y i hx hy, hadd x y) (λ i x hx, hmul _) hx

/-- `submodule.map` as a `ring_hom`, when applied to an `alg_hom`. -/
@[simps]
def map_hom {A'} [semiring A'] [algebra R A'] (f : A →ₐ[R] A') :
  submodule R A →+* submodule R A' :=
{ to_fun := map f,
  map_zero' := map_bot _,
  map_one' := submodule.map_one _,
  map_add' := (add_hom f).map_add,
  map_mul' := λ _ _, submodule.map_mul _ _ _ }

/-- `submodule.map` as a `ring_equiv`, when applied to an `alg_equiv`. -/
@[simps]
def map_equiv {A'} [semiring A'] [algebra R A'] (f : A ≃ₐ[R] A') :
  submodule R A ≃+* submodule R A' :=
{ map_mul' := λ _ _, submodule.map_mul _ _ f.to_alg_hom, .. add_equiv f.to_linear_equiv }

/-- The ring of submodules of the opposite algebra is isomorphic to the opposite ring of
submodules. -/
@[simps apply symm_apply]
def equiv_opposite : submodule R Aᵐᵒᵖ ≃+* (submodule R A)ᵐᵒᵖ :=
{ to_fun := λ p, op $ p.comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ),
  inv_fun := λ p, p.unop.comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A),
  left_inv := λ p, set_like.coe_injective $ rfl,
  right_inv := λ p, unop_injective $ set_like.coe_injective rfl,
  map_add' := λ p q, by simp [comap_equiv_eq_map_symm, ←op_add],
  map_mul' := λ p q, congr_arg op $ comap_op_mul _ _ }

protected lemma map_pow {A'} [semiring A'] [algebra R A'] (f : A →ₐ[R] A') (n : ℕ) :
  map f.to_linear_map (M ^ n) = map f.to_linear_map M ^ n :=
map_pow (map_hom f) M n

lemma comap_unop_pow (n : ℕ) :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
    comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n :=
(equiv_opposite : submodule R Aᵐᵒᵖ ≃+* _).symm.map_pow (op M) n

lemma comap_op_pow (n : ℕ) (M : submodule R Aᵐᵒᵖ) :
  comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
    comap (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n :=
op_injective $ (equiv_opposite : submodule R Aᵐᵒᵖ ≃+* _).map_pow M n

lemma map_op_pow (n : ℕ) :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) (M ^ n) =
    map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ) : A →ₗ[R] Aᵐᵒᵖ) M ^ n :=
by rw [map_equiv_eq_comap_symm, map_equiv_eq_comap_symm, comap_unop_pow]

lemma map_unop_pow (n : ℕ) (M : submodule R Aᵐᵒᵖ) :
  map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) (M ^ n) =
    map (↑(op_linear_equiv R : A ≃ₗ[R] Aᵐᵒᵖ).symm : Aᵐᵒᵖ →ₗ[R] A) M ^ n :=
by rw [←comap_equiv_eq_map_symm, ←comap_equiv_eq_map_symm, comap_op_pow]

/-- `span` is a semiring homomorphism (recall multiplication is pointwise multiplication of subsets
on either side). -/
@[simps]
def span.ring_hom : set_semiring A →+* submodule R A :=
{ to_fun := λ s, submodule.span R s.down,
  map_zero' := span_empty,
  map_one' := one_eq_span.symm,
  map_add' := span_union,
  map_mul' := λ s t, by rw [set_semiring.down_mul, span_mul_span, ← image_mul_prod] }

section
variables {α : Type*} [monoid α] [mul_semiring_action α A] [smul_comm_class α R A]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `submodule.pointwise_distrib_mul_action`. -/
protected def pointwise_mul_semiring_action : mul_semiring_action α (submodule R A) :=
{ smul_mul := λ r x y, submodule.map_mul x y $ mul_semiring_action.to_alg_hom R A r,
  smul_one := λ r, submodule.map_one $ mul_semiring_action.to_alg_hom R A r,
  ..submodule.pointwise_distrib_mul_action }

localized "attribute [instance] submodule.pointwise_mul_semiring_action" in pointwise

end

end ring

section comm_ring

variables {A : Type v} [comm_semiring A] [algebra R A]
variables {M N : submodule R A} {m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
mul_comm m n ▸ mul_mem_mul hm hn

variables (M N)
protected theorem mul_comm : M * N = N * M :=
le_antisymm (mul_le.2 $ λ r hrm s hsn, mul_mem_mul_rev hsn hrm)
(mul_le.2 $ λ r hrn s hsm, mul_mem_mul_rev hsm hrn)

/-- Sub-R-modules of an R-algebra A form a semiring. -/
instance : idem_comm_semiring (submodule R A) :=
{ mul_comm := submodule.mul_comm,
  .. submodule.idem_semiring }

lemma prod_span {ι : Type*} (s : finset ι) (M : ι → set A) :
  (∏ i in s, submodule.span R (M i)) = submodule.span R (∏ i in s, M i) :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simp [one_eq_span, set.singleton_one] },
  { intros _ _ H ih,
    rw [finset.prod_insert H, finset.prod_insert H, ih, span_mul_span] }
end

lemma prod_span_singleton {ι : Type*} (s : finset ι) (x : ι → A) :
  (∏ i in s, span R ({x i} : set A)) = span R {∏ i in s, x i} :=
by rw [prod_span, set.finset_prod_singleton]

variables (R A)

/-- R-submodules of the R-algebra A are a module over `set A`. -/
instance module_set : module (set_semiring A) (submodule R A) :=
{ smul := λ s P, span R s.down * P,
  smul_add := λ _ _ _, mul_add _ _ _,
  add_smul := λ s t P,
    by simp_rw [has_smul.smul, set_semiring.down_add, span_union, sup_mul, add_eq_sup],
  mul_smul := λ s t P,
    by simp_rw [has_smul.smul, set_semiring.down_mul, ← mul_assoc, span_mul_span],
  one_smul := λ P,
    by simp_rw [has_smul.smul, set_semiring.down_one, ←one_eq_span_one_set, one_mul],
  zero_smul := λ P,
    by simp_rw [has_smul.smul, set_semiring.down_zero, span_empty, bot_mul, bot_eq_zero],
  smul_zero := λ _, mul_bot _ }

variables {R A}

lemma smul_def (s : set_semiring A) (P : submodule R A) : s • P = span R s.down * P := rfl

lemma smul_le_smul {s t : set_semiring A} {M N : submodule R A} (h₁ : s.down ⊆ t.down)
  (h₂ : M ≤ N) : s • M ≤ t • N :=
mul_le_mul (span_mono h₁) h₂

lemma smul_singleton (a : A) (M : submodule R A) :
  ({a} : set A).up • M = M.map (linear_map.mul_left R a) :=
begin
  conv_lhs {rw ← span_eq M},
  change span _ _ * span _ _ = _,
  rw [span_mul_span],
  apply le_antisymm,
  { rw span_le,
    rintros _ ⟨b, m, hb, hm, rfl⟩,
    rw [set_like.mem_coe, mem_map, set.mem_singleton_iff.mp hb],
    exact ⟨m, hm, rfl⟩ },
  { rintros _ ⟨m, hm, rfl⟩, exact subset_span ⟨a, m, set.mem_singleton a, hm, rfl⟩ }
end

section quotient

/-- The elements of `I / J` are the `x` such that `x • J ⊆ I`.

In fact, we define `x ∈ I / J` to be `∀ y ∈ J, x * y ∈ I` (see `mem_div_iff_forall_mul_mem`),
which is equivalent to `x • J ⊆ I` (see `mem_div_iff_smul_subset`), but nicer to use in proofs.

This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance : has_div (submodule R A) :=
⟨ λ I J,
{ carrier   := { x | ∀ y ∈ J, x * y ∈ I },
  zero_mem' := λ y hy, by { rw zero_mul, apply submodule.zero_mem },
  add_mem'  := λ a b ha hb y hy, by { rw add_mul, exact submodule.add_mem _ (ha _ hy) (hb _ hy) },
  smul_mem' := λ r x hx y hy, by { rw algebra.smul_mul_assoc,
    exact submodule.smul_mem _ _ (hx _ hy) } } ⟩

lemma mem_div_iff_forall_mul_mem {x : A} {I J : submodule R A} :
  x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
iff.refl _

lemma mem_div_iff_smul_subset {x : A} {I J : submodule R A} : x ∈ I / J ↔ x • (J : set A) ⊆ I :=
⟨ λ h y ⟨y', hy', xy'_eq_y⟩, by { rw ← xy'_eq_y, apply h, assumption },
  λ h y hy, h (set.smul_mem_smul_set hy) ⟩

lemma le_div_iff {I J K : submodule R A} : I ≤ J / K ↔ ∀ (x ∈ I) (z ∈ K), x * z ∈ J := iff.refl _

lemma le_div_iff_mul_le {I J K : submodule R A} : I ≤ J / K ↔ I * K ≤ J :=
by rw [le_div_iff, mul_le]

@[simp] lemma one_le_one_div {I : submodule R A} :
  1 ≤ 1 / I ↔ I ≤ 1 :=
begin
  split, all_goals {intro hI},
  {rwa [le_div_iff_mul_le, one_mul] at hI},
  {rwa [le_div_iff_mul_le, one_mul]},
end

lemma le_self_mul_one_div {I : submodule R A} (hI : I ≤ 1) :
  I ≤ I * (1 / I) :=
begin
  rw [← mul_one I] {occs := occurrences.pos [1]},
  apply mul_le_mul_right (one_le_one_div.mpr hI),
end

lemma mul_one_div_le_one {I : submodule R A} : I * (1 / I) ≤ 1 :=
begin
  rw submodule.mul_le,
  intros m hm n hn,
  rw [submodule.mem_div_iff_forall_mul_mem] at hn,
  rw mul_comm,
  exact hn m hm,
end

@[simp] protected lemma map_div {B : Type*} [comm_semiring B] [algebra R B]
  (I J : submodule R A) (h : A ≃ₐ[R] B) :
  (I / J).map h.to_linear_map = I.map h.to_linear_map / J.map h.to_linear_map :=
begin
  ext x,
  simp only [mem_map, mem_div_iff_forall_mul_mem],
  split,
  { rintro ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
    exact ⟨x * y, hx _ hy, h.map_mul x y⟩ },
  { rintro hx,
    refine ⟨h.symm x, λ z hz, _, h.apply_symm_apply x⟩,
    obtain ⟨xz, xz_mem, hxz⟩ := hx (h z) ⟨z, hz, rfl⟩,
    convert xz_mem,
    apply h.injective,
    erw [h.map_mul, h.apply_symm_apply, hxz] }
end

end quotient

end comm_ring

end submodule
