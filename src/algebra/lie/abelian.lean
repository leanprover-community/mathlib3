/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.of_associative
import algebra.lie.ideal_operations

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `lie_module.is_trivial`
  * `is_lie_abelian`
  * `commutative_ring_iff_abelian_lie_ring`
  * `lie_module.ker`
  * `lie_module.maximal_trivial_submodule`
  * `lie_algebra.center`

## Tags

lie algebra, abelian, commutative, center
-/

universes u v w w₁ w₂

/-- A Lie (ring) module is trivial iff all brackets vanish. -/
class lie_module.is_trivial (L : Type v) (M : Type w) [has_bracket L M] [has_zero M] : Prop :=
(trivial : ∀ (x : L) (m : M), ⁅x, m⁆ = 0)

@[simp] lemma trivial_lie_zero (L : Type v) (M : Type w)
  [has_bracket L M] [has_zero M] [lie_module.is_trivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0 :=
lie_module.is_trivial.trivial x m

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
abbreviation is_lie_abelian (L : Type v) [has_bracket L L] [has_zero L] : Prop :=
lie_module.is_trivial L L

instance lie_ideal.is_lie_abelian_of_trivial (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] (I : lie_ideal R L) [h : lie_module.is_trivial L I] :
  is_lie_abelian I :=
{ trivial := λ x y, by apply h.trivial, }

lemma function.injective.is_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w}
  [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]
  {f : L₁ →ₗ⁅R⁆ L₂} (h₁ : function.injective f) (h₂ : is_lie_abelian L₂) :
  is_lie_abelian L₁ :=
{ trivial := λ x y,
    by { apply h₁, rw [lie_hom.map_lie, trivial_lie_zero, lie_hom.map_zero], } }

lemma function.surjective.is_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w}
  [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]
  {f : L₁ →ₗ⁅R⁆ L₂} (h₁ : function.surjective f) (h₂ : is_lie_abelian L₁) :
  is_lie_abelian L₂ :=
{ trivial := λ x y,
    begin
      obtain ⟨u, hu⟩ := h₁ x, rw ← hu,
      obtain ⟨v, hv⟩ := h₁ y, rw ← hv,
      rw [← lie_hom.map_lie, trivial_lie_zero, lie_hom.map_zero],
    end }

lemma lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w}
  [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]
  (e : L₁ ≃ₗ⁅R⁆ L₂) : is_lie_abelian L₁ ↔ is_lie_abelian L₂ :=
⟨e.symm.injective.is_lie_abelian, e.injective.is_lie_abelian⟩

lemma commutative_ring_iff_abelian_lie_ring {A : Type v} [ring A] :
  is_commutative A (*) ↔ is_lie_abelian A :=
begin
  have h₁ : is_commutative A (*) ↔ ∀ (a b : A), a * b = b * a := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  have h₂ : is_lie_abelian A ↔ ∀ (a b : A), ⁅a, b⁆ = 0 := ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  simp only [h₁, h₂, lie_ring.of_associative_ring_bracket, sub_eq_zero],
end

lemma lie_algebra.is_lie_abelian_bot (R : Type u) (L : Type v)
  [comm_ring R] [lie_ring L] [lie_algebra R L] : is_lie_abelian (⊥ : lie_ideal R L) :=
⟨begin
  rintros ⟨x, hx⟩ ⟨y, hy⟩,
  suffices : ⁅x, y⁆ = 0,
  { ext, simp only [this, lie_subalgebra.coe_bracket, submodule.coe_mk, submodule.coe_zero], },
  change x ∈ (⊥ : lie_ideal R L) at hx, rw lie_submodule.mem_bot at hx, rw [hx, zero_lie],
end⟩

section center

variables (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group N] [module R N] [lie_ring_module L N] [lie_module R L N]

namespace lie_module

/-- The kernel of the action of a Lie algebra `L` on a Lie module `M` as a Lie ideal in `L`. -/
protected def ker : lie_ideal R L := (to_endomorphism R L M).ker

@[simp] protected lemma mem_ker (x : L) : x ∈ lie_module.ker R L M ↔ ∀ (m : M), ⁅x, m⁆ = 0 :=
begin
  dunfold lie_module.ker,
  simp only [lie_hom.mem_ker, linear_map.ext_iff, linear_map.zero_apply,
    to_endomorphism_apply_apply],
end

/-- The largest submodule of a Lie module `M` on which the Lie algebra `L` acts trivially. -/
def maximal_trivial_submodule : lie_submodule R L M :=
{ carrier   := { m | ∀ (x : L), ⁅x, m⁆ = 0 },
  zero_mem' := λ x, lie_zero x,
  add_mem'  := λ x y hx hy z, by rw [lie_add, hx, hy, add_zero],
  smul_mem' := λ c x hx y, by rw [lie_smul, hx, smul_zero],
  lie_mem   := λ x m hm y, by rw [hm, lie_zero], }

@[simp] lemma mem_maximal_trivial_submodule (m : M) :
  m ∈ maximal_trivial_submodule R L M ↔ ∀ (x : L), ⁅x, m⁆ = 0 :=
iff.rfl

instance : is_trivial L (maximal_trivial_submodule R L M) :=
{ trivial := λ x m, subtype.ext (m.property x), }

lemma trivial_iff_le_maximal_trivial (N : lie_submodule R L M) :
  is_trivial L N ↔ N ≤ maximal_trivial_submodule R L M :=
begin
  split,
  { rintros ⟨h⟩, intros m hm x, specialize h x ⟨m, hm⟩, rw subtype.ext_iff at h, exact h, },
  { intros h, constructor, rintros x ⟨m, hm⟩, apply subtype.ext, apply h, exact hm, },
end

lemma is_trivial_iff_maximal_trivial_eq_top :
  is_trivial L M ↔ maximal_trivial_submodule R L M = ⊤ :=
begin
  split,
  { rintros ⟨h⟩, ext,
    simp only [mem_maximal_trivial_submodule, h, forall_const, true_iff, eq_self_iff_true], },
  { intros h, constructor, intros x m, revert x,
    rw [← mem_maximal_trivial_submodule R L M, h], exact lie_submodule.mem_top m, },
end

variables {R L M N}

/-- `maximal_trivial_submodule` is functorial. -/
def maximal_trivial_hom (f : M →ₗ⁅R,L⁆ N) :
  maximal_trivial_submodule R L M →ₗ⁅R,L⁆ maximal_trivial_submodule R L N :=
{ to_fun    := λ m, ⟨f m, λ x, by
    { have h := congr_arg f (m.property x),
      rw [lie_module_hom.map_zero, lie_module_hom.map_lie] at h, exact h, }⟩,
  map_add'  := λ m n, by simpa,
  map_smul' := λ t m, by simpa,
  map_lie'  := λ x m, by simp, }

@[norm_cast, simp] lemma coe_maximal_trivial_hom_apply
  (f : M →ₗ⁅R,L⁆ N) (m : maximal_trivial_submodule R L M) :
  (maximal_trivial_hom f m : N) = f m :=
rfl

-- Should I just have this as a `≃ₗ[R]` or should I at least have a 'ed version in that form?
/-- The maximal trivial submodules of Lie-equivalent Lie modules are Lie-equivalent. -/
def maximal_trivial_equiv (e : M ≃ₗ⁅R,L⁆ N) :
  maximal_trivial_submodule R L M ≃ₗ⁅R,L⁆ maximal_trivial_submodule R L N :=
{ to_fun    := maximal_trivial_hom (e : M →ₗ⁅R,L⁆ N),
  inv_fun   := maximal_trivial_hom (e.symm : N →ₗ⁅R,L⁆ M),
  left_inv  := λ m, by { ext, simp, },
  right_inv := λ n, by { ext, simp, },
  .. maximal_trivial_hom (e : M →ₗ⁅R,L⁆ N), }

@[simp] lemma maximal_trivial_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
  (maximal_trivial_equiv e).symm = maximal_trivial_equiv e.symm :=
rfl

@[norm_cast, simp] lemma coe_maximal_trivial_equiv_apply
  (e : M ≃ₗ⁅R,L⁆ N) (m : maximal_trivial_submodule R L M) :
  (maximal_trivial_equiv e m : N) = e ↑m :=
rfl

@[simp] lemma maximal_trivial_equiv_of_refl_eq_refl :
  maximal_trivial_equiv (lie_module_equiv.refl : M ≃ₗ⁅R,L⁆ M) = lie_module_equiv.refl :=
by { ext, simp only [coe_maximal_trivial_equiv_apply, lie_module_equiv.refl_apply], }

@[simp] lemma maximal_trivial_equiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
  (maximal_trivial_equiv e).symm = maximal_trivial_equiv e.symm :=
rfl

/-- A linear map between two Lie modules is a morphism of Lie modules iff the Lie algebra action
on it is trivial. -/
def maximal_trivial_linear_map_equiv_lie_module_hom :
  (maximal_trivial_submodule R L (M →ₗ[R] N)) ≃ₗ[R] (M →ₗ⁅R,L⁆ N) :=
{ to_fun    := λ f,
    { map_lie' := λ x m, by
      { have hf : ⁅x, f.val⁆ m = 0, { rw [f.property x, linear_map.zero_apply], },
        rw [bracket_apply, sub_eq_zero, ← linear_map.to_fun_eq_coe] at hf, exact hf.symm, },
      ..f.val, },
  map_add'  := λ f g, by { ext, simp, },
  map_smul' := λ F G, by { ext, simp, },
  inv_fun   := λ F, ⟨F, λ x, by { ext, simp, }⟩,
  left_inv  := λ f, by simp,
  right_inv := λ F, by simp, }

@[simp] lemma coe_maximal_trivial_linear_map_equiv_lie_module_hom
  (f : maximal_trivial_submodule R L (M →ₗ[R] N)) :
  ((maximal_trivial_linear_map_equiv_lie_module_hom f) : M → N) = f :=
by { ext, refl, }

@[simp] lemma coe_maximal_trivial_linear_map_equiv_lie_module_hom_apply
  (f : maximal_trivial_submodule R L (M →ₗ[R] N)) :
  ((maximal_trivial_linear_map_equiv_lie_module_hom f) : M →ₗ[R] N) = (f : M →ₗ[R] N) :=
by { ext, refl, }

@[simp] lemma coe_maximal_trivial_linear_map_equiv_lie_module_hom_symm_apply
  (f : M →ₗ⁅R,L⁆ N) :
  ((maximal_trivial_linear_map_equiv_lie_module_hom.symm f) : M →ₗ[R] N) = (f : M →ₗ[R] N) :=
rfl

end lie_module

namespace lie_algebra

/-- The center of a Lie algebra is the set of elements that commute with everything. It can
be viewed as the maximal trivial submodule of the Lie algebra as a Lie module over itself via the
adjoint representation. -/
abbreviation center : lie_ideal R L := lie_module.maximal_trivial_submodule R L L

instance : is_lie_abelian (center R L) := infer_instance

lemma center_eq_adjoint_kernel : center R L = lie_module.ker R L L :=
begin
  ext y,
  simp only [lie_module.mem_maximal_trivial_submodule, lie_module.mem_ker,
    ← lie_skew _ y, neg_eq_zero],
end

lemma abelian_of_le_center (I : lie_ideal R L) (h : I ≤ center R L) : is_lie_abelian I :=
begin
  rw ← lie_module.trivial_iff_le_maximal_trivial R L L I at h,
  haveI := h, exact lie_ideal.is_lie_abelian_of_trivial R L I,
end

lemma is_lie_abelian_iff_center_eq_top : is_lie_abelian L ↔ center R L = ⊤ :=
lie_module.is_trivial_iff_maximal_trivial_eq_top R L L

end lie_algebra

end center

section ideal_operations

open lie_submodule lie_subalgebra

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (N N' : lie_submodule R L M) (I J : lie_ideal R L)

@[simp] lemma lie_submodule.trivial_lie_oper_zero [lie_module.is_trivial L M] : ⁅I, N⁆ = ⊥ :=
begin
  suffices : ⁅I, N⁆ ≤ ⊥, { exact le_bot_iff.mp this, },
  rw [lie_ideal_oper_eq_span, lie_submodule.lie_span_le],
  rintros m ⟨x, n, h⟩, rw trivial_lie_zero at h, simp [← h],
end

lemma lie_submodule.lie_abelian_iff_lie_self_eq_bot : is_lie_abelian I ↔ ⁅I, I⁆ = ⊥ :=
begin
  simp only [_root_.eq_bot_iff, lie_ideal_oper_eq_span, lie_submodule.lie_span_le,
    lie_submodule.bot_coe, set.subset_singleton_iff, set.mem_set_of_eq, exists_imp_distrib],
  split; intros h,
  { intros z x y hz, rw [← hz, ← coe_bracket, coe_zero_iff_zero], apply h.trivial, },
  { exact ⟨λ x y, by { rw ← coe_zero_iff_zero, apply h _ x y, refl, }⟩, },
end

end ideal_operations
