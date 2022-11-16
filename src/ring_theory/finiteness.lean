/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.algebra.restrict_scalars
import group_theory.finiteness
import ring_theory.noetherian

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `module.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.

-/

open function (surjective)
open_locale big_operators

section module_and_algebra

variables (R A B M N : Type*)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class module.finite [semiring R] [add_comm_monoid M] [module R M] :
  Prop := (out : (⊤ : submodule R M).fg)

namespace module

variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]

lemma finite_def {R M} [semiring R] [add_comm_monoid M] [module R M] :
  finite R M ↔ (⊤ : submodule R M).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian.finite [is_noetherian R M] : finite R M :=
⟨is_noetherian.noetherian ⊤⟩

namespace finite
open _root_.submodule set

lemma iff_add_monoid_fg {M : Type*} [add_comm_monoid M] : module.finite ℕ M ↔ add_monoid.fg M :=
⟨λ h, add_monoid.fg_def.2 $ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_submonoid_fg ⊤).2 (add_monoid.fg_def.1 h)⟩

lemma iff_add_group_fg {G : Type*} [add_comm_group G] : module.finite ℤ G ↔ add_group.fg G :=
⟨λ h, add_group.fg_def.2 $ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_subgroup_fg ⊤).2 (add_group.fg_def.1 h)⟩

variables {R M N}

lemma exists_fin [finite R M] : ∃ (n : ℕ) (s : fin n → M), span R (range s) = ⊤ :=
submodule.fg_iff_exists_fin_generating_family.mp out

lemma of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) :
  finite R N :=
⟨begin
  rw [← linear_map.range_eq_top.2 hf, ← submodule.map_top],
  exact hM.1.map f
end⟩

lemma of_injective [is_noetherian R N] (f : M →ₗ[R] N)
  (hf : function.injective f) : finite R M :=
⟨fg_of_injective f hf⟩

variables (R)

instance self : finite R R :=
⟨⟨{1}, by simpa only [finset.coe_singleton] using ideal.span_singleton_one⟩⟩

variable (M)

lemma of_restrict_scalars_finite (R A M : Type*) [comm_semiring R] [semiring A] [add_comm_monoid M]
  [module R M] [module A M] [algebra R A] [is_scalar_tower R A M] [hM : finite R M] :
  finite A M :=
begin
  rw [finite_def, fg_def] at hM ⊢,
  obtain ⟨S, hSfin, hSgen⟩ := hM,
  refine ⟨S, hSfin, eq_top_iff.2 _⟩,
  have := submodule.span_le_restrict_scalars R A S,
  rw hSgen at this,
  exact this
end

variables {R M}

instance prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
⟨begin
  rw ← submodule.prod_top,
  exact hM.1.prod hN.1
end⟩

instance pi {ι : Type*} {M : ι → Type*} [_root_.finite ι] [Π i, add_comm_monoid (M i)]
  [Π i, module R (M i)] [h : ∀ i, finite R (M i)] : finite R (Π i, M i) :=
⟨begin
  rw ← submodule.pi_top,
  exact submodule.fg_pi (λ i, (h i).1),
end⟩

lemma equiv [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
of_surjective (e : M →ₗ[R] N) e.surjective

section algebra

lemma trans {R : Type*} (A B : Type*) [comm_semiring R] [comm_semiring A] [algebra R A]
  [semiring B] [algebra R B] [algebra A B] [is_scalar_tower R A B] :
  ∀ [finite R A] [finite A B], finite R B
| ⟨⟨s, hs⟩⟩ ⟨⟨t, ht⟩⟩ := ⟨submodule.fg_def.2
  ⟨set.image2 (•) (↑s : set A) (↑t : set B),
    set.finite.image2 _ s.finite_to_set t.finite_to_set,
    by rw [set.image2_smul, submodule.span_smul hs (↑t : set B),
      ht, submodule.restrict_scalars_top]⟩⟩

end algebra

end finite

end module

instance module.finite.base_change [comm_semiring R] [semiring A] [algebra R A]
  [add_comm_monoid M] [module R M] [h : module.finite R M] :
  module.finite A (tensor_product R A M) :=
begin
  classical,
  obtain ⟨s, hs⟩ := h.out,
  refine ⟨⟨s.image (tensor_product.mk R A M 1), eq_top_iff.mpr $ λ x _, _⟩⟩,
  apply tensor_product.induction_on x,
  { exact zero_mem _ },
  { intros x y,
    rw [finset.coe_image, ← submodule.span_span_of_tower R, submodule.span_image, hs,
      submodule.map_top, linear_map.range_coe],
      change _ ∈ submodule.span A (set.range $ tensor_product.mk R A M 1),
    rw [← mul_one x, ← smul_eq_mul, ← tensor_product.smul_tmul'],
    exact submodule.smul_mem _ x (submodule.subset_span $ set.mem_range_self y) },
  { exact λ _ _, submodule.add_mem _ }
end

instance module.finite.tensor_product [comm_semiring R]
  [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  [hM : module.finite R M] [hN : module.finite R N] : module.finite R (tensor_product R M N) :=
{ out := (tensor_product.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out) }

namespace algebra

variables [comm_ring R] [comm_ring A] [algebra R A] [comm_ring B] [algebra R B]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]

end algebra

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop :=
by letI : algebra A B := f.to_algebra; exact module.finite A B

namespace finite

variables (A)

lemma id : finite (ring_hom.id A) := module.finite.self A

variables {A}

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite :=
begin
  letI := f.to_algebra,
  exact module.finite.of_surjective (algebra.of_id A B).to_linear_map hf
end

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
@module.finite.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).finite) : g.finite :=
begin
  letI := f.to_algebra,
  letI := g.to_algebra,
  letI := (g.comp f).to_algebra,
  letI : is_scalar_tower A B C := restrict_scalars.is_scalar_tower A B C,
  letI : module.finite A C := h,
  exact module.finite.of_restrict_scalars_finite A B C
end

end finite

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite

namespace finite

variables (R A)

lemma id : finite (alg_hom.id R A) := ring_hom.finite.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
ring_hom.finite.comp hg hf

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
ring_hom.finite.of_surjective f hf

lemma of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).finite) : g.finite :=
ring_hom.finite.of_comp_finite h

end finite

end alg_hom
