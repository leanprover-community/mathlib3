/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.pi_instances
import linear_algebra.smodeq
import ring_theory.ideal_operations
import data.padics

/-!
# Completion of a module with respect to an ideal.

In this file we define the notion of Hausdorff and precomplete and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `is_Hausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `is_precomplete I M`: this says that every Cauchy sequence converges.
- `is_adic_complete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorfficiation I M`: this is the universal Hausdorff module with a map from `M`.
- `completion I M`: if `I` is finitely generated, then this is the universal complete module (TODO)
  with a map from `M`. This map is injective iff `M` is Hausdorff and surjective iff `M` is
  precomplete.

-/

open submodule

variables {R : Type*} [comm_ring R] (I : ideal R)
variables (M : Type*) [add_comm_group M] [module R M]
variables {N : Type*} [add_comm_group N] [module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
@[class] def is_Hausdorff : Prop :=
∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
@[class] def is_precomplete : Prop :=
∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : submodule R M)]) →
∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
@[class] def is_adic_complete : Prop :=
is_Hausdorff I M ∧ is_precomplete I M

/-- The Hausdorffification of a module with respect to an ideal. -/
@[reducible] def Hausdorffification : Type* :=
(⨅ n : ℕ, I ^ n • ⊤ : submodule R M).quotient

/-- The completion of a module with respect to an ideal. This is not Hausdorff.
In fact, this is only complete if the ideal is finitely generated. -/
def completion : submodule R (Π n : ℕ, (I ^ n • ⊤ : submodule R M).quotient) :=
{ carrier := { f | ∀ {m n} (h : m ≤ n), liftq _ (mkq _)
    (by { rw ker_mkq, exact smul_mono (ideal.pow_le_pow h) (le_refl _) }) (f n) = f m },
  zero_mem' := λ m n hmn, by rw [pi.zero_apply, pi.zero_apply, linear_map.map_zero],
  add_mem' := λ f g hf hg m n hmn, by rw [pi.add_apply, pi.add_apply,
    linear_map.map_add, hf hmn, hg hmn],
  smul_mem' := λ c f hf m n hmn, by rw [pi.smul_apply, pi.smul_apply, linear_map.map_smul, hf hmn] }

namespace is_Hausdorff

instance bot : is_Hausdorff (⊥ : ideal R) M :=
λ x hx, by simpa only [pow_one ⊥, bot_smul, smodeq.bot] using hx 1

variables {M}
protected theorem subsingleton (h : is_Hausdorff (⊤ : ideal R) M) : subsingleton M :=
⟨λ x y, eq_of_sub_eq_zero $ h (x - y) $ λ n, by { rw [ideal.top_pow, top_smul], exact smodeq.top }⟩
variables (M)

@[priority 100] instance of_subsingleton [subsingleton M] : is_Hausdorff I M :=
λ x _, subsingleton.elim _ _

variables {I M}
theorem infi_pow_smul (h : is_Hausdorff I M) :
  (⨅ n : ℕ, I ^ n • ⊤ : submodule R M) = ⊥ :=
eq_bot_iff.2 $ λ x hx, (mem_bot _).2 $ h x $ λ n, smodeq.zero.2 $
(mem_infi $ λ n : ℕ, I ^ n • ⊤).1 hx n

end is_Hausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
def of : M →ₗ[R] Hausdorffification I M := mkq _

@[elab_as_eliminator]
lemma induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
  (ih : ∀ x, C (of I M x)) : C x :=
quotient.induction_on' x ih

instance : is_Hausdorff I (Hausdorffification I M) :=
λ x, quotient.induction_on' x $ λ x hx, (quotient.mk_eq_zero _).2 $ (mem_infi _).2 $ λ n, begin
  have := comap_map_mkq (⨅ n : ℕ, I ^ n • ⊤ : submodule R M) (I ^ n • ⊤),
  simp only [sup_of_le_right (infi_le (λ n, (I ^ n • ⊤ : submodule R M)) n)] at this,
  rw [← this, map_smul'', mem_comap, map_top, range_mkq, ← smodeq.zero], exact hx n
end

variables {M} [h : is_Hausdorff I N]
include h

/-- universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
liftq _ f $ map_le_iff_le_comap.1 $ h.infi_pow_smul ▸ le_infi (λ n,
le_trans (map_mono $ infi_le _ n) $ by { rw map_smul'', exact smul_mono (le_refl _) le_top })

theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x := rfl

theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
linear_map.ext $ λ _, rfl

end Hausdorffification

namespace is_precomplete

instance bot : is_precomplete (⊥ : ideal R) M :=
begin
  refine λ f hf, ⟨f 1, λ n, _⟩, cases n,
  { rw [pow_zero, ideal.one_eq_top, top_smul], exact smodeq.top },
  specialize hf (nat.le_add_left 1 n),
  rw [pow_one, bot_smul, smodeq.bot] at hf, rw hf
end

instance top : is_precomplete (⊤ : ideal R) M :=
λ f hf, ⟨0, λ n, by { rw [ideal.top_pow, top_smul], exact smodeq.top }⟩

@[priority 100] instance of_subsingleton [subsingleton M] : is_precomplete I M :=
λ f hf, ⟨0, λ n, by rw subsingleton.elim (f n) 0⟩

end is_precomplete

namespace completion

/-- The canonical linear map to the completion. -/
def of : M →ₗ[R] completion I M :=
{ to_fun    := λ x, ⟨λ n, mkq _ x, λ m n hmn, rfl⟩,
  map_add'  := λ x y, rfl,
  map_smul' := λ c x, rfl }

@[simp] lemma of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkq _ x := rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
def eval (n : ℕ) : completion I M →ₗ[R] (I ^ n • ⊤ : submodule R M).quotient :=
{ to_fun    := λ f, f.1 n,
  map_add'  := λ f g, rfl,
  map_smul' := λ c f, rfl }

@[simp] lemma coe_eval (n : ℕ) :
  (eval I M n : completion I M → (I ^ n • ⊤ : submodule R M).quotient) = λ f, f.1 n := rfl

lemma eval_apply (n : ℕ) (f : completion I M) : eval I M n f = f.1 n := rfl

lemma eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkq _ x := rfl

@[simp] lemma eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkq _ := rfl

@[simp] lemma range_eval (n : ℕ) : (eval I M n).range = ⊤ :=
linear_map.range_eq_top.2 $ λ x, quotient.induction_on' x $ λ x, ⟨of I M x, rfl⟩

variables {I M}
@[ext] lemma ext {x y : completion I M} (h : ∀ n, eval I M n x = eval I M n y) : x = y :=
subtype.eq $ funext h
variables (I M)

instance : is_Hausdorff I (completion I M) :=
λ x hx, ext $ λ n, smul_induction_on (smodeq.zero.1 $ hx n)
  (λ r hr x _, ((eval I M n).map_smul r x).symm ▸ quotient.induction_on' (eval I M n x)
    (λ x, smodeq.zero.2 $ smul_mem_smul hr mem_top))
  rfl
  (λ _ _ ih1 ih2, by rw [linear_map.map_add, ih1, ih2, linear_map.map_zero, add_zero])
  (λ c _ ih, by rw [linear_map.map_smul, ih, linear_map.map_zero, smul_zero])

end completion

namespace is_adic_complete

instance bot : is_adic_complete (⊥ : ideal R) M :=
⟨by apply_instance, by apply_instance⟩

protected theorem subsingleton (h : is_adic_complete (⊤ : ideal R) M) : subsingleton M :=
h.1.subsingleton

@[priority 100] instance of_subsingleton [subsingleton M] : is_adic_complete I M :=
⟨by apply_instance, by apply_instance⟩

end is_adic_complete
