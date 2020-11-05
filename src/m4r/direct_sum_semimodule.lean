/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Direct sum of modules over commutative rings, indexed by a discrete type.
-/
import  m4r.direct_sum2
import linear_algebra.basic

/-!
# Direct sum of modules over commutative rings, indexed by a discrete type.

This file provides constructors for finite direct sums of modules.
It provides a construction of the direct sum using the universal property and proves
its uniqueness.

## Implementation notes

All of this file assumes that
* `R` is a commutative ring,
* `ι` is a discrete type,
* `S` is a finite set in `ι`,
* `M` is a family of `R` semimodules indexed over `ι`.
-/

universes u v w u₁

variables (R : Type u) [semiring R]
variables (ι : Type v) [dec_ι : decidable_eq ι] (M : ι → Type w)
variables [Π i, add_comm_monoid (M i)] [Π i, semimodule R (M i)]
include R

namespace direct_sum2
open_locale direct_sum

variables {R ι M}
instance : semimodule R (⨁ i, M i) := dfinsupp.to_semimodule

include dec_ι

variables R ι M
/-- Create the direct sum given a family `M` of `R` semimodules indexed over `ι`. -/
def lmk : Π s : finset ι, (Π i : (↑s : set ι), M i.val) →ₗ[R] (⨁ i, M i) :=
dfinsupp.lmk M R

/-- Inclusion of each component into the direct sum. -/
def lof : Π i : ι, M i →ₗ[R] (⨁ i, M i) :=
dfinsupp.lsingle M R
variables {ι M}

lemma single_eq_lof (i : ι) (b : M i) :
  dfinsupp.single i b = lof R ι M i b := rfl

/-- Scalar multiplication commutes with direct sums. -/
theorem mk_smul (s : finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
(lmk R ι M s).map_smul c x

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
(lof R ι M i).map_smul c x

variables {N : Type u₁} [add_comm_monoid N] [semimodule R N]
variables (φ : Π i, M i →ₗ[R] N)

variables (ι N φ)
/-- The linear map constructed using the universal property of the coproduct. -/
def to_semimodule : (⨁ i, M i) →ₗ[R] N :=
{ to_fun := to_monoid (λ i, φ i),
  map_add' := to_monoid_add _,
  map_smul' := λ c x, direct_sum2.induction_on x
    (by rw [smul_zero, to_monoid_zero, smul_zero])
    (λ i x, by rw [← of_smul, to_monoid_of, to_monoid_of, (φ i).map_smul c x])
    (λ x y ihx ihy, by rw [smul_add, to_monoid_add, ihx, ihy, to_monoid_add, smul_add]) }

variables {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp] lemma to_semimodule_lof (i) (x : M i) : to_semimodule R ι N φ (lof R ι M i x) = φ i x :=
to_monoid_of (λ i, φ i) i x

variables (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem to_semimodule.unique (f : ⨁ i, M i) : ψ f = to_semimodule R ι N (λ i, ψ.comp $ lof R ι M i) f :=
to_monoid.unique ψ f

variables {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

theorem to_semimodule.ext (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) (f : ⨁ i, M i) :
  ψ f = ψ' f :=
by rw [to_semimodule.unique R ψ, to_semimodule.unique R ψ', funext H]

/--
The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map.
-/
def lset_to_set (S T : set ι) (H : S ⊆ T) :
  (⨁ (i : S), M i) →ₗ (⨁ (i : T), M i) :=
to_semimodule R _ _ $ λ i, lof R T (M ∘ @subtype.val _ T) ⟨i.1, H i.2⟩

omit dec_ι

/-- The natural linear equivalence between `⨁ _ : punit, M` and `M`. -/
-- TODO: generalize this to arbitrary index type `ι` with `unique ι`
protected def lid (M : Type v) [add_comm_monoid M] [semimodule R M] :
  (⨁ (_ : punit), M) ≃ₗ M :=
{ .. direct_sum2.id M,
  .. to_semimodule R punit M (λ i, linear_map.id) }

variables (ι M)
/-- The projection map onto one component, as a linear map. -/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
{ to_fun := λ f, f i,
  map_add' := λ _ _, dfinsupp.add_apply,
  map_smul' := λ _ _, dfinsupp.smul_apply }

variables {ι M}

lemma apply_eq_component (f : ⨁ i, M i) (i : ι) :
  f i = component R ι M i f := rfl

@[ext] lemma ext {f g : ⨁ i, M i}
  (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
dfinsupp.ext h

lemma ext_iff {f g : ⨁ i, M i} : f = g ↔
  ∀ i, component R ι M i f = component R ι M i g :=
⟨λ h _, by rw h, ext R⟩

include dec_ι

@[simp] lemma lof_apply (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
by rw [lof, dfinsupp.lsingle_apply, dfinsupp.single_apply, dif_pos rfl]

@[simp] lemma component.lof_self (i : ι) (b : M i) :
  component R ι M i ((lof R ι M i) b) = b :=
lof_apply R i b

lemma component.of (i j : ι) (b : M j) :
  component R ι M i ((lof R ι M j) b) =
  if h : j = i then eq.rec_on h b else 0 :=
dfinsupp.single_apply

end direct_sum2
