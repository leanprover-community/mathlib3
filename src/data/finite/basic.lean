/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.fintype.powerset
import data.fintype.prod
import data.fintype.sigma
import data.fintype.sum
import data.fintype.vector

/-!
# Finite types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove some theorems about `finite` and provide some instances. This typeclass is a
`Prop`-valued counterpart of the typeclass `fintype`. See more details in the file where `finite` is
defined.

## Main definitions

* `fintype.finite`, `finite.of_fintype` creates a `finite` instance from a `fintype` instance. The
  former lemma takes `fintype α` as an explicit argument while the latter takes it as an instance
  argument.
* `fintype.of_finite` noncomputably creates a `fintype` instance from a `finite` instance.

## Implementation notes

There is an apparent duplication of many `fintype` instances in this module,
however they follow a pattern: if a `fintype` instance depends on `decidable`
instances or other `fintype` instances, then we need to "lower" the instance
to be a `finite` instance by removing the `decidable` instances and switching
the `fintype` instances to `finite` instances. These are precisely the ones
that cannot be inferred using `finite.of_fintype`. (However, when using
`open_locale classical` or the `classical` tactic the instances relying only
on `decidable` instances will give `finite` instances.) In the future we might
consider writing automation to create these "lowered" instances.

## Tags

finiteness, finite types
-/

noncomputable theory
open_locale classical

variables {α β γ : Type*}

namespace finite

@[priority 100] -- see Note [lower instance priority]
instance of_subsingleton {α : Sort*} [subsingleton α] : finite α :=
of_injective (function.const α ()) $ function.injective_of_subsingleton _

@[nolint instance_priority] -- Higher priority for `Prop`s
instance prop (p : Prop) : finite p := finite.of_subsingleton

instance [finite α] [finite β] : finite (α × β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, apply_instance }

instance {α β : Sort*} [finite α] [finite β] : finite (pprod α β) :=
of_equiv _ equiv.pprod_equiv_prod_plift.symm

lemma prod_left (β) [finite (α × β)] [nonempty β] : finite α :=
of_surjective (prod.fst : α × β → α) prod.fst_surjective

lemma prod_right (α) [finite (α × β)] [nonempty α] : finite β :=
of_surjective (prod.snd : α × β → β) prod.snd_surjective

instance [finite α] [finite β] : finite (α ⊕ β) :=
by { haveI := fintype.of_finite α, haveI := fintype.of_finite β, apply_instance }

lemma sum_left (β) [finite (α ⊕ β)] : finite α :=
of_injective (sum.inl : α → α ⊕ β) sum.inl_injective

lemma sum_right (α) [finite (α ⊕ β)] : finite β :=
of_injective (sum.inr : β → α ⊕ β) sum.inr_injective

instance {β : α → Type*} [finite α] [Π a, finite (β a)] : finite (Σ a, β a) :=
by { letI := fintype.of_finite α, letI := λ a, fintype.of_finite (β a), apply_instance }

instance {ι : Sort*} {π : ι → Sort*} [finite ι] [Π i, finite (π i)] : finite (Σ' i, π i) :=
of_equiv _ (equiv.psigma_equiv_sigma_plift π).symm

instance [finite α] : finite (set α) := by { casesI nonempty_fintype α, apply_instance }

end finite

/-- This instance also provides `[finite s]` for `s : set α`. -/
instance subtype.finite {α : Sort*} [finite α] {p : α → Prop} : finite {x // p x} :=
finite.of_injective coe subtype.coe_injective

instance pi.finite {α : Sort*} {β : α → Sort*} [finite α] [∀ a, finite (β a)] : finite (Π a, β a) :=
begin
  haveI := fintype.of_finite (plift α),
  haveI := λ a, fintype.of_finite (plift (β a)),
  exact finite.of_equiv (Π (a : plift α), plift (β (equiv.plift a)))
    (equiv.Pi_congr equiv.plift (λ _, equiv.plift)),
end

instance vector.finite {α : Type*} [finite α] {n : ℕ} : finite (vector α n) :=
by { haveI := fintype.of_finite α, apply_instance }

instance quot.finite {α : Sort*} [finite α] (r : α → α → Prop) : finite (quot r) :=
finite.of_surjective _ (surjective_quot_mk r)

instance quotient.finite {α : Sort*} [finite α] (s : setoid α) : finite (quotient s) :=
quot.finite _

instance function.embedding.finite {α β : Sort*} [finite β] : finite (α ↪ β) :=
begin
  casesI is_empty_or_nonempty (α ↪ β) with _ h,
  { apply_instance, },
  { refine h.elim (λ f, _),
    haveI : finite α := finite.of_injective _ f.injective,
    exact finite.of_injective _ fun_like.coe_injective },
end

instance equiv.finite_right {α β : Sort*} [finite β] : finite (α ≃ β) :=
finite.of_injective equiv.to_embedding $ λ e₁ e₂ h, equiv.ext $
  by convert fun_like.congr_fun h

instance equiv.finite_left {α β : Sort*} [finite α] : finite (α ≃ β) :=
finite.of_equiv _ ⟨equiv.symm, equiv.symm, equiv.symm_symm, equiv.symm_symm⟩

instance [finite α] {n : ℕ} : finite (sym α n) :=
by { haveI := fintype.of_finite α, apply_instance }
