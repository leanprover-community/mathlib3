/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.measure.ae_measurable

/-!
# Typeclasses for measurability of lattice operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define classes `has_measurable_sup` and `has_measurable_inf` and prove dot-style
lemmas (`measurable.sup`, `ae_measurable.sup` etc). For binary operations we define two typeclasses:

- `has_measurable_sup` says that both left and right sup are measurable;
- `has_measurable_sup₂` says that `λ p : α × α, p.1 ⊔ p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_sup₂`
etc require `α` to have a second countable topology.

For instances relating, e.g., `has_continuous_sup` to `has_measurable_sup` see file
`measure_theory.borel_space`.

## Tags

measurable function, lattice operation

-/

open measure_theory

/-- We say that a type `has_measurable_sup` if `((⊔) c)` and `(⊔ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊔)` see `has_measurable_sup₂`. -/
class has_measurable_sup (M : Type*) [measurable_space M] [has_sup M] : Prop :=
(measurable_const_sup : ∀ c : M, measurable ((⊔) c))
(measurable_sup_const : ∀ c : M, measurable (⊔ c))

/-- We say that a type `has_measurable_sup₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_sup`. -/
class has_measurable_sup₂ (M : Type*) [measurable_space M] [has_sup M] : Prop :=
(measurable_sup : measurable (λ p : M × M, p.1 ⊔ p.2))

export has_measurable_sup₂ (measurable_sup)
  has_measurable_sup (measurable_const_sup measurable_sup_const)

/-- We say that a type `has_measurable_inf` if `((⊓) c)` and `(⊓ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (⊓)` see `has_measurable_inf₂`. -/
class has_measurable_inf (M : Type*) [measurable_space M] [has_inf M] : Prop :=
(measurable_const_inf : ∀ c : M, measurable ((⊓) c))
(measurable_inf_const : ∀ c : M, measurable (⊓ c))

/-- We say that a type `has_measurable_inf₂` if `uncurry (⊔)` is a measurable functions.
For a typeclass assuming measurability of `((⊔) c)` and `(⊔ c)` see `has_measurable_inf`. -/
class has_measurable_inf₂ (M : Type*) [measurable_space M] [has_inf M] : Prop :=
(measurable_inf : measurable (λ p : M × M, p.1 ⊓ p.2))

export has_measurable_inf₂ (measurable_inf)
  has_measurable_inf (measurable_const_inf measurable_inf_const)

variables {M : Type*} [measurable_space M]

section order_dual

@[priority 100]
instance [has_inf M] [has_measurable_inf M] : has_measurable_sup Mᵒᵈ :=
⟨@measurable_const_inf M _ _ _, @measurable_inf_const M _ _ _⟩

@[priority 100]
instance [has_sup M] [has_measurable_sup M] : has_measurable_inf Mᵒᵈ :=
⟨@measurable_const_sup M _ _ _, @measurable_sup_const M _ _ _⟩

@[priority 100]
instance [has_inf M] [has_measurable_inf₂ M] : has_measurable_sup₂ Mᵒᵈ :=
⟨@measurable_inf M _ _ _⟩

@[priority 100]
instance [has_sup M] [has_measurable_sup₂ M] : has_measurable_inf₂ Mᵒᵈ :=
⟨@measurable_sup M _ _ _⟩

end order_dual

variables {α : Type*} {m : measurable_space α} {μ : measure α} {f g : α → M}
include m

section sup
variables [has_sup M]

section measurable_sup
variables [has_measurable_sup M]

@[measurability]
lemma measurable.const_sup (hf : measurable f) (c : M) : measurable (λ x, c ⊔ f x) :=
(measurable_const_sup c).comp hf

@[measurability]
lemma ae_measurable.const_sup (hf : ae_measurable f μ) (c : M) : ae_measurable (λ x, c ⊔ f x) μ :=
(has_measurable_sup.measurable_const_sup c).comp_ae_measurable hf

@[measurability]
lemma measurable.sup_const (hf : measurable f) (c : M) : measurable (λ x, f x ⊔ c) :=
(measurable_sup_const c).comp hf

@[measurability]
lemma ae_measurable.sup_const (hf : ae_measurable f μ) (c : M) :
  ae_measurable (λ x, f x ⊔ c) μ :=
(measurable_sup_const c).comp_ae_measurable hf

end measurable_sup

section measurable_sup₂
variables [has_measurable_sup₂ M]

@[measurability]
lemma measurable.sup' (hf : measurable f) (hg : measurable g) : measurable (f ⊔ g) :=
measurable_sup.comp (hf.prod_mk hg)

@[measurability]
lemma measurable.sup (hf : measurable f) (hg : measurable g) : measurable (λ a, f a ⊔ g a) :=
measurable_sup.comp (hf.prod_mk hg)

@[measurability]
lemma ae_measurable.sup' (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (f ⊔ g) μ :=
measurable_sup.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
lemma ae_measurable.sup (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, f a ⊔ g a) μ :=
measurable_sup.comp_ae_measurable (hf.prod_mk hg)

omit m
@[priority 100]
instance has_measurable_sup₂.to_has_measurable_sup : has_measurable_sup M :=
⟨λ c, measurable_const.sup measurable_id, λ c, measurable_id.sup measurable_const⟩
include m

end measurable_sup₂

end sup

section inf
variables [has_inf M]

section measurable_inf
variables [has_measurable_inf M]

@[measurability]
lemma measurable.const_inf (hf : measurable f) (c : M) :
  measurable (λ x, c ⊓ f x) :=
(measurable_const_inf c).comp hf

@[measurability]
lemma ae_measurable.const_inf (hf : ae_measurable f μ) (c : M) :
  ae_measurable (λ x, c ⊓ f x) μ :=
(has_measurable_inf.measurable_const_inf c).comp_ae_measurable hf

@[measurability]
lemma measurable.inf_const (hf : measurable f) (c : M) :
  measurable (λ x, f x ⊓ c) :=
(measurable_inf_const c).comp hf

@[measurability]
lemma ae_measurable.inf_const (hf : ae_measurable f μ) (c : M) :
  ae_measurable (λ x, f x ⊓ c) μ :=
(measurable_inf_const c).comp_ae_measurable hf

end measurable_inf

section measurable_inf₂
variables [has_measurable_inf₂ M]

@[measurability]
lemma measurable.inf' (hf : measurable f) (hg : measurable g) : measurable (f ⊓ g) :=
measurable_inf.comp (hf.prod_mk hg)

@[measurability]
lemma measurable.inf (hf : measurable f) (hg : measurable g) : measurable (λ a, f a ⊓ g a) :=
measurable_inf.comp (hf.prod_mk hg)

@[measurability]
lemma ae_measurable.inf' (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (f ⊓ g) μ :=
measurable_inf.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
lemma ae_measurable.inf (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, f a ⊓ g a) μ :=
measurable_inf.comp_ae_measurable (hf.prod_mk hg)

omit m
@[priority 100]
instance has_measurable_inf₂.to_has_measurable_inf : has_measurable_inf M :=
⟨λ c, measurable_const.inf measurable_id, λ c, measurable_id.inf measurable_const⟩
include m

end measurable_inf₂

end inf

section semilattice_sup

open finset

variables {δ : Type*} [measurable_space δ] [semilattice_sup α] [has_measurable_sup₂ α]

@[measurability] lemma finset.measurable_sup' {ι : Type*} {s : finset ι} (hs : s.nonempty)
  {f : ι → δ → α} (hf : ∀ n ∈ s, measurable (f n)) :
  measurable (s.sup' hs f) :=
finset.sup'_induction hs _ (λ f hf g hg, hf.sup hg) (λ n hn, hf n hn)

@[measurability] lemma finset.measurable_range_sup'
  {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, measurable (f k)) :
  measurable ((range (n + 1)).sup' nonempty_range_succ f) :=
begin
  simp_rw ← nat.lt_succ_iff at hf,
  refine finset.measurable_sup' _ _,
  simpa [finset.mem_range],
end

@[measurability] lemma finset.measurable_range_sup''
  {f : ℕ → δ → α} {n : ℕ} (hf : ∀ k ≤ n, measurable (f k)) :
  measurable (λ x, (range (n + 1)).sup' nonempty_range_succ (λ k, f k x)) :=
begin
  convert finset.measurable_range_sup' hf,
  ext x,
  simp,
end

end semilattice_sup
