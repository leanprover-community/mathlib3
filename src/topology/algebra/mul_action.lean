/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.add_torsor
import topology.algebra.constructions
import group_theory.group_action.prod
import topology.algebra.const_mul_action

/-!
# Continuous monoid action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M X` if `M` acts on
`X` and the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/

open_locale topology pointwise
open filter

/-- Class `has_continuous_smul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class has_continuous_smul (M X : Type*) [has_smul M X]
  [topological_space M] [topological_space X] : Prop :=
(continuous_smul : continuous (λp : M × X, p.1 • p.2))

export has_continuous_smul (continuous_smul)

/-- Class `has_continuous_vadd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class has_continuous_vadd (M X : Type*) [has_vadd M X]
  [topological_space M] [topological_space X] : Prop :=
(continuous_vadd : continuous (λp : M × X, p.1 +ᵥ p.2))

export has_continuous_vadd (continuous_vadd)

attribute [to_additive] has_continuous_smul

section main

variables {M X Y α : Type*} [topological_space M] [topological_space X] [topological_space Y]

section has_smul

variables [has_smul M X] [has_continuous_smul M X]

@[priority 100, to_additive] instance has_continuous_smul.has_continuous_const_smul :
  has_continuous_const_smul M X :=
{ continuous_const_smul := λ _, continuous_smul.comp (continuous_const.prod_mk continuous_id) }

@[to_additive]
lemma filter.tendsto.smul {f : α → M} {g : α → X} {l : filter α} {c : M} {a : X}
  (hf : tendsto f l (𝓝 c)) (hg : tendsto g l (𝓝 a)) :
  tendsto (λ x, f x • g x) l (𝓝 $ c • a) :=
(continuous_smul.tendsto _).comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma filter.tendsto.smul_const {f : α → M} {l : filter α} {c : M}
  (hf : tendsto f l (𝓝 c)) (a : X) :
  tendsto (λ x, (f x) • a) l (𝓝 (c • a)) :=
hf.smul tendsto_const_nhds

variables {f : Y → M} {g : Y → X} {b : Y} {s : set Y}

@[to_additive]
lemma continuous_within_at.smul (hf : continuous_within_at f s b)
  (hg : continuous_within_at g s b) :
  continuous_within_at (λ x, f x • g x) s b :=
hf.smul hg

@[to_additive]
lemma continuous_at.smul (hf : continuous_at f b) (hg : continuous_at g b) :
  continuous_at (λ x, f x • g x) b :=
hf.smul hg

@[to_additive]
lemma continuous_on.smul (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

@[continuity, to_additive]
lemma continuous.smul (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x • g x) :=
continuous_smul.comp (hf.prod_mk hg)

/-- If a scalar action is central, then its right action is continuous when its left action is. -/
@[to_additive "If an additive action is central, then its right action is continuous when its left
action is."]
instance has_continuous_smul.op [has_smul Mᵐᵒᵖ X] [is_central_scalar M X] :
  has_continuous_smul Mᵐᵒᵖ X :=
⟨ suffices continuous (λ p : M × X, mul_opposite.op p.fst • p.snd),
  from this.comp (mul_opposite.continuous_unop.prod_map continuous_id),
  by simpa only [op_smul_eq_smul] using (continuous_smul : continuous (λ p : M × X, _)) ⟩

@[to_additive] instance mul_opposite.has_continuous_smul : has_continuous_smul M Xᵐᵒᵖ :=
⟨mul_opposite.continuous_op.comp $ continuous_smul.comp $
  continuous_id.prod_map mul_opposite.continuous_unop⟩

end has_smul

section monoid

variables [monoid M] [mul_action M X] [has_continuous_smul M X]

@[to_additive] instance units.has_continuous_smul : has_continuous_smul Mˣ X :=
{ continuous_smul :=
    show continuous ((λ p : M × X, p.fst • p.snd) ∘ (λ p : Mˣ × X, (p.1, p.2))),
    from continuous_smul.comp ((units.continuous_coe.comp continuous_fst).prod_mk continuous_snd) }

end monoid

@[to_additive]
instance [has_smul M X] [has_smul M Y] [has_continuous_smul M X]
  [has_continuous_smul M Y] :
  has_continuous_smul M (X × Y) :=
⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
  (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*}
  [∀ i, topological_space (γ i)] [Π i, has_smul M (γ i)] [∀ i, has_continuous_smul M (γ i)] :
  has_continuous_smul M (Π i, γ i) :=
⟨continuous_pi $ λ i,
  (continuous_fst.smul continuous_snd).comp $
    continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

end main

section lattice_ops

variables {ι : Sort*} {M X : Type*} [topological_space M] [has_smul M X]

@[to_additive] lemma has_continuous_smul_Inf {ts : set (topological_space X)}
  (h : Π t ∈ ts, @has_continuous_smul M X _ _ t) :
  @has_continuous_smul M X _ _ (Inf ts) :=
{ continuous_smul :=
  begin
    rw ← @Inf_singleton _ _ ‹topological_space M›,
    exact continuous_Inf_rng.2 (λ t ht, continuous_Inf_dom₂ (eq.refl _) ht
      (@has_continuous_smul.continuous_smul _ _ _ _ t (h t ht)))
  end }

@[to_additive] lemma has_continuous_smul_infi {ts' : ι → topological_space X}
  (h : Π i, @has_continuous_smul M X _ _ (ts' i)) :
  @has_continuous_smul M X _ _ (⨅ i, ts' i) :=
has_continuous_smul_Inf $ set.forall_range_iff.mpr h

@[to_additive] lemma has_continuous_smul_inf {t₁ t₂ : topological_space X}
  [@has_continuous_smul M X _ _ t₁] [@has_continuous_smul M X _ _ t₂] :
  @has_continuous_smul M X _ _ (t₁ ⊓ t₂) :=
by { rw inf_eq_infi, refine has_continuous_smul_infi (λ b, _), cases b; assumption }

end lattice_ops

section add_torsor

variables (G : Type*) (P : Type*) [add_group G] [add_torsor G P] [topological_space G]
variables [preconnected_space G] [topological_space P] [has_continuous_vadd G P]
include G

/-- An `add_torsor` for a connected space is a connected space. This is not an instance because
it loops for a group as a torsor over itself. -/
protected lemma add_torsor.connected_space : connected_space P :=
{ is_preconnected_univ :=
    begin
      convert is_preconnected_univ.image ((equiv.vadd_const (classical.arbitrary P)) : G → P)
                                         (continuous_id.vadd continuous_const).continuous_on,
      rw [set.image_univ, equiv.range_eq_univ]
    end,
  to_nonempty := infer_instance }

end add_torsor
