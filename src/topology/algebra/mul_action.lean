/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.monoid
import algebra.module.prod
import topology.homeomorph

/-!
# Continuous monoid action

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M α` if `M` acts on
`α` and the map `(c, x) ↦ c • x` is continuous on `M × α`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M α` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × α`;
* `homeomorph.smul_of_unit`: scalar multiplication by a unit of `M` as a homeomorphism of `α`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `α` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `α`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `α`
  is a homeomorphism of `α`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/

open_locale topological_space
open filter

/-- Class `has_continuous_smul M α` says that the scalar multiplication `(•) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class has_continuous_smul (M α : Type*) [has_scalar M α]
  [topological_space M] [topological_space α] : Prop :=
(continuous_smul : continuous (λp : M × α, p.1 • p.2))

export has_continuous_smul (continuous_smul)

variables {M α β : Type*} [topological_space M] [topological_space α]

section has_scalar

variables [has_scalar M α] [has_continuous_smul M α]

lemma filter.tendsto.smul {f : β → M} {g : β → α} {l : filter β} {c : M} {a : α}
  (hf : tendsto f l (𝓝 c)) (hg : tendsto g l (𝓝 a)) :
  tendsto (λ x, f x • g x) l (𝓝 $ c • a) :=
(continuous_smul.tendsto _).comp (hf.prod_mk_nhds hg)

lemma filter.tendsto.const_smul {f : β → α} {l : filter β} {a : α} (hf : tendsto f l (𝓝 a))
  (c : M) :
  tendsto (λ x, c • f x) l (𝓝 (c • a)) :=
tendsto_const_nhds.smul hf

variables [topological_space β] {f : β → M} {g : β → α} {b : β} {s : set β}

lemma continuous_within_at.smul (hf : continuous_within_at f s b) (hg : continuous_within_at g s b) :
  continuous_within_at (λ x, f x • g x) s b :=
hf.smul hg

lemma continuous_within_at.const_smul (hg : continuous_within_at g s b) (c : M) :
  continuous_within_at (λ x, c • g x) s b :=
hg.const_smul c

lemma continuous_at.smul (hf : continuous_at f b) (hg : continuous_at g b) :
  continuous_at (λ x, f x • g x) b :=
hf.smul hg

lemma continuous_at.const_smul (hg : continuous_at g b) (c : M) :
  continuous_at (λ x, c • g x) b :=
hg.const_smul c

lemma continuous_on.smul (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

lemma continuous_on.const_smul (hg : continuous_on g s) (c : M) :
  continuous_on (λ x, c • g x) s :=
λ x hx, (hg x hx).const_smul c

@[continuity]
lemma continuous.smul (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x • g x) :=
continuous_smul.comp (hf.prod_mk hg)

lemma continuous.const_smul (hg : continuous g) (c : M) :
  continuous (λ x, c • g x) :=
continuous_smul.comp (continuous_const.prod_mk hg)

end has_scalar

section monoid

variables [monoid M] [mul_action M α] [has_continuous_smul M α]

lemma units.tendsto_const_smul_iff {f : β → α} {l : filter β} {a : α} (u : units M) :
  tendsto (λ x, (u : M) • f x) l (𝓝 $ (u : M) • a) ↔ tendsto f l (𝓝 a) :=
⟨λ h, by simpa only [u.inv_smul_smul] using h.const_smul ((u⁻¹ : units M) : M),
  λ h, h.const_smul _⟩

lemma is_unit.tendsto_const_smul_iff {f : β → α} {l : filter β} {a : α} {c : M} (hc : is_unit c) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
let ⟨u, hu⟩ := hc in hu ▸ u.tendsto_const_smul_iff

variables [topological_space β] {f : β → α} {b : β} {c : M} {s : set β}

lemma is_unit.continuous_within_at_const_smul_iff (hc : is_unit c) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
hc.tendsto_const_smul_iff

lemma is_unit.continuous_on_const_smul_iff (hc : is_unit c) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
forall_congr $ λ b, forall_congr $ λ hb, hc.continuous_within_at_const_smul_iff

lemma is_unit.continuous_at_const_smul_iff (hc : is_unit c) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
hc.tendsto_const_smul_iff

lemma is_unit.continuous_const_smul_iff (hc : is_unit c) :
  continuous (λ x, c • f x) ↔ continuous f :=
by simp only [continuous_iff_continuous_at, hc.continuous_at_const_smul_iff]

/-- Scalar multiplication by a unit of a monoid `M` acting on `α` is a homeomorphism from `α`
to itself. -/
protected def homeomorph.smul_of_unit (u : units M) : α ≃ₜ α :=
{ to_equiv := units.smul_perm_hom u,
  continuous_to_fun  := continuous_id.const_smul _,
  continuous_inv_fun := continuous_id.const_smul _ }

lemma is_unit.is_open_map_smul (hc : is_unit c) : is_open_map (λ x : α, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ (homeomorph.smul_of_unit u).is_open_map

lemma is_unit.is_closed_map_smul (hc : is_unit c) : is_closed_map (λ x : α, c • x) :=
let ⟨u, hu⟩ := hc in hu ▸ (homeomorph.smul_of_unit u).is_closed_map

end monoid

section group_with_zero

variables {G₀ : Type*} [topological_space G₀] [group_with_zero G₀] [mul_action G₀ α]
  [has_continuous_smul G₀ α]

lemma tendsto_const_smul_iff' {f : β → α} {l : filter β} {a : α} {c : G₀} (hc : c ≠ 0) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
(is_unit.mk0 c hc).tendsto_const_smul_iff

variables [topological_space β] {f : β → α} {b : β} {c : G₀} {s : set β}

lemma continuous_within_at_const_smul_iff' (hc : c ≠ 0) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
(is_unit.mk0 c hc).tendsto_const_smul_iff

lemma continuous_on_const_smul_iff' (hc : c ≠ 0) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
(is_unit.mk0 c hc).continuous_on_const_smul_iff

lemma continuous_at_const_smul_iff' (hc : c ≠ 0) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
(is_unit.mk0 c hc).continuous_at_const_smul_iff

lemma continuous_const_smul_iff' (hc : c ≠ 0) :
  continuous (λ x, c • f x) ↔ continuous f :=
(is_unit.mk0 c hc).continuous_const_smul_iff

/-- Scalar multiplication by a non-zero element of a group with zero acting on `α` is a
homeomorphism from `α` onto itself. -/
protected def homeomorph.smul_of_ne_zero (c : G₀) (hc : c ≠ 0) : α ≃ₜ α :=
homeomorph.smul_of_unit (units.mk0 c hc)

lemma is_open_map_smul' {c : G₀} (hc : c ≠ 0) : is_open_map (λ x : α, c • x) :=
(is_unit.mk0 c hc).is_open_map_smul

/-- `smul` is a closed map in the second argument.

The lemma that `smul` is a closed map in the first argument (for a normed space over a complete
normed field) is `is_closed_map_smul_left` in `analysis.normed_space.finite_dimension`. -/
lemma is_closed_map_smul' {c : G₀} (hc : c ≠ 0) : is_closed_map (λ x : α, c • x) :=
(is_unit.mk0 c hc).is_closed_map_smul

end group_with_zero

section group

variables {G : Type*} [topological_space G] [group G] [mul_action G α]
  [has_continuous_smul G α]

lemma tendsto_const_smul_iff {f : β → α} {l : filter β} {a : α} (c : G) :
  tendsto (λ x, c • f x) l (𝓝 $ c • a) ↔ tendsto f l (𝓝 a) :=
(to_units c).tendsto_const_smul_iff

variables [topological_space β] {f : β → α} {b : β}  {s : set β}

lemma continuous_within_at_const_smul_iff (c : G) :
  continuous_within_at (λ x, c • f x) s b ↔ continuous_within_at f s b :=
(is_unit_all c).tendsto_const_smul_iff

lemma continuous_on_const_smul_iff (c : G) :
  continuous_on (λ x, c • f x) s ↔ continuous_on f s :=
(is_unit_all c).continuous_on_const_smul_iff

lemma continuous_at_const_smul_iff (c : G) :
  continuous_at (λ x, c • f x) b ↔ continuous_at f b :=
(is_unit_all c).continuous_at_const_smul_iff

lemma continuous_const_smul_iff (c : G) :
  continuous (λ x, c • f x) ↔ continuous f :=
(is_unit_all c).continuous_const_smul_iff

/-- Scalar multiplication by a unit of a monoid `M` acting on `α` is a homeomorphism from `α`
to itself. -/
protected def homeomorph.smul (c : G) : α ≃ₜ α :=
homeomorph.smul_of_unit (to_units c)

lemma is_open_map_smul (c : G) : is_open_map (λ x : α, c • x) :=
(homeomorph.smul c).is_open_map

lemma is_closed_map_smul (c : G) : is_closed_map (λ x : α, c • x) :=
(homeomorph.smul c).is_closed_map

end group

instance has_contnuous_mul.has_continuous_smul {M : Type*} [monoid M]
  [topological_space M] [has_continuous_mul M] :
  has_continuous_smul M M :=
⟨continuous_mul⟩

instance [topological_space β] [has_scalar M α] [has_scalar M β] [has_continuous_smul M α]
  [has_continuous_smul M β] :
  has_continuous_smul M (α × β) :=
⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
  (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩
