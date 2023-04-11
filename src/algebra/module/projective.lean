/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Antoine Labelle
-/

import algebra.module.basic
import linear_algebra.finsupp
import linear_algebra.free_module.basic

/-!

# Projective modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `is_projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `is_projective.lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `is_projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `is_projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.

All of these should be relatively straightforward.

## Tags

projective module

-/

universes u v

open linear_map finsupp

/- The actual implementation we choose: `P` is projective if the natural surjection
   from the free `R`-module on `P` to `P` splits. -/
/-- An R-module is projective if it is a direct summand of a free module, or equivalently
  if maps from the module lift along surjections. There are several other equivalent
  definitions. -/
class module.projective (R : Type*) [semiring R] (P : Type*) [add_comm_monoid P]
  [module R P] : Prop :=
(out : ∃ s : P →ₗ[R] (P →₀ R), function.left_inverse (finsupp.total P P R id) s)

namespace module

section semiring

variables {R : Type*} [semiring R] {P : Type*} [add_comm_monoid P] [module R P]
  {M : Type*} [add_comm_monoid M] [module R M] {N : Type*} [add_comm_monoid N] [module R N]

lemma projective_def : projective R P ↔
  (∃ s : P →ₗ[R] (P →₀ R), function.left_inverse (finsupp.total P P R id) s) :=
⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem projective_def' : projective R P ↔
  (∃ s : P →ₗ[R] (P →₀ R), (finsupp.total P P R id) ∘ₗ s = id) :=
by simp_rw [projective_def, fun_like.ext_iff, function.left_inverse, coe_comp, id_coe, id.def]

/-- A projective R-module has the property that maps from it lift along surjections. -/
theorem projective_lifting_property [h : projective R P] (f : M →ₗ[R] N) (g : P →ₗ[R] N)
  (hf : function.surjective f) : ∃ (h : P →ₗ[R] M), f.comp h = g :=
begin
  /-
  Here's the first step of the proof.
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → N` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ N`. Apply this to a (noncomputable) map `P → M` coming from the map
  `P →ₗ N` and a random splitting of the surjection `M →ₗ N`, and we get
  a map `φ : (P →₀ R) →ₗ M`.
  -/
  let φ : (P →₀ R) →ₗ[R] M := finsupp.total _ _ _ (λ p, function.surj_inv hf (g p)),
  -- By projectivity we have a map `P →ₗ (P →₀ R)`;
  cases h.out with s hs,
  -- Compose to get `P →ₗ M`. This works.
  use φ.comp s,
  ext p,
  conv_rhs {rw ← hs p},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

variables {Q : Type*} [add_comm_monoid Q] [module R Q]

instance [hP : projective R P] [hQ : projective R Q] : projective R (P × Q) :=
begin
  rw module.projective_def',
  cases hP.out with sP hsP,
  cases hQ.out with sQ hsQ,
  use coprod (lmap_domain R R (inl R P Q)) (lmap_domain R R (inr R P Q)) ∘ₗ sP.prod_map sQ,
  ext; simp only [coe_inl, coe_inr, coe_comp, function.comp_app, prod_map_apply, map_zero,
    coprod_apply, lmap_domain_apply, map_domain_zero, add_zero, zero_add, id_comp,
    total_map_domain],

  { rw [←fst_apply _, apply_total R], exact hsP x, },
  { rw [←snd_apply _, apply_total R], exact finsupp.total_zero_apply _ (sP x), },
  { rw [←fst_apply _, apply_total R], exact finsupp.total_zero_apply _ (sQ x), },
  { rw [←snd_apply _, apply_total R], exact hsQ x, },
end

variables {ι : Type*} (A : ι → Type*) [Π (i : ι), add_comm_monoid (A i)]
  [Π (i : ι), module R (A i)]

instance [h : Π (i : ι), projective R (A i)] : projective R (Π₀ i, A i) :=
begin
  classical,
  rw module.projective_def',
  simp_rw projective_def at h, choose s hs using h,

  letI : Π (i : ι), add_comm_monoid (A i →₀ R) := λ i, by apply_instance,
  letI : Π (i : ι), module R (A i →₀ R) := λ i, by apply_instance,
  letI : add_comm_monoid (Π₀ (i : ι), A i →₀ R) := @dfinsupp.add_comm_monoid ι (λ i, A i →₀ R) _,
  letI : module R (Π₀ (i : ι), A i →₀ R) := @dfinsupp.module ι R (λ i, A i →₀ R) _ _ _,

  let f := λ i, lmap_domain R R (dfinsupp.single i : A i → Π₀ i, A i),
  use dfinsupp.coprod_map f ∘ₗ dfinsupp.map_range.linear_map s,

  ext i x j,
  simp only [dfinsupp.coprod_map, direct_sum.lof, total_map_domain,
    coe_comp, coe_lsum, id_coe, linear_equiv.coe_to_linear_map, finsupp_lequiv_dfinsupp_symm_apply,
    function.comp_app, dfinsupp.lsingle_apply, dfinsupp.map_range.linear_map_apply,
    dfinsupp.map_range_single, lmap_domain_apply, dfinsupp.to_finsupp_single,
    finsupp.sum_single_index, id.def, function.comp.left_id, dfinsupp.single_apply],
  rw [←dfinsupp.lapply_apply j, apply_total R],

  obtain rfl | hij := eq_or_ne i j,

  { convert (hs i) x,
    { ext, simp },
    { simp } },
  { convert finsupp.total_zero_apply _ ((s i) x),
    { ext, simp [hij] },
    { simp [hij] } }
end

end semiring

section ring

variables {R : Type*} [ring R] {P : Type*} [add_comm_group P] [module R P]

/-- Free modules are projective. -/
theorem projective_of_basis {ι : Type*} (b : basis ι R P) : projective R P :=
begin
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ (λ i, finsupp.single (b i) (1 : R)),
  intro m,
  simp only [b.constr_apply, mul_one, id.def, finsupp.smul_single', finsupp.total_single,
    linear_map.map_finsupp_sum],
  exact b.total_repr m,
end

@[priority 100]
instance projective_of_free [module.free R P] : module.projective R P :=
projective_of_basis $ module.free.choose_basis R P

end ring

--This is in a different section because special universe restrictions are required.
section of_lifting_property

/-- A module which satisfies the universal property is projective. Note that the universe variables
in `huniv` are somewhat restricted. -/
theorem projective_of_lifting_property'
  {R : Type u} [semiring R] {P : Type (max u v)} [add_comm_monoid P] [module R P]
  -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
  (huniv : ∀ {M : Type (max v u)} {N : Type (max u v)} [add_comm_monoid M] [add_comm_monoid N],
    by exactI
    ∀ [module R M] [module R N],
    by exactI
    ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
  function.surjective f → ∃ (h : P →ₗ[R] M), f.comp h = g) :
  -- then `P` is projective.
  projective R P :=
begin
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ (s : P →ₗ[R] P →₀ R),
    (finsupp.total P P R id).comp s = linear_map.id :=
    huniv (finsupp.total P P R (id : P → P)) (linear_map.id : P →ₗ[R] P) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro p,
    use finsupp.single p 1,
    simp },
end

/-- A variant of `of_lifting_property'` when we're working over a `[ring R]`,
which only requires quantifying over modules with an `add_comm_group` instance. -/
theorem projective_of_lifting_property
  {R : Type u} [ring R] {P : Type (max u v)} [add_comm_group P] [module R P]
  -- If for all surjections of `R`-modules `M →ₗ N`, all maps `P →ₗ N` lift to `P →ₗ M`,
  (huniv : ∀ {M : Type (max v u)} {N : Type (max u v)} [add_comm_group M] [add_comm_group N],
    by exactI
    ∀ [module R M] [module R N],
    by exactI
    ∀ (f : M →ₗ[R] N) (g : P →ₗ[R] N),
  function.surjective f → ∃ (h : P →ₗ[R] M), f.comp h = g) :
  -- then `P` is projective.
  projective R P :=
-- We could try and prove this *using* `of_lifting_property`,
-- but this quickly leads to typeclass hell,
-- so we just prove it over again.
begin
  -- let `s` be the universal map `(P →₀ R) →ₗ P` coming from the identity map `P →ₗ P`.
  obtain ⟨s, hs⟩ : ∃ (s : P →ₗ[R] P →₀ R),
    (finsupp.total P P R id).comp s = linear_map.id :=
    huniv (finsupp.total P P R (id : P → P)) (linear_map.id : P →ₗ[R] P) _,
  -- This `s` works.
  { use s,
    rwa linear_map.ext_iff at hs },
  { intro p,
    use finsupp.single p 1,
    simp },
end

end of_lifting_property

end module
