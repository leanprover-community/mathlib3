/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import algebra.module.basic
import linear_algebra.finsupp

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a universal lifting property, and the
proof that all free modules are projective.

# Main definitions

Let `R` be a ring and let `M` be an `R`-module.

`is_projective R M` -- the proposition saying that `M` is a projective `R`-module.

## Implementation details

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes.

-/

universes u v

/-- An R-module is projective if it is a direct summand of a free module.
There are several other equivalent definitions. -/
def is_projective
  (R : Type u) [ring R] (M : Type v) [add_comm_group M] [module R M] : Prop :=
∃ s : M →ₗ[R] (M →₀ R), ∀ m, finsupp.total M M R id (s m) = m

namespace is_projective

variables {R M A B : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group A]
  [module R A]
  [add_comm_group B]
  [module R B]

theorem universal_property (h : is_projective R M) (f : A →ₗ[R] B) (g : M →ₗ[R] B) -- the R-linear maps
(hf : function.surjective f) : ∃ (h : M →ₗ[R] A), f.comp h = g :=
begin
  /-
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → A` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ A`. Apply this to a (noncomputable) map `M → A` coming the map
  `M → B` and a random splitting of the surjection `A → B`, and we get
  a map `φ : (M →₀ R) →ₗ A`.
  -/
  let φ : (M →₀ R) →ₗ[R] A := finsupp.total _ _ _ (λ m, function.surj_inv hf (g m)),
  -- By projectivity we have a map `M →ₗ (M →₀ R)`;
  cases h with s hs,
  -- Compose to get `M →ₗ A`. This works.
  use φ.comp s,
  ext m,
  conv_rhs {rw ← hs m},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

theorem of_universal_property
  (huniv : ∀ {A B : Type*} [add_comm_group A] [add_comm_group B],
  by exactI
  ∀ [module R A] [module R B],
  by exactI
  ∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B), -- the R-linear maps
  function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) : is_projective R M :=
begin
  -- let f be the universal map (M →₀ R) →ₗ[R] M coming from the identity map
  -- so it's finsupp.sum
  specialize huniv (finsupp.total M M R (id : M → M)) (linear_map.id),
    intro m,
    use finsupp.single m 1,
    simp,
  cases huniv with s hs,
  use s,
  rw linear_map.ext_iff at hs,
  exact hs,
end

end is_projective

/-
import linear_algebra.basic
import algebra.homology.chain_complex
import algebra.category.Module.abelian

universe u

def is_projective
  (R : Type u) [ring R] (M : Type u) [add_comm_group M] [module R M] : Prop :=
∃ s : M →ₗ[R] (M →₀ R), ∀ m, (s m).sum (λ m r, r • m) = m

namespace function

variables {α β : Type u} (f : α → β) (hf : surjective f)

--@[simp] lemma surj_inv.apply (b) : f (surj_inv hf b) = b := surj_inv_eq hf b

--#check surj_inv.apply
--#check surj_inv_eq

end function
namespace is_projective

variables {R : Type u} [ring R] {M : Type u} [add_comm_group M] [module R M] (h : is_projective R M)

-- this is finsupp.total
-- noncomputable
-- def universal_free_R_mod_map {X : Type u} (f : X → M) : (X →₀ R) →ₗ[R] M :=
--   { to_fun := λ l, finsupp.sum l (λ m r, r • f m),
--     map_add' := begin
--       intros,
--       rw finsupp.sum_add_index;
--       simp [add_smul],
--     end,
--     map_smul' := begin
--       intros m f,
--       rw finsupp.sum_smul_index',
--       { rw finsupp.smul_sum,
--         simp_rw smul_assoc },
--       { simp },
--     end }

-- this is total_single
-- def universal_free_R_mod_property (X : Type u) (f : X → M) (x : X) (r : R) :
-- universal_free_R_mod_map f (finsupp.single x r) = r • f x :=
-- begin
--   simp [universal_free_R_mod_map],
-- end

theorem universal_property {R A B M : Type u} [ring R] [add_comm_group M]
  [semimodule R M] (h : is_projective R M)
[add_comm_group A] [add_comm_group B]
  [module R A] [module R B] (f : A →ₗ[R] B) (g : M →ₗ[R] B) -- the R-linear maps
(hf : function.surjective f) : ∃ (k : M →ₗ[R] A), f.comp k = g :=
begin
  /-
  Recall that `X →₀ R` is Lean's way of talking about the free `R`-module
  on a type `X`. The universal property `finsupp.total` says that to a map
  `X → A` from a type to an `R`-module, we get an associated R-module map
  `(X →₀ R) →ₗ A`. Apply this to a (noncomputable) map `M → A` coming the map
  `M → B` and a random splitting of the surjection `A → B`, and we get
  a map `φ : (M →₀ R) →ₗ A`.
  -/
  let φ : (M →₀ R) →ₗ[R] A := finsupp.total _ _ _ (λ m, function.surj_inv hf (g m)),
  -- By projectivity we have a map `M →ₗ (M →₀ R)`;
  cases h with s hs,
  -- Compose to get `M →ₗ A`. This works.
  use φ.comp s,
  ext m,
  conv_rhs {rw ← hs m},
  simp [φ, finsupp.total_apply, function.surj_inv_eq hf],
end

#check @finsupp.total
theorem is_projective_of_universal_property
  {R M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (huniv : ∀ {A B : Type u} [add_comm_group A] [add_comm_group B], by exactI ∀
  [module R A] [module R B], by exactI
  ∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B), -- the R-linear maps
  function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) : is_projective R M :=
begin
  -- let f be the universal map (M →₀ R) →ₗ[R] M coming from the identity map
  -- so it's finsupp.sum
  specialize huniv (finsupp.total _ _ _ (id : M → M)) (linear_map.id) _,
    intro m,
    use finsupp.single m 1,
    simp,
  cases huniv with s hs,
  use s,
  rw linear_map.ext_iff at hs,
  exact hs,
end


def chain_complex.pure (R M : Type u) [ring R] [add_comm_group M] [semimodule R M] :
  chain_complex (Module R) :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl }

structure projective_resolution (R : Type u) [comm_ring R] (M : Type u)
  [add_comm_group M] [module R M] :=
(complex : chain_complex (Module R))  -- `Module R` with a capital M is the type of objects in
-- the category of R-modules.
(bounded : ∀ (n : ℤ), n < 0 → subsingleton (complex.X n)) -- The modules to the right of the
-- zeroth module are trivial.
(projective : ∀ (n : ℤ), is_projective R (complex.X n))
(resolution : complex ≅ chain_complex.pure R M)
--(coker_isom : (homological_complex.homology (Module R) 0).obj complex ≅ Module.of R M)
-- The homology at the zeroth module (the cokernel of the map P₁ → Pₒ) is isomorphic to M.

lemma projective_of_subsingleton (R : Type u) [comm_ring R] (M : Type u)
  [add_comm_group M] [module R M] [subsingleton M] :
is_projective R M :=
begin
  use 0,
  simp,
end


def projective_resolution_of_projective (R : Type u) [comm_ring R] (M : Type u)
  [add_comm_group M] [module R M] (H : is_projective R M) :
  projective_resolution R M :=
{ complex :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl },
  bounded := λ n hn, -- let n ∈ ℤ be negative
  begin
    dsimp,
    rw if_neg (int.ne_of_lt hn), -- apply the fact that n cannot be 0
    exact punit.subsingleton,
  end,
  projective := λ n,
  begin
    dsimp,
    split_ifs, -- split into the cases n = 0 and n ≠ 0
    { rwa if_pos h }, -- apply the assumptions that n = 0 and M is projective
    { rw if_neg h, -- apply the assumption n ≠ 0
      apply projective_of_subsingleton }
  end,
  resolution := category_theory.iso.refl _ }

end is_projective

-/
