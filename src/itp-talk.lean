import analysis.normed_space.dual

open is_R_or_C

open_locale complex_conjugate

set_option old_structure_cmd true
variables {F : Type*} [inner_product_space ℝ F]


--/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
--`f (x + y) = f x + f y` and `f (c • x) = c • f x`. Elements of `linear_map R M M₂` (available under
--the notation `M →ₗ[R] M₂`) are bundled versions of such maps. -/
--
--structure linear_map (R : Type u) (M : Type v) (M₂ : Type w)
--  [semiring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
--  extends add_hom M M₂, M →[R] M₂

section bad_def₁

-- Make a totally separate definition for conjugate linear maps like this:
structure conj_linear_map_bad₁ (M₁ : Type*) (M₂ : Type*)
  [add_comm_group M₁] [add_comm_group M₂] [module ℂ M₁] [module ℂ M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : ℂ) (z : M₁), to_fun (c • z) = (conj c) • to_fun z)

-- Main problem: totally separate from linear maps, which means massive code duplication

end bad_def₁

section bad_def₂

-- Generalize this construction to real or complex:
structure conj_linear_map_bad₂ (𝕜 : Type*) (M₁ : Type*) (M₂ : Type*) [is_R_or_C 𝕜]
  [add_comm_group M₁] [add_comm_group M₂] [module 𝕜 M₁] [module 𝕜 M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : 𝕜) (z : M₁), to_fun (c • z) = (conj c) • to_fun z)

variables {M₁ M₂ : Type*} [add_comm_group M₁] [add_comm_group M₂] [module ℝ M₁]
[module ℝ M₂]

-- Better, could at least unify e.g. vector spaces
-- Not general enough to replace linear maps -> needs to be a separate definition with its own API
-- Also, in the real case, we don't actually get a linear map:
--example (f₁ : linear_map ℝ M₁ M₂) : conj_linear_map_bad ℝ M₁ M₂ := f₁

end bad_def₂

section bad_def₃

-- Generalize some more?
structure conj_linear_map_bad₃ (b : bool) (𝕜 : Type*) (M₁ : Type*) (M₂ : Type*)
  [ring 𝕜] [star_ring 𝕜] [add_comm_group M₁] [add_comm_group M₂] [module 𝕜 M₁] [module 𝕜 M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : 𝕜) (z : M₁), to_fun (c • z) = (if b then star c else c) • to_fun z)

-- Problem: in the real case, still have two different definitions when b=0 and b=1
-- Also, still not general enough to actually replace linear maps

end bad_def₃

section solution

/-
Bad solution 4: Conjugate space -> define a type copy of the vector space where
scalar multiplication has complex conjugation baked in.
-/

-- (Part of) our solution
structure semilinear_map {R₁ : Type*} {R₂ : Type*} [ring R₁] [ring R₂] (σ : R₁ →+* R₂)
  (M₁ : Type*) (M₂ : Type*)
  [add_comm_group M₁] [add_comm_group M₂] [module R₁ M₁] [module R₂ M₂]
  extends add_hom M₁ M₂ :=
(map_smul' : ∀ (r : R₁) (x : M₁), to_fun (r • x) = (σ r) • to_fun x)

variables {M₁ M₂ : Type*} [add_comm_group M₁] [add_comm_group M₂] [module ℝ M₁]
[module ℝ M₂]

example (f₁ : semilinear_map (ring_hom.id ℝ) M₁ M₂) :
  semilinear_map (conj : ℝ →+* ℝ) M₁ M₂ := f₁

/-
Big advantage: can actually replace linear maps, no need to duplicate API
Use notation to hide the ugliness:
`semilinear_map (ring_hom.id ℂ) M₁ M₂` denoted by `M₁ →ₗ[ℂ] M₂`
Conjugate-linear maps denoted as `M₁ →ₗ⋆[ℂ] M₂`
Drawback: implies massive refactor
-/

end solution

-- How to deal with composition?
variables {R₁ R₂ R₃ M₁ M₂ M₃ : Type*} [ring R₁] [ring R₂] [ring R₃]
  [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃]
  [module R₁ M₁] [module R₂ M₂] [module R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃}

namespace semilinear_map

instance : add_hom_class (semilinear_map σ₁₂ M₁ M₂) M₁ M₂ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_add := λ f, f.map_add' }

def comp (g : semilinear_map σ₂₃ M₂ M₃) (f : semilinear_map σ₁₂ M₁ M₂) :
  semilinear_map (σ₂₃.comp σ₁₂) M₁ M₃ :=
{ to_fun := g ∘ f,
  map_add' := sorry,
  map_smul' := sorry }

variables {N : Type*} [add_comm_group N] [module ℂ N]
variables (g : semilinear_map (ring_hom.id ℂ) N N) (f : semilinear_map (conj : ℂ →+* ℂ) N N)

#check f.comp f
#check f.comp g
#check g.comp g

example : g.comp g = g := sorry  -- Typechecks
--example : f.comp f = g := sorry  -- Doesn't typecheck!

-- The solution:

/-- Class that expresses the fact that three ring homomorphisms form a composition triple. This is
used to handle composition of semilinear maps. -/
class ring_hom_comp_triple (σ₁₂ : R₁ →+* R₂) (σ₂₃ : R₂ →+* R₃)
  (σ₁₃ : out_param (R₁ →+* R₃)) : Prop :=
(comp_eq : σ₂₃.comp σ₁₂ = σ₁₃)

/-- Class that expresses the fact that two ring homomorphisms are inverses of each other. This is
used to handle `symm` for semilinear equivalences. -/
class ring_hom_inv_pair (σ : R₁ →+* R₂) (σ' : out_param (R₂ →+* R₁)) : Prop :=
(comp_eq : σ'.comp σ = ring_hom.id R₁)
(comp_eq₂ : σ.comp σ' = ring_hom.id R₂)

-- This one is needed for many lemmas about continuous linear maps:

/-- Class expressing the fact that a `ring_hom` is surjective. This is needed in the context
of semilinear maps, where some lemmas require this. -/
class ring_hom_surjective (σ : R₁ →+* R₂) : Prop :=
(is_surjective : function.surjective σ)


end semilinear_map

-- **Applications**

-- * Riesz representation theorem: `inner_product_space/dual.lean`, line 113
-- * Adjoint of an operator on a Hilbert space: `inner_product_space/adjoint.lean`, line 93
-- * Frobenius-linear maps: over to Rob!
