import analysis.normed_space.dual

open is_R_or_C

variables {F : Type*} [inner_product_space ℝ F]


--/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
--`f (x + y) = f x + f y` and `f (c • x) = c • f x`. Elements of `linear_map R M M₂` (available under
--the notation `M →ₗ[R] M₂`) are bundled versions of such maps. An unbundled version is available with
--the predicate `is_linear_map`, but it should be avoided most of the time. -/
--structure linear_map (R : Type u) (M : Type v) (M₂ : Type w)
--  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R M₂]
--  extends add_hom M M₂, M →[R] M₂

section bad_def₁

structure conj_linear_map_bad (𝕜 : Type*) (M₁ : Type*) (M₂ : Type*) [is_R_or_C 𝕜]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [module 𝕜 M₁] [module 𝕜 M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : 𝕜) (z : M₁), to_fun (c • z) = (conj c) • to_fun z)

variables {M₁ M₂ : Type*} [add_comm_monoid M₁] [add_comm_monoid M₂] [module ℝ M₁] [module ℝ M₂]

example (f₁ : linear_map ℝ M₁ M₂) : conj_linear_map_bad ℝ M₁ M₂ := f₁

end bad_def₁

section bad_def₂

structure conj_linear_map_bad₂ (b : bool) (𝕜 : Type*) (M₁ : Type*) (M₂ : Type*)
  [ring 𝕜] [star_ring 𝕜] [add_comm_monoid M₁] [add_comm_monoid M₂] [module 𝕜 M₁] [module 𝕜 M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : 𝕜) (z : M₁), to_fun (c • z) = (if b then star c else c) • to_fun z)

end bad_def₂

section bad_def₃

structure conj_linear_map_bad₃ (b : bool) (𝕜 : Type*) (M₁ : Type*) (M₂ : Type*)
  [ring 𝕜] [star_ring 𝕜] [add_comm_monoid M₁] [add_comm_monoid M₂] [module 𝕜 M₁] [module 𝕜 M₂]
  extends add_hom M₁ M₂ :=
(map_smul : ∀ (c : 𝕜) (z : M₁), to_fun (c • z) = (if b then star c else c) • to_fun z)

end bad_def₃

-- Our solution
structure semilinear_map {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  (M : Type*) (M₂ : Type*)
  [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends add_hom M M₂ :=
(map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = (σ r) • to_fun x)
