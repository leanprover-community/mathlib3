import algebra.module.pi
import algebra.module.prod
import linear_algebra.affine_space.basic

open_locale affine

variables {𝕜 V V₁ V₂ E E₁ E₂ ι : Type*} {𝕜i Vi Ei : Π i : ι, Type*}

variables (𝕜 E)

class convex_space [semiring 𝕜] :=
(segment_map : 𝕜 → 𝕜 → E → E → E)
(segment_map_symm : ∀ a b, a + b = 1 → ∀ x y, segment_map a b x y = segment_map b a y x)

variables {𝕜 E}

section prod
variables [semiring 𝕜] [convex_space 𝕜 E₁] [convex_space 𝕜 E₂]

instance : convex_space 𝕜 (E₁ × E₂) :=
{ segment_map := λ a b x y,
    ⟨convex_space.segment_map a b x.1 y.1, convex_space.segment_map a b x.2 y.2⟩,
  segment_map_symm := λ a b h x y,
    prod.ext (convex_space.segment_map_symm a b h x.1 y.1)
      (convex_space.segment_map_symm a b h x.2 y.2) }

end prod

section pi
variables [Π i, semiring (𝕜i i)] [Π i, convex_space (𝕜i i) (Ei i)]

instance : convex_space (Π i : ι, 𝕜i i) (Π i : ι, Ei i) :=
{ segment_map := λ a b x y i, convex_space.segment_map (a i) (b i) (x i) (y i),
  segment_map_symm := λ a b h x y,
    funext (λ i, convex_space.segment_map_symm _ _ (congr_fun h i) _ _) }

end pi

section affine
variables [ring 𝕜] [add_comm_group V] [module 𝕜 V] [affine_space V E]
  [add_comm_group V₁] [module 𝕜 V₁] [affine_space V₁ E₁]
  [add_comm_group V₂] [module 𝕜 V₂] [affine_space V₂ E₂]
  [Π i, ring (𝕜i i)] [Π i, add_comm_group (Vi i)] [Π i, module (𝕜i i) (Vi i)]
  [Π i, affine_space (Vi i) (Ei i)]

section
include V

instance affine_space.to_convex_space : convex_space 𝕜 E :=
{ segment_map := λ a _ x y, a • (y -ᵥ x) +ᵥ x,
  segment_map_symm := λ a b h x y,
  by rw [eq_sub_of_add_eq h, sub_smul, one_smul, sub_eq_add_neg, ←smul_neg, neg_vsub_eq_vsub_rev,
    add_comm, ←vadd_vadd, vsub_vadd] }

end

end affine

section module
variables [semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] [add_comm_monoid E₁] [module 𝕜 E₁]
  [add_comm_monoid E₂] [module 𝕜 E₂]
  [Π i, semiring (𝕜i i)] [Π i, add_comm_monoid (Ei i)] [Π i, module (𝕜i i) (Ei i)]

instance module.to_convex_space : convex_space 𝕜 E :=
{ segment_map := λ a b x y, a • x + b • y,
  segment_map_symm := λ a b _ x y, add_comm _ _ }

end module
