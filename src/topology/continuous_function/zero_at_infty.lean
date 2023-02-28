/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import topology.continuous_function.bounded
import topology.continuous_function.cocompact_map

/-!
# Continuous functions vanishing at infinity

The type of continuous functions vanishing at infinity. When the domain is compact
`C(α, β) ≃ C₀(α, β)` via the identity map. When the codomain is a metric space, every continuous
map which vanishes at infinity is a bounded continuous function. When the domain is a locally
compact space, this type has nice properties.

## TODO

* Create more intances of algebraic structures (e.g., `non_unital_semiring`) once the necessary
  type classes (e.g., `topological_ring`) are sufficiently generalized.
* Relate the unitization of `C₀(α, β)` to the Alexandroff compactification.
-/
universes u v w

variables {F : Type*} {α : Type u} {β : Type v} {γ : Type w} [topological_space α]

open_locale bounded_continuous_function topology
open filter metric

/-- `C₀(α, β)` is the type of continuous functions `α → β` which vanish at infinity from a
topological space to a metric space with a zero element.

When possible, instead of parametrizing results over `(f : C₀(α, β))`,
you should parametrize over `(F : Type*) [zero_at_infty_continuous_map_class F α β] (f : F)`.

When you extend this structure, make sure to extend `zero_at_infty_continuous_map_class`. -/
structure zero_at_infty_continuous_map (α : Type u) (β : Type v)
  [topological_space α] [has_zero β] [topological_space β] extends continuous_map α β :
  Type (max u v) :=
(zero_at_infty' : tendsto to_fun (cocompact α) (𝓝 0))

localized "notation [priority 2000] (name := zero_at_infty_continuous_map)
  `C₀(` α `, ` β `)` := zero_at_infty_continuous_map α β" in zero_at_infty
localized "notation (name := zero_at_infty_continuous_map.arrow)
  α ` →C₀ ` β := zero_at_infty_continuous_map α β" in zero_at_infty

section
set_option old_structure_cmd true

/-- `zero_at_infty_continuous_map_class F α β` states that `F` is a type of continuous maps which
vanish at infinity.

You should also extend this typeclass when you extend `zero_at_infty_continuous_map`. -/
class zero_at_infty_continuous_map_class (F : Type*) (α β : out_param $ Type*) [topological_space α]
  [has_zero β] [topological_space β] extends continuous_map_class F α β :=
(zero_at_infty (f : F) : tendsto f (cocompact α) (𝓝 0))

end

export zero_at_infty_continuous_map_class (zero_at_infty)

namespace zero_at_infty_continuous_map

section basics

variables [topological_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

instance : zero_at_infty_continuous_map_class C₀(α, β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_continuous := λ f, f.continuous_to_fun,
  zero_at_infty := λ f, f.zero_at_infty' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun C₀(α, β) (λ _, α → β) := fun_like.has_coe_to_fun

instance : has_coe_t F C₀(α, β) :=
⟨λ f, { to_fun := f, continuous_to_fun := map_continuous f, zero_at_infty' := zero_at_infty f }⟩

@[simp] lemma coe_to_continuous_fun (f : C₀(α, β)) : (f.to_continuous_map : α → β) = f := rfl


@[ext] lemma ext {f g : C₀(α, β)} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

/-- Copy of a `zero_at_infinity_continuous_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : C₀(α, β) :=
{ to_fun := f',
  continuous_to_fun := by { rw h, exact f.continuous_to_fun },
  zero_at_infty' := by { simp_rw h, exact f.zero_at_infty' } }

@[simp] lemma coe_copy (f : C₀(α, β)) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' := rfl
lemma copy_eq (f : C₀(α, β)) (f' : α → β) (h : f' = f) : f.copy f' h = f := fun_like.ext' h

lemma eq_of_empty [is_empty α] (f g : C₀(α, β)) : f = g :=
ext $ is_empty.elim ‹_›

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. -/
@[simps]
def continuous_map.lift_zero_at_infty [compact_space α] : C(α, β) ≃ C₀(α, β) :=
{ to_fun := λ f, { to_fun := f, continuous_to_fun := f.continuous, zero_at_infty' := by simp },
  inv_fun := λ f, f,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- A continuous function on a compact space is automatically a continuous function vanishing at
infinity. This is not an instance to avoid type class loops. -/
@[simps]
def zero_at_infty_continuous_map_class.of_compact {G : Type*} [continuous_map_class G α β]
  [compact_space α] : zero_at_infty_continuous_map_class G α β :=
{ coe := λ g, g,
  coe_injective' := λ f g h, fun_like.coe_fn_eq.mp h,
  map_continuous := map_continuous,
  zero_at_infty := by simp }

end basics

/-! ### Algebraic structure

Whenever `β` has suitable algebraic structure and a compatible topological structure, then
`C₀(α, β)` inherits a corresponding algebraic structure. The primary exception to this is that
`C₀(α, β)` will not have a multiplicative identity.
-/

section algebraic_structure

variables [topological_space β] (x : α)

instance [has_zero β] : has_zero C₀(α, β) := ⟨⟨0, tendsto_const_nhds⟩⟩

instance [has_zero β] : inhabited C₀(α, β) := ⟨0⟩

@[simp] lemma coe_zero [has_zero β] : ⇑(0 : C₀(α, β)) = 0 := rfl
lemma zero_apply [has_zero β] : (0 : C₀(α, β)) x = 0 := rfl

instance [mul_zero_class β] [has_continuous_mul β] : has_mul C₀(α, β) :=
⟨λ f g, ⟨f * g, by simpa only [mul_zero] using (zero_at_infty f).mul (zero_at_infty g)⟩⟩

@[simp] lemma coe_mul [mul_zero_class β] [has_continuous_mul β] (f g : C₀(α, β)) :
  ⇑(f * g) = f * g := rfl
lemma mul_apply [mul_zero_class β] [has_continuous_mul β] (f g : C₀(α, β)) :
  (f * g) x = f x * g x := rfl

instance [mul_zero_class β] [has_continuous_mul β] : mul_zero_class C₀(α, β) :=
fun_like.coe_injective.mul_zero_class _ coe_zero coe_mul

instance [semigroup_with_zero β] [has_continuous_mul β] : semigroup_with_zero C₀(α, β) :=
fun_like.coe_injective.semigroup_with_zero _ coe_zero coe_mul

instance [add_zero_class β] [has_continuous_add β] : has_add C₀(α, β) :=
⟨λ f g, ⟨f + g, by simpa only [add_zero] using (zero_at_infty f).add (zero_at_infty g)⟩⟩

@[simp] lemma coe_add [add_zero_class β] [has_continuous_add β] (f g : C₀(α, β)) :
  ⇑(f + g) = f + g := rfl
lemma add_apply [add_zero_class β] [has_continuous_add β] (f g : C₀(α, β)) :
  (f + g) x = f x + g x := rfl

instance [add_zero_class β] [has_continuous_add β] : add_zero_class C₀(α, β) :=
fun_like.coe_injective.add_zero_class _ coe_zero coe_add

section add_monoid

variables [add_monoid β] [has_continuous_add β] (f g : C₀(α, β))

@[simp] lemma coe_nsmul_rec : ∀ n, ⇑(nsmul_rec n f) = n • f
| 0 := by rw [nsmul_rec, zero_smul, coe_zero]
| (n + 1) := by rw [nsmul_rec, succ_nsmul, coe_add, coe_nsmul_rec]

instance has_nat_scalar : has_smul ℕ C₀(α, β) :=
⟨λ n f, ⟨n • f, by simpa [coe_nsmul_rec] using zero_at_infty (nsmul_rec n f)⟩⟩

instance : add_monoid C₀(α, β) :=
fun_like.coe_injective.add_monoid _ coe_zero coe_add (λ _ _, rfl)

end add_monoid

instance [add_comm_monoid β] [has_continuous_add β] : add_comm_monoid C₀(α, β) :=
fun_like.coe_injective.add_comm_monoid _ coe_zero coe_add (λ _ _, rfl)

section add_group

variables [add_group β] [topological_add_group β] (f g : C₀(α, β))

instance : has_neg C₀(α, β) :=
⟨λ f, ⟨-f, by simpa only [neg_zero] using (zero_at_infty f).neg⟩⟩

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
lemma neg_apply : (-f) x = -f x := rfl

instance : has_sub C₀(α, β) :=
⟨λ f g, ⟨f - g, by simpa only [sub_zero] using (zero_at_infty f).sub (zero_at_infty g)⟩⟩

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl
lemma sub_apply : (f - g) x = f x - g x := rfl

@[simp] lemma coe_zsmul_rec : ∀ z, ⇑(zsmul_rec z f) = z • f
| (int.of_nat n) := by rw [zsmul_rec, int.of_nat_eq_coe, coe_nsmul_rec, coe_nat_zsmul]
| -[1+ n] := by rw [zsmul_rec, zsmul_neg_succ_of_nat, coe_neg, coe_nsmul_rec]

instance has_int_scalar : has_smul ℤ C₀(α, β) :=
⟨λ n f, ⟨n • f, by simpa using zero_at_infty (zsmul_rec n f)⟩⟩

instance : add_group C₀(α, β) :=
fun_like.coe_injective.add_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

end add_group

instance [add_comm_group β] [topological_add_group β] : add_comm_group C₀(α, β) :=
fun_like.coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub (λ _ _, rfl) (λ _ _, rfl)

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : has_smul R C₀(α, β) :=
⟨λ r f, ⟨r • f, by simpa [smul_zero] using (zero_at_infty f).const_smul r⟩⟩

@[simp] lemma coe_smul [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : C₀(α, β)) : ⇑(r • f) = r • f := rfl

lemma smul_apply [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] (r : R) (f : C₀(α, β)) (x : α) : (r • f) x = r • f x := rfl

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β] [smul_with_zero Rᵐᵒᵖ β]
  [has_continuous_const_smul R β] [is_central_scalar R β] : is_central_scalar R C₀(α, β) :=
⟨λ r f, ext $ λ x, op_smul_eq_smul _ _⟩

instance [has_zero β] {R : Type*} [has_zero R] [smul_with_zero R β]
  [has_continuous_const_smul R β] : smul_with_zero R C₀(α, β) :=
function.injective.smul_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [has_zero β] {R : Type*} [monoid_with_zero R] [mul_action_with_zero R β]
  [has_continuous_const_smul R β] : mul_action_with_zero R C₀(α, β) :=
function.injective.mul_action_with_zero ⟨_, coe_zero⟩ fun_like.coe_injective coe_smul

instance [add_comm_monoid β] [has_continuous_add β] {R : Type*} [semiring R] [module R β]
  [has_continuous_const_smul R β] : module R C₀(α, β) :=
function.injective.module R ⟨_, coe_zero, coe_add⟩ fun_like.coe_injective coe_smul

instance [non_unital_non_assoc_semiring β] [topological_semiring β] :
  non_unital_non_assoc_semiring C₀(α, β) :=
fun_like.coe_injective.non_unital_non_assoc_semiring _ coe_zero coe_add coe_mul (λ _ _, rfl)

instance [non_unital_semiring β] [topological_semiring β] :
  non_unital_semiring C₀(α, β) :=
fun_like.coe_injective.non_unital_semiring _ coe_zero coe_add coe_mul (λ _ _, rfl)

instance [non_unital_comm_semiring β] [topological_semiring β] :
  non_unital_comm_semiring C₀(α, β) :=
fun_like.coe_injective.non_unital_comm_semiring _ coe_zero coe_add coe_mul (λ _ _, rfl)

instance [non_unital_non_assoc_ring β] [topological_ring β] :
  non_unital_non_assoc_ring C₀(α, β) :=
fun_like.coe_injective.non_unital_non_assoc_ring _ coe_zero coe_add coe_mul coe_neg coe_sub
  (λ _ _, rfl) (λ _ _, rfl)

instance [non_unital_ring β] [topological_ring β] :
  non_unital_ring C₀(α, β) :=
fun_like.coe_injective.non_unital_ring _ coe_zero coe_add coe_mul coe_neg coe_sub (λ _ _, rfl)
  (λ _ _, rfl)

instance [non_unital_comm_ring β] [topological_ring β] :
  non_unital_comm_ring C₀(α, β) :=
fun_like.coe_injective.non_unital_comm_ring _ coe_zero coe_add coe_mul coe_neg coe_sub (λ _ _, rfl)
  (λ _ _, rfl)

instance {R : Type*} [semiring R] [non_unital_non_assoc_semiring β] [topological_semiring β]
  [module R β] [has_continuous_const_smul R β] [is_scalar_tower R β β] :
  is_scalar_tower R C₀(α, β) C₀(α, β) :=
{ smul_assoc := λ r f g,
  begin
    ext,
    simp only [smul_eq_mul, coe_mul, coe_smul, pi.mul_apply, pi.smul_apply],
    rw [←smul_eq_mul, ←smul_eq_mul, smul_assoc],
  end }

instance {R : Type*} [semiring R] [non_unital_non_assoc_semiring β] [topological_semiring β]
  [module R β] [has_continuous_const_smul R β] [smul_comm_class R β β] :
  smul_comm_class R C₀(α, β) C₀(α, β) :=
{ smul_comm := λ r f g,
  begin
    ext,
    simp only [smul_eq_mul, coe_smul, coe_mul, pi.smul_apply, pi.mul_apply],
    rw [←smul_eq_mul, ←smul_eq_mul, smul_comm],
  end }

end algebraic_structure

section uniform

variables [uniform_space β] [uniform_space γ] [has_zero γ]
  [zero_at_infty_continuous_map_class F β γ]

lemma uniform_continuous (f : F) : uniform_continuous (f : β → γ) :=
(map_continuous f).uniform_continuous_of_tendsto_cocompact (zero_at_infty f)

end uniform

/-! ### Metric structure

When `β` is a metric space, then every element of `C₀(α, β)` is bounded, and so there is a natural
inclusion map `zero_at_infty_continuous_map.to_bcf : C₀(α, β) → (α →ᵇ β)`. Via this map `C₀(α, β)`
inherits a metric as the pullback of the metric on `α →ᵇ β`. Moreover, this map has closed range
in `α →ᵇ β` and consequently `C₀(α, β)` is a complete space whenever `β` is complete.
-/

section metric

open metric set

variables [metric_space β] [has_zero β] [zero_at_infty_continuous_map_class F α β]

protected lemma bounded (f : F) : ∃ C, ∀ x y : α, dist ((f : α → β) x) (f y) ≤ C :=
begin
  obtain ⟨K : set α, hK₁, hK₂⟩ := mem_cocompact.mp (tendsto_def.mp (zero_at_infty (f : F)) _
    (closed_ball_mem_nhds (0 : β) zero_lt_one)),
  obtain ⟨C, hC⟩ := (hK₁.image (map_continuous f)).bounded.subset_ball (0 : β),
  refine ⟨max C 1 + max C 1, (λ x y, _)⟩,
  have : ∀ x, f x ∈ closed_ball (0 : β) (max C 1),
  { intro x,
    by_cases hx : x ∈ K,
    { exact (mem_closed_ball.mp $ hC ⟨x, hx, rfl⟩).trans (le_max_left _ _) },
    { exact (mem_closed_ball.mp $ mem_preimage.mp (hK₂ hx)).trans (le_max_right _ _) } },
  exact (dist_triangle (f x) 0 (f y)).trans
    (add_le_add (mem_closed_ball.mp $ this x) (mem_closed_ball'.mp $ this y)),
end

lemma bounded_range (f : C₀(α, β)) : bounded (range f) :=
bounded_range_iff.2 f.bounded

lemma bounded_image (f : C₀(α, β)) (s : set α) : bounded (f '' s) :=
f.bounded_range.mono $ image_subset_range _ _

@[priority 100]
instance : bounded_continuous_map_class F α β :=
{ map_bounded := λ f, zero_at_infty_continuous_map.bounded f,
  ..‹zero_at_infty_continuous_map_class F α β› }

/-- Construct a bounded continuous function from a continuous function vanishing at infinity. -/
@[simps]
def to_bcf (f : C₀(α, β)) : α →ᵇ β :=
⟨f, map_bounded f⟩

section
variables (α) (β)
lemma to_bcf_injective :
  function.injective (to_bcf : C₀(α, β) → α →ᵇ β) :=
λ f g h, by { ext, simpa only using fun_like.congr_fun h x, }
end

variables {C : ℝ} {f g : C₀(α, β)}

/-- The type of continuous functions vanishing at infinity, with the uniform distance induced by the
inclusion `zero_at_infinity_continuous_map.to_bcf`, is a metric space. -/
noncomputable instance : metric_space C₀(α, β) :=
metric_space.induced _ (to_bcf_injective α β) (by apply_instance)

@[simp]
lemma dist_to_bcf_eq_dist {f g : C₀(α, β)} : dist f.to_bcf g.to_bcf = dist f g := rfl

open bounded_continuous_function

/-- Convergence in the metric on `C₀(α, β)` is uniform convergence. -/
lemma tendsto_iff_tendsto_uniformly {ι : Type*} {F : ι → C₀(α, β)} {f : C₀(α, β)} {l : filter ι} :
  tendsto F l (𝓝 f) ↔ tendsto_uniformly (λ i, F i) f l :=
by simpa only [metric.tendsto_nhds] using @bounded_continuous_function.tendsto_iff_tendsto_uniformly
  _ _ _ _ _ (λ i, (F i).to_bcf) f.to_bcf l

lemma isometry_to_bcf : isometry (to_bcf : C₀(α, β) → α →ᵇ β) := by tauto

lemma closed_range_to_bcf : is_closed (range (to_bcf : C₀(α, β) → α →ᵇ β)) :=
begin
  refine is_closed_iff_cluster_pt.mpr (λ f hf, _),
  rw cluster_pt_principal_iff at hf,
  have : tendsto f (cocompact α) (𝓝 0),
  { refine metric.tendsto_nhds.mpr (λ ε hε, _),
    obtain ⟨_, hg, g, rfl⟩ := hf (ball f (ε / 2)) (ball_mem_nhds f $ half_pos hε),
    refine (metric.tendsto_nhds.mp (zero_at_infty g) (ε / 2)
      (half_pos hε)).mp (eventually_of_forall $ λ x hx, _),
    calc dist (f x) 0 ≤ dist (g.to_bcf x) (f x) + dist (g x) 0 : dist_triangle_left _ _ _
    ...               < dist g.to_bcf f + ε / 2 : add_lt_add_of_le_of_lt (dist_coe_le_dist x) hx
    ...               < ε : by simpa [add_halves ε] using add_lt_add_right hg (ε / 2) },
  exact ⟨⟨f.to_continuous_map, this⟩, by {ext, refl}⟩,
end

/-- Continuous functions vanishing at infinity taking values in a complete space form a
complete space. -/
instance [complete_space β] : complete_space C₀(α, β) :=
(complete_space_iff_is_complete_range isometry_to_bcf.uniform_inducing).mpr
  closed_range_to_bcf.is_complete

end metric

section norm

/-! ### Normed space

The norm structure on `C₀(α, β)` is the one induced by the inclusion `to_bcf : C₀(α, β) → (α →ᵇ b)`,
viewed as an additive monoid homomorphism. Then `C₀(α, β)` is naturally a normed space over a normed
field `𝕜` whenever `β` is as well.
-/

section normed_space

variables [normed_add_comm_group β] {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 β]

noncomputable instance : normed_add_comm_group C₀(α, β) :=
normed_add_comm_group.induced C₀(α, β) (α →ᵇ β) (⟨to_bcf, rfl, λ x y, rfl⟩ : C₀(α, β) →+ (α →ᵇ β))
  (to_bcf_injective α β)

@[simp]
lemma norm_to_bcf_eq_norm {f : C₀(α, β)} : ‖f.to_bcf‖ = ‖f‖ := rfl

instance : normed_space 𝕜 C₀(α, β) :=
{ norm_smul_le := λ k f, (norm_smul k f.to_bcf).le }

end normed_space

section normed_ring

variables [non_unital_normed_ring β]

noncomputable instance : non_unital_normed_ring C₀(α, β) :=
{ norm_mul := λ f g, norm_mul_le f.to_bcf g.to_bcf,
  ..zero_at_infty_continuous_map.non_unital_ring,
  ..zero_at_infty_continuous_map.normed_add_comm_group }

end normed_ring

end norm

section star

/-! ### Star structure

It is possible to equip `C₀(α, β)` with a pointwise `star` operation whenever there is a continuous
`star : β → β` for which `star (0 : β) = 0`. We don't have quite this weak a typeclass, but
`star_add_monoid` is close enough.

The `star_add_monoid` and `normed_star_group` classes on `C₀(α, β)` are inherited from their
counterparts on `α →ᵇ β`. Ultimately, when `β` is a C⋆-ring, then so is `C₀(α, β)`.
-/

variables [topological_space β] [add_monoid β] [star_add_monoid β] [has_continuous_star β]

instance : has_star C₀(α, β) :=
{ star := λ f,
  { to_fun := λ x, star (f x),
    continuous_to_fun := (map_continuous f).star,
    zero_at_infty' := by simpa only [star_zero]
      using (continuous_star.tendsto (0 : β)).comp (zero_at_infty f) } }

@[simp]
lemma coe_star (f : C₀(α, β)) : ⇑(star f) = star f := rfl

lemma star_apply (f : C₀(α, β)) (x : α) :
  (star f) x = star (f x) := rfl

instance [has_continuous_add β] : star_add_monoid C₀(α, β) :=
{ star_involutive := λ f, ext $ λ x, star_star (f x),
  star_add := λ f g, ext $ λ x, star_add (f x) (g x) }

end star

section normed_star

variables [normed_add_comm_group β] [star_add_monoid β] [normed_star_group β]

instance : normed_star_group C₀(α, β) :=
{ norm_star := λ f, (norm_star f.to_bcf : _) }

end normed_star

section star_module

variables {𝕜 : Type*} [has_zero 𝕜] [has_star 𝕜]
  [add_monoid β] [star_add_monoid β] [topological_space β] [has_continuous_star β]
  [smul_with_zero 𝕜 β] [has_continuous_const_smul 𝕜 β] [star_module 𝕜 β]

instance : star_module 𝕜 C₀(α, β) :=
{ star_smul := λ k f, ext $ λ x, star_smul k (f x) }

end star_module

section star_ring

variables [non_unital_semiring β] [star_ring β] [topological_space β] [has_continuous_star β]
  [topological_semiring β]

instance : star_ring C₀(α, β) :=
{ star_mul := λ f g, ext $ λ x, star_mul (f x) (g x),
  ..zero_at_infty_continuous_map.star_add_monoid }

end star_ring

section cstar_ring

instance [non_unital_normed_ring β] [star_ring β] [cstar_ring β] : cstar_ring C₀(α, β) :=
{ norm_star_mul_self := λ f, @cstar_ring.norm_star_mul_self _ _ _ _ f.to_bcf }

end cstar_ring

/-! ### C₀ as a functor

For each `β` with sufficient structure, there is a contravariant functor `C₀(-, β)` from the
category of topological spaces with morphisms given by `cocompact_map`s.
-/

variables {δ : Type*} [topological_space β] [topological_space γ] [topological_space δ]

local notation α ` →co ` β := cocompact_map α β

section
variables [has_zero δ]

/-- Composition of a continuous function vanishing at infinity with a cocompact map yields another
continuous function vanishing at infinity. -/
def comp (f : C₀(γ, δ)) (g : β →co γ) : C₀(β, δ) :=
{ to_continuous_map := (f : C(γ, δ)).comp g,
  zero_at_infty' := (zero_at_infty f).comp (cocompact_tendsto g) }

@[simp] lemma coe_comp_to_continuous_fun (f : C₀(γ, δ)) (g : β →co γ) :
  ((f.comp g).to_continuous_map : β → δ) = f ∘ g := rfl

@[simp] lemma comp_id (f : C₀(γ, δ)) : f.comp (cocompact_map.id γ) = f := ext (λ x, rfl)

@[simp] lemma comp_assoc (f : C₀(γ, δ)) (g : β →co γ) (h : α →co β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp] lemma zero_comp (g : β →co γ) : (0 : C₀(γ, δ)).comp g = 0 := rfl

end

/-- Composition as an additive monoid homomorphism. -/
def comp_add_monoid_hom [add_monoid δ] [has_continuous_add δ] (g : β →co γ) :
  C₀(γ, δ) →+ C₀(β, δ) :=
{ to_fun := λ f, f.comp g,
  map_zero' := zero_comp g,
  map_add' := λ f₁ f₂, rfl }

/-- Composition as a semigroup homomorphism. -/
def comp_mul_hom [mul_zero_class δ] [has_continuous_mul δ]
  (g : β →co γ) : C₀(γ, δ) →ₙ* C₀(β, δ) :=
{ to_fun := λ f, f.comp g,
  map_mul' := λ f₁ f₂, rfl }

/-- Composition as a linear map. -/
def comp_linear_map [add_comm_monoid δ] [has_continuous_add δ] {R : Type*}
  [semiring R] [module R δ] [has_continuous_const_smul R δ] (g : β →co γ) :
  C₀(γ, δ) →ₗ[R] C₀(β, δ) :=
{ to_fun := λ f, f.comp g,
  map_add' := λ f₁ f₂, rfl,
  map_smul' := λ r f, rfl }

/-- Composition as a non-unital algebra homomorphism. -/
def comp_non_unital_alg_hom {R : Type*} [semiring R] [non_unital_non_assoc_semiring δ]
  [topological_semiring δ] [module R δ] [has_continuous_const_smul R δ] (g : β →co γ) :
  C₀(γ, δ) →ₙₐ[R] C₀(β, δ) :=
{ to_fun := λ f, f.comp g,
  map_smul' := λ r f, rfl,
  map_zero' := rfl,
  map_add' := λ f₁ f₂, rfl,
  map_mul' := λ f₁ f₂, rfl }

end zero_at_infty_continuous_map
