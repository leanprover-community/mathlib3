/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import topology.algebra.ring
import topology.algebra.mul_action
import topology.algebra.uniform_group
import topology.uniform_space.uniform_embedding
import algebra.algebra.basic
import linear_algebra.projection
import linear_algebra.pi
import linear_algebra.determinant

/-!
# Theory of topological modules and continuous linear maps.

We use the class `has_continuous_smul` for topological (semi) modules and topological vector spaces.

In this file we define continuous (semi-)linear maps, as semilinear maps between topological
modules which are continuous. The set of continuous semilinear maps between the topological
`R₁`-module `M` and `R₂`-module `M₂` with respect to the `ring_hom` `σ` is denoted by `M →SL[σ] M₂`.
Plain linear maps are denoted by `M →L[R] M₂` and star-linear maps by `M →L⋆[R] M₂`.

The corresponding notation for equivalences is `M ≃SL[σ] M₂`, `M ≃L[R] M₂` and `M ≃L⋆[R] M₂`.
-/

open filter
open_locale topological_space big_operators filter

universes u v w u'

section

variables {R : Type*} {M : Type*}
[ring R] [topological_space R]
[topological_space M] [add_comm_group M]
[module R M]

lemma has_continuous_smul.of_nhds_zero [topological_ring R] [topological_add_group M]
  (hmul : tendsto (λ p : R × M, p.1 • p.2) (𝓝 0 ×ᶠ (𝓝 0)) (𝓝 0))
  (hmulleft : ∀ m : M, tendsto (λ a : R, a • m) (𝓝 0) (𝓝 0))
  (hmulright : ∀ a : R, tendsto (λ m : M, a • m) (𝓝 0) (𝓝 0)) : has_continuous_smul R M :=
⟨begin
  rw continuous_iff_continuous_at,
  rintros ⟨a₀, m₀⟩,
  have key : ∀ p : R × M,
    p.1 • p.2 = a₀ • m₀ + ((p.1 - a₀) • m₀ + a₀ • (p.2 - m₀) + (p.1 - a₀) • (p.2 - m₀)),
  { rintro ⟨a, m⟩,
    simp [sub_smul, smul_sub],
    abel },
  rw funext key, clear key,
  refine tendsto_const_nhds.add (tendsto.add (tendsto.add _ _) _),
  { rw [sub_self, zero_smul],
    apply (hmulleft m₀).comp,
    rw [show (λ p : R × M, p.1 - a₀) = (λ a, a - a₀) ∘ prod.fst, by {ext, refl }, nhds_prod_eq],
    have : tendsto (λ a, a - a₀) (𝓝 a₀) (𝓝 0),
    { rw ← sub_self a₀,
      exact tendsto_id.sub tendsto_const_nhds },
    exact this.comp tendsto_fst  },
  { rw [sub_self, smul_zero],
    apply (hmulright a₀).comp,
    rw [show (λ p : R × M, p.2 - m₀) = (λ m, m - m₀) ∘ prod.snd, by {ext, refl }, nhds_prod_eq],
    have : tendsto (λ m, m - m₀) (𝓝 m₀) (𝓝 0),
    { rw ← sub_self m₀,
      exact tendsto_id.sub tendsto_const_nhds },
    exact this.comp tendsto_snd },
  { rw [sub_self, zero_smul, nhds_prod_eq,
        show (λ p : R × M, (p.fst - a₀) • (p.snd - m₀)) =
             (λ  p : R × M, p.1 • p.2) ∘ (prod.map (λ a, a - a₀) (λ m, m - m₀)), by { ext, refl }],
    apply hmul.comp (tendsto.prod_map _ _);
    { rw ← sub_self ,
      exact tendsto_id.sub tendsto_const_nhds } },
end⟩
end

section
variables {R : Type*} {M : Type*}
[ring R] [topological_space R]
[topological_space M] [add_comm_group M] [has_continuous_add M]
[module R M] [has_continuous_smul R M]

/-- If `M` is a topological module over `R` and `0` is a limit of invertible elements of `R`, then
`⊤` is the only submodule of `M` with a nonempty interior.
This is the case, e.g., if `R` is a nontrivially normed field. -/
lemma submodule.eq_top_of_nonempty_interior'
  [ne_bot (𝓝[{x : R | is_unit x}] 0)]
  (s : submodule R M) (hs : (interior (s:set M)).nonempty) :
  s = ⊤ :=
begin
  rcases hs with ⟨y, hy⟩,
  refine (submodule.eq_top_iff'.2 $ λ x, _),
  rw [mem_interior_iff_mem_nhds] at hy,
  have : tendsto (λ c:R, y + c • x) (𝓝[{x : R | is_unit x}] 0) (𝓝 (y + (0:R) • x)),
    from tendsto_const_nhds.add ((tendsto_nhds_within_of_tendsto_nhds tendsto_id).smul
      tendsto_const_nhds),
  rw [zero_smul, add_zero] at this,
  obtain ⟨_, hu : y + _ • _ ∈ s, u, rfl⟩ :=
    nonempty_of_mem (inter_mem (mem_map.1 (this hy)) self_mem_nhds_within),
  have hy' : y ∈ ↑s := mem_of_mem_nhds hy,
  rwa [s.add_mem_iff_right hy', ←units.smul_def, s.smul_mem_iff' u] at hu,
end

variables (R M)

/-- Let `R` be a topological ring such that zero is not an isolated point (e.g., a nontrivially
normed field, see `normed_field.punctured_nhds_ne_bot`). Let `M` be a nontrivial module over `R`
such that `c • x = 0` implies `c = 0 ∨ x = 0`. Then `M` has no isolated points. We formulate this
using `ne_bot (𝓝[≠] x)`.

This lemma is not an instance because Lean would need to find `[has_continuous_smul ?m_1 M]` with
unknown `?m_1`. We register this as an instance for `R = ℝ` in `real.punctured_nhds_module_ne_bot`.
One can also use `haveI := module.punctured_nhds_ne_bot R M` in a proof.
-/
lemma module.punctured_nhds_ne_bot [nontrivial M] [ne_bot (𝓝[≠] (0 : R))]
  [no_zero_smul_divisors R M] (x : M) :
  ne_bot (𝓝[≠] x) :=
begin
  rcases exists_ne (0 : M) with ⟨y, hy⟩,
  suffices : tendsto (λ c : R, x + c • y) (𝓝[≠] 0) (𝓝[≠] x), from this.ne_bot,
  refine tendsto.inf _ (tendsto_principal_principal.2 $ _),
  { convert tendsto_const_nhds.add ((@tendsto_id R _).smul_const y),
    rw [zero_smul, add_zero] },
  { intros c hc,
    simpa [hy] using hc }
end

end

section lattice_ops

variables {ι R M₁ M₂ : Type*} [semiring R] [add_comm_monoid M₁] [add_comm_monoid M₂]
  [module R M₁] [module R M₂] [u : topological_space R] {t : topological_space M₂}
  [has_continuous_smul R M₂] (f : M₁ →ₗ[R] M₂)

lemma has_continuous_smul_induced :
  @has_continuous_smul R M₁ _ u (t.induced f) :=
{ continuous_smul :=
    begin
      letI : topological_space M₁ := t.induced f,
      refine continuous_induced_rng.2 _,
      simp_rw [function.comp, f.map_smul],
      refine continuous_fst.smul (continuous_induced_dom.comp continuous_snd)
    end }

end lattice_ops

namespace submodule

variables {α β : Type*} [topological_space β]

instance [topological_space α] [semiring α] [add_comm_monoid β] [module α β]
  [has_continuous_smul α β] (S : submodule α β) :
  has_continuous_smul α S :=
{ continuous_smul :=
  begin
    rw embedding_subtype_coe.to_inducing.continuous_iff,
    exact continuous_fst.smul
      (continuous_subtype_coe.comp continuous_snd)
  end }

instance [ring α] [add_comm_group β] [module α β] [topological_add_group β] (S : submodule α β) :
  topological_add_group S :=
S.to_add_subgroup.topological_add_group

end submodule

section closure
variables {R : Type u} {M : Type v}
[semiring R] [topological_space R]
[topological_space M] [add_comm_monoid M]
[module R M] [has_continuous_smul R M]

lemma submodule.closure_smul_self_subset (s : submodule R M) :
  (λ p : R × M, p.1 • p.2) '' (set.univ ×ˢ closure s) ⊆ closure s :=
calc
(λ p : R × M, p.1 • p.2) '' (set.univ ×ˢ closure s)
    = (λ p : R × M, p.1 • p.2) '' closure (set.univ ×ˢ s) :
  by simp [closure_prod_eq]
... ⊆ closure ((λ p : R × M, p.1 • p.2) '' (set.univ ×ˢ s)) :
  image_closure_subset_closure_image continuous_smul
... = closure s : begin
  congr,
  ext x,
  refine ⟨_, λ hx, ⟨⟨1, x⟩, ⟨set.mem_univ _, hx⟩, one_smul R _⟩⟩,
  rintros ⟨⟨c, y⟩, ⟨hc, hy⟩, rfl⟩,
  simp [s.smul_mem c hy]
end

lemma submodule.closure_smul_self_eq (s : submodule R M) :
  (λ p : R × M, p.1 • p.2) '' (set.univ ×ˢ closure s) = closure s :=
s.closure_smul_self_subset.antisymm $ λ x hx, ⟨⟨1, x⟩, ⟨set.mem_univ _, hx⟩, one_smul R _⟩

variables [has_continuous_add M]

/-- The (topological-space) closure of a submodule of a topological `R`-module `M` is itself
a submodule. -/
def submodule.topological_closure (s : submodule R M) : submodule R M :=
{ carrier := closure (s : set M),
  smul_mem' := λ c x hx, s.closure_smul_self_subset ⟨⟨c, x⟩, ⟨set.mem_univ _, hx⟩, rfl⟩,
  ..s.to_add_submonoid.topological_closure }

@[simp] lemma submodule.topological_closure_coe (s : submodule R M) :
  (s.topological_closure : set M) = closure (s : set M) :=
rfl

lemma submodule.submodule_topological_closure (s : submodule R M) :
  s ≤ s.topological_closure :=
subset_closure

lemma submodule.is_closed_topological_closure (s : submodule R M) :
  is_closed (s.topological_closure : set M) :=
by convert is_closed_closure

lemma submodule.topological_closure_minimal
  (s : submodule R M) {t : submodule R M} (h : s ≤ t) (ht : is_closed (t : set M)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

lemma submodule.topological_closure_mono {s : submodule R M} {t : submodule R M} (h : s ≤ t) :
  s.topological_closure ≤ t.topological_closure :=
s.topological_closure_minimal (h.trans t.submodule_topological_closure)
  t.is_closed_topological_closure

/-- The topological closure of a closed submodule `s` is equal to `s`. -/
lemma is_closed.submodule_topological_closure_eq {s : submodule R M} (hs : is_closed (s : set M)) :
  s.topological_closure = s :=
le_antisymm (s.topological_closure_minimal rfl.le hs) s.submodule_topological_closure

/-- A subspace is dense iff its topological closure is the entire space. -/
lemma submodule.dense_iff_topological_closure_eq_top {s : submodule R M} :
  dense (s : set M) ↔ s.topological_closure = ⊤ :=
by { rw [←set_like.coe_set_eq, dense_iff_closure_eq], simp }

instance {M' : Type*} [add_comm_monoid M'] [module R M'] [uniform_space M']
  [has_continuous_add M'] [has_continuous_smul R M'] [complete_space M'] (U : submodule R M') :
  complete_space U.topological_closure :=
is_closed_closure.complete_space_coe

end closure

/-- Continuous linear maps between modules. We only put the type classes that are necessary for the
definition, although in applications `M` and `M₂` will be topological modules over the topological
ring `R`. -/
structure continuous_linear_map
  {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂]
  extends M →ₛₗ[σ] M₂ :=
(cont : continuous to_fun . tactic.interactive.continuity')

notation M ` →SL[`:25 σ `] ` M₂ := continuous_linear_map σ M M₂
notation M ` →L[`:25 R `] ` M₂ := continuous_linear_map (ring_hom.id R) M M₂
notation M ` →L⋆[`:25 R `] ` M₂ := continuous_linear_map (star_ring_end R) M M₂

set_option old_structure_cmd true

/-- `continuous_semilinear_map_class F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear maps `M → M₂`.  See also `continuous_linear_map_class F R M M₂` for the case where
`σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class continuous_semilinear_map_class (F : Type*) {R S : out_param Type*} [semiring R] [semiring S]
  (σ : out_param $ R →+* S) (M : out_param Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂] [module R M] [module S M₂]
  extends semilinear_map_class F σ M M₂, continuous_map_class F M M₂

-- `σ`, `R` and `S` become metavariables, but they are all outparams so it's OK
attribute [nolint dangerous_instance] continuous_semilinear_map_class.to_continuous_map_class

/-- `continuous_linear_map_class F R M M₂` asserts `F` is a type of bundled continuous
`R`-linear maps `M → M₂`.  This is an abbreviation for
`continuous_semilinear_map_class F (ring_hom.id R) M M₂`.  -/
abbreviation continuous_linear_map_class (F : Type*)
  (R : out_param Type*) [semiring R]
  (M : out_param Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module R M₂] :=
continuous_semilinear_map_class F (ring_hom.id R) M M₂

set_option old_structure_cmd false

/-- Continuous linear equivalences between modules. We only put the type classes that are necessary
for the definition, although in applications `M` and `M₂` will be topological modules over the
topological semiring `R`. -/
@[nolint has_nonempty_instance]
structure continuous_linear_equiv
  {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂]
  extends M ≃ₛₗ[σ] M₂ :=
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')
(continuous_inv_fun : continuous inv_fun . tactic.interactive.continuity')

notation M ` ≃SL[`:50 σ `] ` M₂ := continuous_linear_equiv σ M M₂
notation M ` ≃L[`:50 R `] ` M₂ := continuous_linear_equiv (ring_hom.id R) M M₂
notation M ` ≃L⋆[`:50 R `] ` M₂ := continuous_linear_equiv (star_ring_end R) M M₂

set_option old_structure_cmd true
/-- `continuous_semilinear_equiv_class F σ M M₂` asserts `F` is a type of bundled continuous
`σ`-semilinear equivs `M → M₂`.  See also `continuous_linear_equiv_class F R M M₂` for the case
where `σ` is the identity map on `R`.  A map `f` between an `R`-module and an `S`-module over a ring
homomorphism `σ : R →+* S` is semilinear if it satisfies the two properties `f (x + y) = f x + f y`
and `f (c • x) = (σ c) • f x`. -/
class continuous_semilinear_equiv_class (F : Type*)
  {R : out_param Type*} {S : out_param Type*} [semiring R] [semiring S] (σ : out_param $ R →+* S)
  {σ' : out_param $ S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : out_param Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂]
  extends semilinear_equiv_class F σ M M₂ :=
(map_continuous  : ∀ (f : F), continuous f . tactic.interactive.continuity')
(inv_continuous : ∀ (f : F), continuous (inv f) . tactic.interactive.continuity')

/-- `continuous_linear_equiv_class F σ M M₂` asserts `F` is a type of bundled continuous
`R`-linear equivs `M → M₂`. This is an abbreviation for
`continuous_semilinear_equiv_class F (ring_hom.id) M M₂`. -/
abbreviation continuous_linear_equiv_class (F : Type*)
  (R : out_param Type*) [semiring R]
  (M : out_param Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : out_param Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module R M₂] :=
continuous_semilinear_equiv_class F (ring_hom.id R) M M₂

set_option old_structure_cmd false

namespace continuous_semilinear_equiv_class
variables (F : Type*)
  {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  {σ' : S →+* R} [ring_hom_inv_pair σ σ'] [ring_hom_inv_pair σ' σ]
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂]

include σ'
-- `σ'` becomes a metavariable, but it's OK since it's an outparam
@[priority 100, nolint dangerous_instance]
instance [s: continuous_semilinear_equiv_class F σ M M₂] :
  continuous_semilinear_map_class F σ M M₂ :=
{ coe := (coe : F → M → M₂),
  coe_injective' := @fun_like.coe_injective F _ _ _,
  ..s }
omit σ'

end continuous_semilinear_equiv_class

section pointwise_limits

variables
{M₁ M₂ α R S : Type*}
[topological_space M₂] [t2_space M₂] [semiring R] [semiring S]
[add_comm_monoid M₁] [add_comm_monoid M₂] [module R M₁] [module S M₂]
[has_continuous_const_smul S M₂]

section

variables (M₁ M₂) (σ : R →+* S)

lemma is_closed_set_of_map_smul : is_closed {f : M₁ → M₂ | ∀ c x, f (c • x) = σ c • f x} :=
begin
  simp only [set.set_of_forall],
  exact is_closed_Inter (λ c, is_closed_Inter (λ x, is_closed_eq (continuous_apply _)
    ((continuous_apply _).const_smul _)))
end

end

variables [has_continuous_add M₂] {σ : R →+* S} {l : filter α}

/-- Constructs a bundled linear map from a function and a proof that this function belongs to the
closure of the set of linear maps. -/
@[simps { fully_applied := ff }] def linear_map_of_mem_closure_range_coe (f : M₁ → M₂)
  (hf : f ∈ closure (set.range (coe_fn : (M₁ →ₛₗ[σ] M₂) → (M₁ → M₂)))) :
  M₁ →ₛₗ[σ] M₂ :=
{ to_fun := f,
  map_smul' := (is_closed_set_of_map_smul M₁ M₂ σ).closure_subset_iff.2
    (set.range_subset_iff.2 linear_map.map_smulₛₗ) hf,
  .. add_monoid_hom_of_mem_closure_range_coe f hf }

/-- Construct a bundled linear map from a pointwise limit of linear maps -/
@[simps { fully_applied := ff }]
def linear_map_of_tendsto (f : M₁ → M₂) (g : α → M₁ →ₛₗ[σ] M₂) [l.ne_bot]
  (h : tendsto (λ a x, g a x) l (𝓝 f)) : M₁ →ₛₗ[σ] M₂ :=
linear_map_of_mem_closure_range_coe f $ mem_closure_of_tendsto h $
  eventually_of_forall $ λ a, set.mem_range_self _

variables (M₁ M₂ σ)

lemma linear_map.is_closed_range_coe :
  is_closed (set.range (coe_fn : (M₁ →ₛₗ[σ] M₂) → (M₁ → M₂))) :=
is_closed_of_closure_subset $ λ f hf, ⟨linear_map_of_mem_closure_range_coe f hf, rfl⟩

end pointwise_limits

namespace continuous_linear_map

section semiring
/-!
### Properties that hold for non-necessarily commutative semirings.
-/

variables
{R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [semiring R₁] [semiring R₂] [semiring R₃]
{σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
{M₁ : Type*} [topological_space M₁] [add_comm_monoid M₁]
{M'₁ : Type*} [topological_space M'₁] [add_comm_monoid M'₁]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[module R₁ M₁] [module R₁ M'₁] [module R₂ M₂] [module R₃ M₃]

/-- Coerce continuous linear maps to linear maps. -/
instance : has_coe (M₁ →SL[σ₁₂] M₂) (M₁ →ₛₗ[σ₁₂] M₂) := ⟨to_linear_map⟩

-- make the coercion the preferred form
@[simp] lemma to_linear_map_eq_coe (f : M₁ →SL[σ₁₂] M₂) : f.to_linear_map = f := rfl

theorem coe_injective : function.injective (coe : (M₁ →SL[σ₁₂] M₂) → (M₁ →ₛₗ[σ₁₂] M₂)) :=
by { intros f g H, cases f, cases g, congr' }

instance : continuous_semilinear_map_class (M₁ →SL[σ₁₂] M₂) σ₁₂ M₁ M₂ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, coe_injective (fun_like.coe_injective h),
  map_add := λ f, map_add f.to_linear_map,
  map_continuous := λ f, f.2,
  map_smulₛₗ := λ f, f.to_linear_map.map_smul' }

/-- Coerce continuous linear maps to functions. -/
-- see Note [function coercion]
instance to_fun : has_coe_to_fun (M₁ →SL[σ₁₂] M₂) (λ _, M₁ → M₂) := ⟨λ f, f.to_fun⟩

@[simp] lemma coe_mk (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ →ₛₗ[σ₁₂] M₂) = f := rfl
@[simp] lemma coe_mk' (f : M₁ →ₛₗ[σ₁₂] M₂) (h) : (mk f h : M₁ → M₂) = f := rfl

@[continuity]
protected lemma continuous (f : M₁ →SL[σ₁₂] M₂) : continuous f := f.2

protected lemma uniform_continuous {E₁ E₂ : Type*} [uniform_space E₁] [uniform_space E₂]
  [add_comm_group E₁] [add_comm_group E₂] [module R₁ E₁] [module R₂ E₂]
  [uniform_add_group E₁] [uniform_add_group E₂] (f : E₁ →SL[σ₁₂] E₂) :
  uniform_continuous f :=
uniform_continuous_add_monoid_hom_of_continuous f.continuous

@[simp, norm_cast] lemma coe_inj {f g : M₁ →SL[σ₁₂] M₂} :
  (f : M₁ →ₛₗ[σ₁₂] M₂) = g ↔ f = g :=
coe_injective.eq_iff

theorem coe_fn_injective : @function.injective (M₁ →SL[σ₁₂] M₂) (M₁ → M₂) coe_fn :=
fun_like.coe_injective

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ →SL[σ₁₂] M₂) : M₁ → M₂ := h

/-- See Note [custom simps projection]. -/
def simps.coe (h : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂ := h

initialize_simps_projections continuous_linear_map
  (to_linear_map_to_fun → apply, to_linear_map → coe)

@[ext] theorem ext {f g : M₁ →SL[σ₁₂] M₂} (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

theorem ext_iff {f g : M₁ →SL[σ₁₂] M₂} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

/-- Copy of a `continuous_linear_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : M₁ →SL[σ₁₂] M₂) (f' : M₁ → M₂) (h : f' = ⇑f) : M₁ →SL[σ₁₂] M₂ :=
{ to_linear_map := f.to_linear_map.copy f' h,
  cont := show continuous f', from h.symm ▸ f.continuous }

-- make some straightforward lemmas available to `simp`.
protected lemma map_zero (f : M₁ →SL[σ₁₂] M₂) : f (0 : M₁) = 0 := map_zero f
protected lemma map_add (f : M₁ →SL[σ₁₂] M₂) (x y : M₁) : f (x + y) = f x + f y := map_add f x y
@[simp]
protected lemma map_smulₛₗ (f : M₁ →SL[σ₁₂] M₂) (c : R₁) (x : M₁) :
  f (c • x) = (σ₁₂ c) • f x := (to_linear_map _).map_smulₛₗ _ _

@[simp]
protected lemma map_smul [module R₁ M₂] (f : M₁ →L[R₁] M₂)(c : R₁) (x : M₁) : f (c • x) = c • f x :=
by simp only [ring_hom.id_apply, continuous_linear_map.map_smulₛₗ]

@[simp, priority 900]
lemma map_smul_of_tower {R S : Type*} [semiring S] [has_smul R M₁]
  [module S M₁] [has_smul R M₂] [module S M₂]
  [linear_map.compatible_smul M₁ M₂ R S] (f : M₁ →L[S] M₂) (c : R) (x : M₁) :
  f (c • x) = c • f x :=
linear_map.compatible_smul.map_smul f c x

protected lemma map_sum {ι : Type*} (f : M₁ →SL[σ₁₂] M₂) (s : finset ι) (g : ι → M₁) :
  f (∑ i in s, g i) = ∑ i in s, f (g i) := f.to_linear_map.map_sum

@[simp, norm_cast] lemma coe_coe (f : M₁ →SL[σ₁₂] M₂) : ⇑(f : M₁ →ₛₗ[σ₁₂] M₂) = f := rfl

@[ext] theorem ext_ring [topological_space R₁] {f g : R₁ →L[R₁] M₁} (h : f 1 = g 1) : f = g :=
coe_inj.1 $ linear_map.ext_ring h

theorem ext_ring_iff [topological_space R₁] {f g : R₁ →L[R₁] M₁} : f = g ↔ f 1 = g 1 :=
⟨λ h, h ▸ rfl, ext_ring⟩

/-- If two continuous linear maps are equal on a set `s`, then they are equal on the closure
of the `submodule.span` of this set. -/
lemma eq_on_closure_span [t2_space M₂] {s : set M₁} {f g : M₁ →SL[σ₁₂] M₂} (h : set.eq_on f g s) :
  set.eq_on f g (closure (submodule.span R₁ s : set M₁)) :=
(linear_map.eq_on_span' h).closure f.continuous g.continuous

/-- If the submodule generated by a set `s` is dense in the ambient module, then two continuous
linear maps equal on `s` are equal. -/
lemma ext_on [t2_space M₂] {s : set M₁} (hs : dense (submodule.span R₁ s : set M₁))
  {f g : M₁ →SL[σ₁₂] M₂} (h : set.eq_on f g s) :
  f = g :=
ext $ λ x, eq_on_closure_span h (hs x)

/-- Under a continuous linear map, the image of the `topological_closure` of a submodule is
contained in the `topological_closure` of its image. -/
lemma _root_.submodule.topological_closure_map [ring_hom_surjective σ₁₂] [topological_space R₁]
  [topological_space R₂] [has_continuous_smul R₁ M₁] [has_continuous_add M₁]
  [has_continuous_smul R₂ M₂] [has_continuous_add M₂] (f : M₁ →SL[σ₁₂] M₂) (s : submodule R₁ M₁) :
  (s.topological_closure.map (f : M₁ →ₛₗ[σ₁₂] M₂))
  ≤ (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topological_closure :=
image_closure_subset_closure_image f.continuous

/-- Under a dense continuous linear map, a submodule whose `topological_closure` is `⊤` is sent to
another such submodule.  That is, the image of a dense set under a map with dense range is dense.
-/
lemma _root_.dense_range.topological_closure_map_submodule [ring_hom_surjective σ₁₂]
  [topological_space R₁] [topological_space R₂] [has_continuous_smul R₁ M₁] [has_continuous_add M₁]
  [has_continuous_smul R₂ M₂] [has_continuous_add M₂] {f : M₁ →SL[σ₁₂] M₂} (hf' : dense_range f)
  {s : submodule R₁ M₁} (hs : s.topological_closure = ⊤) :
  (s.map (f : M₁ →ₛₗ[σ₁₂] M₂)).topological_closure = ⊤ :=
begin
  rw set_like.ext'_iff at hs ⊢,
  simp only [submodule.topological_closure_coe, submodule.top_coe, ← dense_iff_closure_eq] at hs ⊢,
  exact hf'.dense_image f.continuous hs
end

section smul_monoid

variables {S₂ T₂ : Type*} [monoid S₂] [monoid T₂]
variables [distrib_mul_action S₂ M₂] [smul_comm_class R₂ S₂ M₂] [has_continuous_const_smul S₂ M₂]
variables [distrib_mul_action T₂ M₂] [smul_comm_class R₂ T₂ M₂] [has_continuous_const_smul T₂ M₂]

instance : mul_action S₂ (M₁ →SL[σ₁₂] M₂) :=
{ smul := λ c f, ⟨c • f, (f.2.const_smul _ : continuous (λ x, c • f x))⟩,
  one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ a b f, ext $ λ x, mul_smul _ _ _ }

lemma smul_apply (c : S₂) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (c • f) x = c • (f x) := rfl
@[simp, norm_cast]
lemma coe_smul (c : S₂) (f : M₁ →SL[σ₁₂] M₂) : (↑(c • f) : M₁ →ₛₗ[σ₁₂] M₂) = c • f := rfl
@[simp, norm_cast] lemma coe_smul' (c : S₂) (f : M₁ →SL[σ₁₂] M₂) : ⇑(c • f) = c • f := rfl

instance [has_smul S₂ T₂] [smul_assoc_class S₂ T₂ M₂] : smul_assoc_class S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
⟨λ a b f, ext $ λ x, smul_assoc a b (f x)⟩

instance [smul_comm_class S₂ T₂ M₂] : smul_comm_class S₂ T₂ (M₁ →SL[σ₁₂] M₂) :=
⟨λ a b f, ext $ λ x, smul_comm a b (f x)⟩

end smul_monoid

/-- The continuous map that is constantly zero. -/
instance: has_zero (M₁ →SL[σ₁₂] M₂) := ⟨⟨0, continuous_zero⟩⟩
instance : inhabited (M₁ →SL[σ₁₂] M₂) := ⟨0⟩

@[simp] lemma default_def : (default : M₁ →SL[σ₁₂] M₂) = 0 := rfl
@[simp] lemma zero_apply (x : M₁) : (0 : M₁ →SL[σ₁₂] M₂) x = 0 := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : M₁ →SL[σ₁₂] M₂) : M₁ →ₛₗ[σ₁₂] M₂) = 0 := rfl
/- no simp attribute on the next line as simp does not always simplify `0 x` to `0`
when `0` is the zero function, while it does for the zero continuous linear map,
and this is the most important property we care about. -/
@[norm_cast] lemma coe_zero' : ⇑(0 : M₁ →SL[σ₁₂] M₂) = 0 := rfl

instance unique_of_left [subsingleton M₁] : unique (M₁ →SL[σ₁₂] M₂) :=
coe_injective.unique

instance unique_of_right [subsingleton M₂] : unique (M₁ →SL[σ₁₂] M₂) :=
coe_injective.unique

lemma exists_ne_zero {f : M₁ →SL[σ₁₂] M₂} (hf : f ≠ 0) : ∃ x, f x ≠ 0 :=
by { by_contra' h, exact hf (continuous_linear_map.ext h) }

section

variables (R₁ M₁)

/-- the identity map as a continuous linear map. -/
def id : M₁ →L[R₁] M₁ :=
⟨linear_map.id, continuous_id⟩

end

instance : has_one (M₁ →L[R₁] M₁) := ⟨id R₁ M₁⟩

lemma one_def : (1 : M₁ →L[R₁] M₁) = id R₁ M₁ := rfl
lemma id_apply (x : M₁) : id R₁ M₁ x = x := rfl
@[simp, norm_cast] lemma coe_id : (id R₁ M₁ : M₁ →ₗ[R₁] M₁) = linear_map.id := rfl
@[simp, norm_cast] lemma coe_id' : ⇑(id R₁ M₁) = _root_.id := rfl

@[simp, norm_cast] lemma coe_eq_id {f : M₁ →L[R₁] M₁} :
  (f : M₁ →ₗ[R₁] M₁) = linear_map.id ↔ f = id _ _ :=
by rw [← coe_id, coe_inj]

@[simp] lemma one_apply (x : M₁) : (1 : M₁ →L[R₁] M₁) x = x := rfl

section add
variables [has_continuous_add M₂]

instance : has_add (M₁ →SL[σ₁₂] M₂) :=
⟨λ f g, ⟨f + g, f.2.add g.2⟩⟩

@[simp] lemma add_apply (f g : M₁ →SL[σ₁₂] M₂)  (x : M₁) : (f + g) x = f x + g x := rfl
@[simp, norm_cast] lemma coe_add (f g : M₁ →SL[σ₁₂] M₂) : (↑(f + g) : M₁ →ₛₗ[σ₁₂] M₂) = f + g := rfl
@[norm_cast] lemma coe_add' (f g : M₁ →SL[σ₁₂] M₂) : ⇑(f + g) = f + g := rfl

instance : add_comm_monoid (M₁ →SL[σ₁₂] M₂) :=
{ zero := (0 : M₁ →SL[σ₁₂] M₂),
  add := (+),
  zero_add := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_zero := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_comm := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  add_assoc := by intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm],
  nsmul := (•),
  nsmul_zero' := λ f, by { ext, simp },
  nsmul_succ' := λ n f, by { ext, simp [nat.succ_eq_one_add, add_smul] } }

@[simp, norm_cast] lemma coe_sum {ι : Type*} (t : finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
  ↑(∑ d in t, f d) = (∑ d in t, f d : M₁ →ₛₗ[σ₁₂] M₂) :=
(add_monoid_hom.mk (coe : (M₁ →SL[σ₁₂] M₂) → (M₁ →ₛₗ[σ₁₂] M₂)) rfl (λ _ _, rfl)).map_sum _ _

@[simp, norm_cast] lemma coe_sum' {ι : Type*} (t : finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) :
  ⇑(∑ d in t, f d) = ∑ d in t, f d :=
by simp only [← coe_coe, coe_sum, linear_map.coe_fn_sum]

lemma sum_apply {ι : Type*} (t : finset ι) (f : ι → M₁ →SL[σ₁₂] M₂) (b : M₁) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
by simp only [coe_sum', finset.sum_apply]

end add

variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]

/-- Composition of bounded linear maps. -/
def comp (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) : M₁ →SL[σ₁₃] M₃ :=
⟨(g : M₂ →ₛₗ[σ₂₃] M₃).comp ↑f, g.2.comp f.2⟩

infixr ` ∘L `:80 := @continuous_linear_map.comp _ _ _ _ _ _
  (ring_hom.id _) (ring_hom.id _) (ring_hom.id _) _ _ _ _ _ _ _ _ _ _ _ _ ring_hom_comp_triple.ids

@[simp, norm_cast] lemma coe_comp (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
  (h.comp f : M₁ →ₛₗ[σ₁₃] M₃) = (h : M₂ →ₛₗ[σ₂₃] M₃).comp (f : M₁ →ₛₗ[σ₁₂] M₂) := rfl

include σ₁₃
@[simp, norm_cast] lemma coe_comp' (h : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
  ⇑(h.comp f) = h ∘ f := rfl

lemma comp_apply (g : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : (g.comp f) x = g (f x) := rfl
omit σ₁₃

@[simp] theorem comp_id (f : M₁ →SL[σ₁₂] M₂) : f.comp (id R₁ M₁) = f :=
ext $ λ x, rfl

@[simp] theorem id_comp (f : M₁ →SL[σ₁₂] M₂) : (id R₂ M₂).comp f = f :=
ext $ λ x, rfl

include σ₁₃
@[simp] theorem comp_zero (g : M₂ →SL[σ₂₃] M₃) : g.comp (0 : M₁ →SL[σ₁₂] M₂) = 0 :=
by { ext, simp }

@[simp] theorem zero_comp (f : M₁ →SL[σ₁₂] M₂) : (0 : M₂ →SL[σ₂₃] M₃).comp f = 0 :=
by { ext, simp }

@[simp] lemma comp_add [has_continuous_add M₂] [has_continuous_add M₃]
  (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M₁ →SL[σ₁₂] M₂) :
  g.comp (f₁ + f₂) = g.comp f₁ + g.comp f₂ :=
by { ext, simp }

@[simp] lemma add_comp [has_continuous_add M₃]
  (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M₁ →SL[σ₁₂] M₂) :
  (g₁ + g₂).comp f = g₁.comp f + g₂.comp f :=
by { ext, simp }
omit σ₁₃

theorem comp_assoc {R₄ : Type*} [semiring R₄] [module R₄ M₄] {σ₁₄ : R₁ →+* R₄} {σ₂₄ : R₂ →+* R₄}
  {σ₃₄ : R₃ →+* R₄} [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄] [ring_hom_comp_triple σ₂₃ σ₃₄ σ₂₄]
  [ring_hom_comp_triple σ₁₂ σ₂₄ σ₁₄] (h : M₃ →SL[σ₃₄] M₄) (g : M₂ →SL[σ₂₃] M₃)
  (f : M₁ →SL[σ₁₂] M₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
rfl

instance : has_mul (M₁ →L[R₁] M₁) := ⟨comp⟩

lemma mul_def (f g : M₁ →L[R₁] M₁) : f * g = f.comp g := rfl

@[simp] lemma coe_mul (f g : M₁ →L[R₁] M₁) : ⇑(f * g) = f ∘ g := rfl

lemma mul_apply (f g : M₁ →L[R₁] M₁) (x : M₁) : (f * g) x = f (g x) := rfl

instance : monoid_with_zero (M₁ →L[R₁] M₁) :=
{ mul := (*),
  one := 1,
  zero := 0,
  mul_zero := λ f, ext $ λ _, map_zero f,
  zero_mul := λ _, ext $ λ _, rfl,
  mul_one := λ _, ext $ λ _, rfl,
  one_mul := λ _, ext $ λ _, rfl,
  mul_assoc := λ _ _ _, ext $ λ _, rfl, }

instance [has_continuous_add M₁] : semiring (M₁ →L[R₁] M₁) :=
{ mul := (*),
  one := 1,
  left_distrib := λ f g h, ext $ λ x, map_add f (g x) (h x),
  right_distrib := λ _ _ _, ext $ λ _, linear_map.add_apply _ _ _,
  ..continuous_linear_map.monoid_with_zero,
  ..continuous_linear_map.add_comm_monoid }

/-- `continuous_linear_map.to_linear_map` as a `ring_hom`.-/
@[simps]
def to_linear_map_ring_hom [has_continuous_add M₁] : (M₁ →L[R₁] M₁) →+* (M₁ →ₗ[R₁] M₁) :=
{ to_fun := to_linear_map,
  map_zero' := rfl,
  map_one' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl }

section apply_action
variables [has_continuous_add M₁]

/-- The tautological action by `M₁ →L[R₁] M₁` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_module : module (M₁ →L[R₁] M₁) M₁ :=
module.comp_hom _ to_linear_map_ring_hom

@[simp] protected lemma smul_def (f : M₁ →L[R₁] M₁) (a : M₁) : f • a = f a := rfl

/-- `continuous_linear_map.apply_module` is faithful. -/
instance apply_has_faithful_smul : has_faithful_smul (M₁ →L[R₁] M₁) M₁ :=
⟨λ _ _, continuous_linear_map.ext⟩

instance apply_smul_comm_class : smul_comm_class R₁ (M₁ →L[R₁] M₁) M₁ :=
{ smul_comm := λ r e m, (e.map_smul r m).symm }

instance apply_smul_comm_class' : smul_comm_class (M₁ →L[R₁] M₁) R₁ M₁ :=
{ smul_comm := continuous_linear_map.map_smul }

instance : has_continuous_const_smul (M₁ →L[R₁] M₁) M₁ :=
⟨continuous_linear_map.continuous⟩

end apply_action

/-- The cartesian product of two bounded linear maps, as a bounded linear map. -/
protected def prod [module R₁ M₂] [module R₁ M₃] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₁ →L[R₁] M₃) :
  M₁ →L[R₁] (M₂ × M₃) :=
⟨(f₁ : M₁ →ₗ[R₁] M₂).prod f₂, f₁.2.prod_mk f₂.2⟩

@[simp, norm_cast] lemma coe_prod [module R₁ M₂] [module R₁ M₃] (f₁ : M₁ →L[R₁] M₂)
  (f₂ : M₁ →L[R₁] M₃) :
  (f₁.prod f₂ : M₁ →ₗ[R₁] M₂ × M₃) = linear_map.prod f₁ f₂ :=
rfl

@[simp, norm_cast] lemma prod_apply [module R₁ M₂] [module R₁ M₃] (f₁ : M₁ →L[R₁] M₂)
  (f₂ : M₁ →L[R₁] M₃) (x : M₁) :
  f₁.prod f₂ x = (f₁ x, f₂ x) :=
rfl

section

variables (R₁ M₁ M₂)

/-- The left injection into a product is a continuous linear map. -/
def inl [module R₁ M₂] : M₁ →L[R₁] M₁ × M₂ := (id R₁ M₁).prod 0

/-- The right injection into a product is a continuous linear map. -/
def inr [module R₁ M₂] : M₂ →L[R₁] M₁ × M₂ := (0 : M₂ →L[R₁] M₁).prod (id R₁ M₂)

end

@[simp] lemma inl_apply [module R₁ M₂] (x : M₁) : inl R₁ M₁ M₂ x = (x, 0) := rfl
@[simp] lemma inr_apply [module R₁ M₂] (x : M₂) : inr R₁ M₁ M₂ x = (0, x) := rfl

@[simp, norm_cast] lemma coe_inl [module R₁ M₂] :
  (inl R₁ M₁ M₂ : M₁ →ₗ[R₁] M₁ × M₂) = linear_map.inl R₁ M₁ M₂ := rfl
@[simp, norm_cast] lemma coe_inr [module R₁ M₂] :
  (inr R₁ M₁ M₂ : M₂ →ₗ[R₁] M₁ × M₂) = linear_map.inr R₁ M₁ M₂ := rfl

/-- Kernel of a continuous linear map. -/
def ker (f : M₁ →SL[σ₁₂] M₂) : submodule R₁ M₁ := (f : M₁ →ₛₗ[σ₁₂] M₂).ker

@[norm_cast] lemma ker_coe (f : M₁ →SL[σ₁₂] M₂) : (f : M₁ →ₛₗ[σ₁₂] M₂).ker = f.ker := rfl

@[simp] lemma mem_ker {f : M₁ →SL[σ₁₂] M₂} {x} : x ∈ f.ker ↔ f x = 0 := linear_map.mem_ker

lemma is_closed_ker [t1_space M₂] (f : M₁ →SL[σ₁₂] M₂) : is_closed (f.ker : set M₁) :=
continuous_iff_is_closed.1 f.cont _ is_closed_singleton

@[simp] lemma apply_ker (f : M₁ →SL[σ₁₂] M₂) (x : f.ker) : f x = 0 := mem_ker.1 x.2

lemma is_complete_ker {M' : Type*} [uniform_space M'] [complete_space M'] [add_comm_monoid M']
  [module R₁ M'] [t1_space M₂] (f : M' →SL[σ₁₂] M₂) :
  is_complete (f.ker : set M') :=
f.is_closed_ker.is_complete

instance complete_space_ker {M' : Type*} [uniform_space M'] [complete_space M'] [add_comm_monoid M']
  [module R₁ M'] [t1_space M₂] (f : M' →SL[σ₁₂] M₂) :
  complete_space f.ker :=
f.is_closed_ker.complete_space_coe

@[simp] lemma ker_prod [module R₁ M₂] [module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  ker (f.prod g) = ker f ⊓ ker g :=
linear_map.ker_prod f g

/-- Range of a continuous linear map. -/
def range [ring_hom_surjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) : submodule R₂ M₂ :=
(f : M₁ →ₛₗ[σ₁₂] M₂).range

lemma range_coe [ring_hom_surjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) : (f.range : set M₂) = set.range f :=
linear_map.range_coe _
lemma mem_range [ring_hom_surjective σ₁₂] {f : M₁ →SL[σ₁₂] M₂} {y} : y ∈ f.range ↔ ∃ x, f x = y :=
linear_map.mem_range

lemma mem_range_self [ring_hom_surjective σ₁₂] (f : M₁ →SL[σ₁₂] M₂) (x : M₁) : f x ∈ f.range :=
mem_range.2 ⟨x, rfl⟩

lemma range_prod_le [module R₁ M₂] [module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  range (f.prod g) ≤ (range f).prod (range g) :=
(f : M₁ →ₗ[R₁] M₂).range_prod_le g

/-- Restrict codomain of a continuous linear map. -/
def cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
  M₁ →SL[σ₁₂] p :=
{ cont := continuous_subtype_mk h f.continuous,
  to_linear_map := (f : M₁ →ₛₗ[σ₁₂] M₂).cod_restrict p h}

@[norm_cast] lemma coe_cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
  (f.cod_restrict p h : M₁ →ₛₗ[σ₁₂] p) = (f : M₁ →ₛₗ[σ₁₂] M₂).cod_restrict p h :=
rfl

@[simp] lemma coe_cod_restrict_apply (f : M₁ →SL[σ₁₂] M₂) (p : submodule R₂ M₂) (h : ∀ x, f x ∈ p)
  (x) :
  (f.cod_restrict p h x : M₂) = f x :=
rfl

@[simp] lemma ker_cod_restrict (f : M₁ →SL[σ₁₂] M₂) (p : submodule R₂ M₂) (h : ∀ x, f x ∈ p) :
  ker (f.cod_restrict p h) = ker f :=
(f : M₁ →ₛₗ[σ₁₂] M₂).ker_cod_restrict p h

/-- `submodule.subtype` as a `continuous_linear_map`. -/
def _root_.submodule.subtypeL (p : submodule R₁ M₁) : p →L[R₁] M₁ :=
{ cont := continuous_subtype_val,
  to_linear_map := p.subtype }

@[simp, norm_cast] lemma _root_.submodule.coe_subtypeL (p : submodule R₁ M₁) :
  (p.subtypeL : p →ₗ[R₁] M₁) = p.subtype :=
rfl

@[simp] lemma _root_.submodule.coe_subtypeL' (p : submodule R₁ M₁) :
  ⇑p.subtypeL = p.subtype :=
rfl

@[simp, norm_cast] lemma _root_.submodule.subtypeL_apply (p : submodule R₁ M₁) (x : p) :
  p.subtypeL x = x :=
rfl

@[simp] lemma _root_.submodule.range_subtypeL (p : submodule R₁ M₁) : p.subtypeL.range = p :=
submodule.range_subtype _

@[simp] lemma _root_.submodule.ker_subtypeL (p : submodule R₁ M₁) : p.subtypeL.ker = ⊥ :=
submodule.ker_subtype _

variables (R₁ M₁ M₂)

/-- `prod.fst` as a `continuous_linear_map`. -/
def fst [module R₁ M₂] : M₁ × M₂ →L[R₁] M₁ :=
{ cont := continuous_fst, to_linear_map := linear_map.fst R₁ M₁ M₂ }

/-- `prod.snd` as a `continuous_linear_map`. -/
def snd [module R₁ M₂] : M₁ × M₂ →L[R₁] M₂ :=
{ cont := continuous_snd, to_linear_map := linear_map.snd R₁ M₁ M₂ }

variables {R₁ M₁ M₂}

@[simp, norm_cast] lemma coe_fst [module R₁ M₂] : ↑(fst R₁ M₁ M₂) = linear_map.fst R₁ M₁ M₂ := rfl

@[simp, norm_cast] lemma coe_fst' [module R₁ M₂] : ⇑(fst R₁ M₁ M₂) = prod.fst := rfl

@[simp, norm_cast] lemma coe_snd [module R₁ M₂] : ↑(snd R₁ M₁ M₂) = linear_map.snd R₁ M₁ M₂ := rfl

@[simp, norm_cast] lemma coe_snd' [module R₁ M₂] : ⇑(snd R₁ M₁ M₂) = prod.snd := rfl

@[simp] lemma fst_prod_snd [module R₁ M₂] : (fst R₁ M₁ M₂).prod (snd R₁ M₁ M₂) = id R₁ (M₁ × M₂) :=
  ext $ λ ⟨x, y⟩, rfl

@[simp] lemma fst_comp_prod [module R₁ M₂] [module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  (fst R₁ M₂ M₃).comp (f.prod g) = f :=
ext $ λ x, rfl

@[simp] lemma snd_comp_prod [module R₁ M₂] [module R₁ M₃] (f : M₁ →L[R₁] M₂) (g : M₁ →L[R₁] M₃) :
  (snd R₁ M₂ M₃).comp (f.prod g) = g :=
ext $ λ x, rfl

/-- `prod.map` of two continuous linear maps. -/
def prod_map [module R₁ M₂] [module R₁ M₃] [module R₁ M₄] (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  (M₁ × M₃) →L[R₁] (M₂ × M₄) :=
(f₁.comp (fst R₁ M₁ M₃)).prod (f₂.comp (snd R₁ M₁ M₃))

@[simp, norm_cast] lemma coe_prod_map [module R₁ M₂] [module R₁ M₃] [module R₁ M₄]
  (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  ↑(f₁.prod_map f₂) = ((f₁ : M₁ →ₗ[R₁] M₂).prod_map (f₂ : M₃ →ₗ[R₁] M₄)) :=
rfl

@[simp, norm_cast] lemma coe_prod_map' [module R₁ M₂] [module R₁ M₃] [module R₁ M₄]
  (f₁ : M₁ →L[R₁] M₂) (f₂ : M₃ →L[R₁] M₄) :
  ⇑(f₁.prod_map f₂) = prod.map f₁ f₂ :=
rfl

/-- The continuous linear map given by `(x, y) ↦ f₁ x + f₂ y`. -/
def coprod [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃] (f₁ : M₁ →L[R₁] M₃)
  (f₂ : M₂ →L[R₁] M₃) :
  (M₁ × M₂) →L[R₁] M₃ :=
⟨linear_map.coprod f₁ f₂, (f₁.cont.comp continuous_fst).add (f₂.cont.comp continuous_snd)⟩

@[norm_cast, simp] lemma coe_coprod [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃]
  (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) :
  (f₁.coprod f₂ : (M₁ × M₂) →ₗ[R₁] M₃) = linear_map.coprod f₁ f₂ :=
rfl

@[simp] lemma coprod_apply [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃]
  (f₁ : M₁ →L[R₁] M₃) (f₂ : M₂ →L[R₁] M₃) (x) :
  f₁.coprod f₂ x = f₁ x.1 + f₂ x.2 := rfl

lemma range_coprod [module R₁ M₂] [module R₁ M₃] [has_continuous_add M₃] (f₁ : M₁ →L[R₁] M₃)
  (f₂ : M₂ →L[R₁] M₃) :
  (f₁.coprod f₂).range = f₁.range ⊔ f₂.range :=
linear_map.range_coprod _ _

section

variables {R S : Type*} [semiring R] [semiring S] [module R M₁] [module R M₂] [module R S]
  [module S M₂] [smul_assoc_class R S M₂] [topological_space S] [has_continuous_smul S M₂]

/-- The linear map `λ x, c x • f`.  Associates to a scalar-valued linear map and an element of
`M₂` the `M₂`-valued linear map obtained by multiplying the two (a.k.a. tensoring by `M₂`).
See also `continuous_linear_map.smul_rightₗ` and `continuous_linear_map.smul_rightL`. -/
def smul_right (c : M₁ →L[R] S) (f : M₂) : M₁ →L[R] M₂ :=
{ cont := c.2.smul continuous_const,
  ..c.to_linear_map.smul_right f }

@[simp]
lemma smul_right_apply {c : M₁ →L[R] S} {f : M₂} {x : M₁} :
  (smul_right c f : M₁ → M₂) x = c x • f :=
rfl

end

variables [module R₁ M₂] [topological_space R₁] [has_continuous_smul R₁ M₂]

@[simp]
lemma smul_right_one_one (c : R₁ →L[R₁] M₂) : smul_right (1 : R₁ →L[R₁] R₁) (c 1) = c :=
by ext; simp [← continuous_linear_map.map_smul_of_tower]

@[simp]
lemma smul_right_one_eq_iff {f f' : M₂} :
  smul_right (1 : R₁ →L[R₁] R₁) f = smul_right (1 : R₁ →L[R₁] R₁) f' ↔ f = f' :=
by simp only [ext_ring_iff, smul_right_apply, one_apply, one_smul]

lemma smul_right_comp [has_continuous_mul R₁] {x : M₂} {c : R₁} :
  (smul_right (1 : R₁ →L[R₁] R₁) x).comp (smul_right (1 : R₁ →L[R₁] R₁) c) =
    smul_right (1 : R₁ →L[R₁] R₁) (c • x) :=
by { ext, simp [mul_smul] }

end semiring

section pi
variables
  {R : Type*} [semiring R]
  {M : Type*} [topological_space M] [add_comm_monoid M] [module R M]
  {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂] [module R M₂]
  {ι : Type*} {φ : ι → Type*} [∀i, topological_space (φ i)] [∀i, add_comm_monoid (φ i)]
  [∀i, module R (φ i)]

/-- `pi` construction for continuous linear functions. From a family of continuous linear functions
it produces a continuous linear function into a family of topological modules. -/
def pi (f : Πi, M →L[R] φ i) : M →L[R] (Πi, φ i) :=
⟨linear_map.pi (λ i, f i), continuous_pi (λ i, (f i).continuous)⟩

@[simp] lemma coe_pi' (f : Π i, M →L[R] φ i) : ⇑(pi f) = λ c i, f i c := rfl
@[simp] lemma coe_pi (f : Π i, M →L[R] φ i) :
  (pi f : M →ₗ[R] Π i, φ i) = linear_map.pi (λ i, f i) :=
rfl

lemma pi_apply (f : Πi, M →L[R] φ i) (c : M) (i : ι) :
  pi f c i = f i c := rfl

lemma pi_eq_zero (f : Πi, M →L[R] φ i) : pi f = 0 ↔ (∀i, f i = 0) :=
by { simp only [ext_iff, pi_apply, function.funext_iff], exact forall_swap }

lemma pi_zero : pi (λi, 0 : Πi, M →L[R] φ i) = 0 := ext $ λ _, rfl

lemma pi_comp (f : Πi, M →L[R] φ i) (g : M₂ →L[R] M) : (pi f).comp g = pi (λi, (f i).comp g) := rfl

/-- The projections from a family of topological modules are continuous linear maps. -/
def proj (i : ι) : (Πi, φ i) →L[R] φ i :=
⟨linear_map.proj i, continuous_apply _⟩

@[simp] lemma proj_apply (i : ι) (b : Πi, φ i) : (proj i : (Πi, φ i) →L[R] φ i) b = b i := rfl

lemma proj_pi (f : Πi, M₂ →L[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Πi, φ i)) = ⊥ :=
linear_map.infi_ker_proj

variables (R φ)

/-- If `I` and `J` are complementary index sets, the product of the kernels of the `J`th projections
of `φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv {I J : set ι} [decidable_pred (λi, i ∈ I)]
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) :
  (⨅i ∈ J, ker (proj i) : submodule R (Πi, φ i)) ≃L[R] (Πi:I, φ i) :=
⟨ linear_map.infi_ker_proj_equiv R φ hd hu,
  continuous_pi (λ i, begin
    have := @continuous_subtype_coe _ _ (λ x, x ∈ (⨅i ∈ J, ker (proj i) : submodule R (Πi, φ i))),
    have := continuous.comp (by exact continuous_apply i) this,
    exact this
  end),
  continuous_subtype_mk _ (continuous_pi (λ i, begin
    dsimp, split_ifs; [apply continuous_apply, exact continuous_zero]
  end)) ⟩

end pi

section ring

variables
{R : Type*} [ring R] {R₂ : Type*} [ring R₂] {R₃ : Type*} [ring R₃]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_group M₄]
[module R M] [module R₂ M₂] [module R₃ M₃]
{σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}

section

protected lemma map_neg (f : M →SL[σ₁₂] M₂) (x : M) : f (-x) = - (f x) := map_neg _ _
protected lemma map_sub (f : M →SL[σ₁₂] M₂) (x y : M) : f (x - y) = f x - f y := map_sub _ _ _
@[simp] lemma sub_apply' (f g : M →SL[σ₁₂] M₂) (x : M) : ((f : M →ₛₗ[σ₁₂] M₂) - g) x = f x - g x :=
rfl
end

section
variables [module R M₂] [module R M₃] [module R M₄]

lemma range_prod_eq {f : M →L[R] M₂} {g : M →L[R] M₃} (h : ker f ⊔ ker g = ⊤) :
  range (f.prod g) = (range f).prod (range g) :=
linear_map.range_prod_eq h

lemma ker_prod_ker_le_ker_coprod [has_continuous_add M₃]
  (f : M →L[R] M₃) (g : M₂ →L[R] M₃) :
  (ker f).prod (ker g) ≤ ker (f.coprod g) :=
linear_map.ker_prod_ker_le_ker_coprod f.to_linear_map g.to_linear_map

lemma ker_coprod_of_disjoint_range [has_continuous_add M₃]
  (f : M →L[R] M₃) (g : M₂ →L[R] M₃) (hd : disjoint f.range g.range) :
  ker (f.coprod g) = (ker f).prod (ker g) :=
linear_map.ker_coprod_of_disjoint_range f.to_linear_map g.to_linear_map hd
end

section
variables [topological_add_group M₂]

instance : has_neg (M →SL[σ₁₂] M₂) := ⟨λ f, ⟨-f, f.2.neg⟩⟩

@[simp] lemma neg_apply (f : M →SL[σ₁₂] M₂) (x : M) : (-f) x = - (f x) := rfl
@[simp, norm_cast] lemma coe_neg (f : M →SL[σ₁₂] M₂) : (↑(-f) : M →ₛₗ[σ₁₂] M₂) = -f := rfl
@[norm_cast] lemma coe_neg' (f : M →SL[σ₁₂] M₂) : ⇑(-f) = -f := rfl

instance : has_sub (M →SL[σ₁₂] M₂) := ⟨λ f g, ⟨f - g, f.2.sub g.2⟩⟩

instance : add_comm_group (M →SL[σ₁₂] M₂) :=
by refine
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := _,
  nsmul := (•),
  zsmul := (•),
  zsmul_zero' := λ f, by { ext, simp },
  zsmul_succ' := λ n f, by { ext, simp [add_smul, add_comm] },
  zsmul_neg' := λ n f, by { ext, simp [nat.succ_eq_add_one, add_smul] },
  .. continuous_linear_map.add_comm_monoid, .. };
intros; ext; apply_rules [zero_add, add_assoc, add_zero, add_left_neg, add_comm, sub_eq_add_neg]

lemma sub_apply (f g : M →SL[σ₁₂] M₂) (x : M) : (f - g) x = f x - g x := rfl
@[simp, norm_cast] lemma coe_sub (f g : M →SL[σ₁₂] M₂) : (↑(f - g) : M →ₛₗ[σ₁₂] M₂) = f - g := rfl
@[simp, norm_cast] lemma coe_sub' (f g : M →SL[σ₁₂] M₂) : ⇑(f - g) = f - g := rfl

end

@[simp] lemma comp_neg [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [topological_add_group M₂]
  [topological_add_group M₃] (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
  g.comp (-f) = -g.comp f :=
by { ext, simp }

@[simp] lemma neg_comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [topological_add_group M₃]
  (g : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
  (-g).comp f = -g.comp f :=
by { ext, simp }

@[simp] lemma comp_sub [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [topological_add_group M₂]
  [topological_add_group M₃] (g : M₂ →SL[σ₂₃] M₃) (f₁ f₂ : M →SL[σ₁₂] M₂) :
  g.comp (f₁ - f₂) = g.comp f₁ - g.comp f₂ :=
by { ext, simp }

@[simp] lemma sub_comp [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [topological_add_group M₃]
  (g₁ g₂ : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
  (g₁ - g₂).comp f = g₁.comp f - g₂.comp f :=
by { ext, simp }

instance [topological_add_group M] : ring (M →L[R] M) :=
{ mul := (*),
  one := 1,
  ..continuous_linear_map.semiring,
  ..continuous_linear_map.add_comm_group }

lemma smul_right_one_pow [topological_space R] [topological_ring R] (c : R) (n : ℕ) :
  (smul_right (1 : R →L[R] R) c)^n = smul_right (1 : R →L[R] R) (c^n) :=
begin
  induction n with n ihn,
  { ext, simp },
  { rw [pow_succ, ihn, mul_def, smul_right_comp, smul_eq_mul, pow_succ'] }
end

section
variables {σ₂₁ : R₂ →+* R} [ring_hom_inv_pair σ₁₂ σ₂₁]

/-- Given a right inverse `f₂ : M₂ →L[R] M` to `f₁ : M →L[R] M₂`,
`proj_ker_of_right_inverse f₁ f₂ h` is the projection `M →L[R] f₁.ker` along `f₂.range`. -/
def proj_ker_of_right_inverse [topological_add_group M] (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M)
  (h : function.right_inverse f₂ f₁) :
  M →L[R] f₁.ker :=
(id R M - f₂.comp f₁).cod_restrict f₁.ker $ λ x, by simp [h (f₁ x)]

@[simp] lemma coe_proj_ker_of_right_inverse_apply [topological_add_group M]
  (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M) (h : function.right_inverse f₂ f₁) (x : M) :
  (f₁.proj_ker_of_right_inverse f₂ h x : M) = x - f₂ (f₁ x) :=
rfl

@[simp] lemma proj_ker_of_right_inverse_apply_idem [topological_add_group M]
  (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M) (h : function.right_inverse f₂ f₁) (x : f₁.ker) :
  f₁.proj_ker_of_right_inverse f₂ h x = x :=
subtype.ext_iff_val.2 $ by simp

@[simp] lemma proj_ker_of_right_inverse_comp_inv [topological_add_group M]
  (f₁ : M →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M) (h : function.right_inverse f₂ f₁) (y : M₂) :
  f₁.proj_ker_of_right_inverse f₂ h (f₂ y) = 0 :=
subtype.ext_iff_val.2 $ by simp [h y]

end

end ring

section division_monoid
variables {R M : Type*}

/-- A nonzero continuous linear functional is open. -/
protected lemma is_open_map_of_ne_zero [topological_space R] [division_ring R]
  [has_continuous_sub R] [add_comm_group M] [topological_space M] [has_continuous_add M]
  [module R M] [has_continuous_smul R M] (f : M →L[R] R) (hf : f ≠ 0) : is_open_map f :=
let ⟨x, hx⟩ := exists_ne_zero hf in is_open_map.of_sections $ λ y,
    ⟨λ a, y + (a - f y) • (f x)⁻¹ • x, continuous.continuous_at $ by continuity,
      by simp, λ a, by simp [hx]⟩

end division_monoid

section smul_monoid

-- The M's are used for semilinear maps, and the N's for plain linear maps
variables {R R₂ R₃ S S₃ : Type*} [semiring R] [semiring R₂] [semiring R₃]
  [monoid S] [monoid S₃]
  {M : Type*} [topological_space M] [add_comm_monoid M] [module R M]
  {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂] [module R₂ M₂]
  {M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃] [module R₃ M₃]
  {N₂ : Type*} [topological_space N₂] [add_comm_monoid N₂] [module R N₂]
  {N₃ : Type*} [topological_space N₃] [add_comm_monoid N₃] [module R N₃]
  [distrib_mul_action S₃ M₃] [smul_comm_class R₃ S₃ M₃] [has_continuous_const_smul S₃ M₃]
  [distrib_mul_action S N₃] [smul_comm_class R S N₃] [has_continuous_const_smul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]

include σ₁₃
@[simp] lemma smul_comp (c : S₃) (h : M₂ →SL[σ₂₃] M₃) (f : M →SL[σ₁₂] M₂) :
  (c • h).comp f = c • (h.comp f) := rfl
omit σ₁₃

variables [distrib_mul_action S₃ M₂] [has_continuous_const_smul S₃ M₂] [smul_comm_class R₂ S₃ M₂]
variables [distrib_mul_action S N₂] [has_continuous_const_smul S N₂] [smul_comm_class R S N₂]

@[simp] lemma comp_smul [linear_map.compatible_smul N₂ N₃ S R]
  (hₗ : N₂ →L[R] N₃) (c : S) (fₗ : M →L[R] N₂) :
  hₗ.comp (c • fₗ) = c • (hₗ.comp fₗ) :=
by { ext x, exact hₗ.map_smul_of_tower c (fₗ x) }

include σ₁₃
@[simp] lemma comp_smulₛₗ [smul_comm_class R₂ R₂ M₂] [smul_comm_class R₃ R₃ M₃]
  [has_continuous_const_smul R₂ M₂] [has_continuous_const_smul R₃ M₃]
  (h : M₂ →SL[σ₂₃] M₃) (c : R₂) (f : M →SL[σ₁₂] M₂) :
  h.comp (c • f) = (σ₂₃ c) • (h.comp f) :=
by { ext x, simp only [coe_smul', coe_comp', function.comp_app, pi.smul_apply,
                      continuous_linear_map.map_smulₛₗ] }
omit σ₁₃

instance [has_continuous_add M₂] : distrib_mul_action S₃ (M →SL[σ₁₂] M₂) :=
{ smul_add := λ a f g, ext $ λ x, smul_add a (f x) (g x),
  smul_zero := λ a, ext $ λ x, smul_zero _ }

end smul_monoid

section smul

-- The M's are used for semilinear maps, and the N's for plain linear maps
variables {R R₂ R₃ S S₃ : Type*} [semiring R] [semiring R₂] [semiring R₃]
  [semiring S] [semiring S₃]
  {M : Type*} [topological_space M] [add_comm_monoid M] [module R M]
  {M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂] [module R₂ M₂]
  {M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃] [module R₃ M₃]
  {N₂ : Type*} [topological_space N₂] [add_comm_monoid N₂] [module R N₂]
  {N₃ : Type*} [topological_space N₃] [add_comm_monoid N₃] [module R N₃]
  [module S₃ M₃] [smul_comm_class R₃ S₃ M₃] [has_continuous_const_smul S₃ M₃]
  [module S N₂] [has_continuous_const_smul S N₂] [smul_comm_class R S N₂]
  [module S N₃] [smul_comm_class R S N₃] [has_continuous_const_smul S N₃]
  {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
  (c : S) (h : M₂ →SL[σ₂₃] M₃) (f g : M →SL[σ₁₂] M₂) (x y z : M)

/-- `continuous_linear_map.prod` as an `equiv`. -/
@[simps apply] def prod_equiv : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ (M →L[R] N₂ × N₃) :=
{ to_fun := λ f, f.1.prod f.2,
  inv_fun := λ f, ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩,
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl }

lemma prod_ext_iff {f g : M × N₂ →L[R] N₃} :
  f = g ↔ f.comp (inl _ _ _) = g.comp (inl _ _ _) ∧ f.comp (inr _ _ _) = g.comp (inr _ _ _) :=
by { simp only [← coe_inj, linear_map.prod_ext_iff], refl }

@[ext] lemma prod_ext {f g : M × N₂ →L[R] N₃} (hl : f.comp (inl _ _ _) = g.comp (inl _ _ _))
  (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f = g :=
prod_ext_iff.2 ⟨hl, hr⟩

variables [has_continuous_add M₂] [has_continuous_add M₃] [has_continuous_add N₂]

instance : module S₃ (M →SL[σ₁₃] M₃) :=
{ zero_smul := λ _, ext $ λ _, zero_smul _ _,
  add_smul  := λ _ _ _, ext $ λ _, add_smul _ _ _ }

instance [module S₃ᵐᵒᵖ M₃] [is_central_scalar S₃ M₃] : is_central_scalar S₃ (M →SL[σ₁₃] M₃) :=
{ op_smul_eq_smul := λ _ _, ext $ λ _, op_smul_eq_smul _ _ }

variables (S) [has_continuous_add N₃]

/-- `continuous_linear_map.prod` as a `linear_equiv`. -/
@[simps apply] def prodₗ : ((M →L[R] N₂) × (M →L[R] N₃)) ≃ₗ[S] (M →L[R] N₂ × N₃) :=
{ map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  .. prod_equiv }

/-- The coercion from `M →L[R] M₂` to `M →ₗ[R] M₂`, as a linear map. -/
@[simps]
def coe_lm : (M →L[R] N₃) →ₗ[S] (M →ₗ[R] N₃) :=
{ to_fun := coe,
  map_add' := λ f g, coe_add f g,
  map_smul' := λ c f, coe_smul c f }

variables {S} (σ₁₃)

/-- The coercion from `M →SL[σ] M₂` to `M →ₛₗ[σ] M₂`, as a linear map. -/
@[simps]
def coe_lmₛₗ : (M →SL[σ₁₃] M₃) →ₗ[S₃] (M →ₛₗ[σ₁₃] M₃) :=
{ to_fun := coe,
  map_add' := λ f g, coe_add f g,
  map_smul' := λ c f, coe_smul c f }

variables {σ₁₃}

end smul

section smul_rightₗ

variables {R S T M M₂ : Type*} [semiring R] [semiring S] [semiring T] [module R S]
  [add_comm_monoid M₂] [module R M₂] [module S M₂] [smul_assoc_class R S M₂]
  [topological_space S] [topological_space M₂] [has_continuous_smul S M₂]
  [topological_space M] [add_comm_monoid M] [module R M] [has_continuous_add M₂]
  [module T M₂] [has_continuous_const_smul T M₂]
  [smul_comm_class R T M₂] [smul_comm_class S T M₂]

/-- Given `c : E →L[𝕜] 𝕜`, `c.smul_rightₗ` is the linear map from `F` to `E →L[𝕜] F`
sending `f` to `λ e, c e • f`. See also `continuous_linear_map.smul_rightL`. -/
def smul_rightₗ (c : M →L[R] S) : M₂ →ₗ[T] (M →L[R] M₂) :=
{ to_fun := c.smul_right,
  map_add' := λ x y, by { ext e, apply smul_add },
  map_smul' := λ a x, by { ext e, dsimp, apply smul_comm } }

@[simp] lemma coe_smul_rightₗ (c : M →L[R] S) :
  ⇑(smul_rightₗ c : M₂ →ₗ[T] (M →L[R] M₂)) = c.smul_right := rfl

end smul_rightₗ

section comm_ring

/-- The determinant of a continuous linear map, mainly as a convenience device to be able to
write `A.det` instead of `(A : M →ₗ[R] M).det`. -/
@[reducible] noncomputable def det {R : Type*} [comm_ring R]
  {M : Type*} [topological_space M] [add_comm_group M] [module R M] (A : M →L[R] M) : R :=
linear_map.det (A : M →ₗ[R] M)

variables
{R : Type*} [comm_ring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
[module R M] [module R M₂] [module R M₃] [has_continuous_const_smul R M₃]

variables [topological_add_group M₂] [has_continuous_const_smul R M₂]

instance : algebra R (M₂ →L[R] M₂) :=
algebra.of_module smul_comp (λ _ _ _, comp_smul _ _ _)

end comm_ring

section restrict_scalars

variables {A M M₂ : Type*} [ring A] [add_comm_group M] [add_comm_group M₂]
  [module A M] [module A M₂] [topological_space M] [topological_space M₂]
  (R : Type*) [ring R] [module R M] [module R M₂] [linear_map.compatible_smul M M₂ R A]

/-- If `A` is an `R`-algebra, then a continuous `A`-linear map can be interpreted as a continuous
`R`-linear map. We assume `linear_map.compatible_smul M M₂ R A` to match assumptions of
`linear_map.map_smul_of_tower`. -/
def restrict_scalars (f : M →L[A] M₂) : M →L[R] M₂ :=
⟨(f : M →ₗ[A] M₂).restrict_scalars R, f.continuous⟩

variable {R}

@[simp, norm_cast] lemma coe_restrict_scalars (f : M →L[A] M₂) :
  (f.restrict_scalars R : M →ₗ[R] M₂) = (f : M →ₗ[A] M₂).restrict_scalars R := rfl

@[simp] lemma coe_restrict_scalars' (f : M →L[A] M₂) : ⇑(f.restrict_scalars R) = f := rfl

@[simp] lemma restrict_scalars_zero : (0 : M →L[A] M₂).restrict_scalars R = 0 := rfl

section
variable [topological_add_group M₂]

@[simp] lemma restrict_scalars_add (f g : M →L[A] M₂) :
  (f + g).restrict_scalars R = f.restrict_scalars R + g.restrict_scalars R := rfl

@[simp] lemma restrict_scalars_neg (f : M →L[A] M₂) :
  (-f).restrict_scalars R = -f.restrict_scalars R := rfl
end

variables {S : Type*} [ring S] [module S M₂] [has_continuous_const_smul S M₂]
  [smul_comm_class A S M₂] [smul_comm_class R S M₂]

@[simp] lemma restrict_scalars_smul (c : S) (f : M →L[A] M₂) :
  (c • f).restrict_scalars R = c • f.restrict_scalars R := rfl

variables (A M M₂ R S) [topological_add_group M₂]

/-- `continuous_linear_map.restrict_scalars` as a `linear_map`. See also
`continuous_linear_map.restrict_scalarsL`. -/
def restrict_scalarsₗ : (M →L[A] M₂) →ₗ[S] (M →L[R] M₂) :=
{ to_fun := restrict_scalars R,
  map_add' := restrict_scalars_add,
  map_smul' := restrict_scalars_smul }

variables {A M M₂ R S}

@[simp] lemma coe_restrict_scalarsₗ : ⇑(restrict_scalarsₗ A M M₂ R S) = restrict_scalars R := rfl

end restrict_scalars

end continuous_linear_map

namespace continuous_linear_equiv

section add_comm_monoid

variables {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} [semiring R₁] [semiring R₂] [semiring R₃]
{σ₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
{σ₂₃ : R₂ →+* R₃} {σ₃₂ : R₃ →+* R₂} [ring_hom_inv_pair σ₂₃ σ₃₂] [ring_hom_inv_pair σ₃₂ σ₂₃]
{σ₁₃ : R₁ →+* R₃} {σ₃₁ : R₃ →+* R₁} [ring_hom_inv_pair σ₁₃ σ₃₁] [ring_hom_inv_pair σ₃₁ σ₁₃]
[ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₃₂ σ₂₁ σ₃₁]
{M₁ : Type*} [topological_space M₁] [add_comm_monoid M₁]
{M'₁ : Type*} [topological_space M'₁] [add_comm_monoid M'₁]
{M₂ : Type*} [topological_space M₂] [add_comm_monoid M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_monoid M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_monoid M₄]
[module R₁ M₁] [module R₁ M'₁] [module R₂ M₂] [module R₃ M₃]

include σ₂₁
/-- A continuous linear equivalence induces a continuous linear map. -/
def to_continuous_linear_map (e : M₁ ≃SL[σ₁₂] M₂) : M₁ →SL[σ₁₂] M₂ :=
{ cont := e.continuous_to_fun,
  ..e.to_linear_equiv.to_linear_map }

/-- Coerce continuous linear equivs to continuous linear maps. -/
instance : has_coe (M₁ ≃SL[σ₁₂] M₂) (M₁ →SL[σ₁₂] M₂) := ⟨to_continuous_linear_map⟩

instance : continuous_semilinear_equiv_class (M₁ ≃SL[σ₁₂] M₂) σ₁₂ M₁ M₂ :=
{ coe := λ f, f,
  inv := λ f, f.inv_fun,
  coe_injective' := λ f g h₁ h₂, by { cases f with f' _, cases g with g' _,  cases f', cases g',
                                      congr' },
  left_inv := λ f, f.left_inv,
  right_inv := λ f, f.right_inv,
  map_add := λ f, f.map_add',
  map_smulₛₗ := λ f, f.map_smul',
  map_continuous := continuous_to_fun,
  inv_continuous := continuous_inv_fun }

/-- Coerce continuous linear equivs to maps. -/
-- see Note [function coercion]
instance : has_coe_to_fun (M₁ ≃SL[σ₁₂] M₂) (λ _, M₁ → M₂) := ⟨λ f, f⟩

@[simp] theorem coe_def_rev (e : M₁ ≃SL[σ₁₂] M₂) : e.to_continuous_linear_map = e := rfl

theorem coe_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : (e : M₁ →SL[σ₁₂] M₂) b = e b := rfl

@[simp] lemma coe_to_linear_equiv (f : M₁ ≃SL[σ₁₂] M₂) : ⇑f.to_linear_equiv = f := rfl

@[simp, norm_cast] lemma coe_coe (e : M₁ ≃SL[σ₁₂] M₂) : ⇑(e : M₁ →SL[σ₁₂] M₂) = e := rfl

lemma to_linear_equiv_injective :
  function.injective (to_linear_equiv : (M₁ ≃SL[σ₁₂] M₂) → (M₁ ≃ₛₗ[σ₁₂] M₂))
| ⟨e, _, _⟩ ⟨e', _, _⟩ rfl := rfl

@[ext] lemma ext {f g : M₁ ≃SL[σ₁₂] M₂} (h : (f : M₁ → M₂) = g) : f = g :=
to_linear_equiv_injective $ linear_equiv.ext $ congr_fun h

lemma coe_injective : function.injective (coe : (M₁ ≃SL[σ₁₂] M₂) → (M₁ →SL[σ₁₂] M₂)) :=
λ e e' h, ext $ funext $ continuous_linear_map.ext_iff.1 h

@[simp, norm_cast] lemma coe_inj {e e' : M₁ ≃SL[σ₁₂] M₂} : (e : M₁ →SL[σ₁₂] M₂) = e' ↔ e = e' :=
coe_injective.eq_iff

/-- A continuous linear equivalence induces a homeomorphism. -/
def to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : M₁ ≃ₜ M₂ := { to_equiv := e.to_linear_equiv.to_equiv, ..e }

@[simp] lemma coe_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) : ⇑e.to_homeomorph = e := rfl

lemma image_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₁) : e '' closure s = closure (e '' s) :=
e.to_homeomorph.image_closure s

lemma preimage_closure (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₂) : e ⁻¹' closure s = closure (e ⁻¹' s) :=
e.to_homeomorph.preimage_closure s

@[simp] lemma is_closed_image (e : M₁ ≃SL[σ₁₂] M₂) {s : set M₁} :
  is_closed (e '' s) ↔ is_closed s :=
e.to_homeomorph.is_closed_image

lemma map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e (𝓝 x) = 𝓝 (e x) :=
e.to_homeomorph.map_nhds_eq x

-- Make some straightforward lemmas available to `simp`.
@[simp] lemma map_zero (e : M₁ ≃SL[σ₁₂] M₂) : e (0 : M₁) = 0 := (e : M₁ →SL[σ₁₂] M₂).map_zero
@[simp] lemma map_add (e : M₁ ≃SL[σ₁₂] M₂) (x y : M₁) : e (x + y) = e x + e y :=
(e : M₁ →SL[σ₁₂] M₂).map_add x y
@[simp] lemma map_smulₛₗ (e : M₁ ≃SL[σ₁₂] M₂) (c : R₁) (x : M₁) : e (c • x) = σ₁₂ c • (e x) :=
(e : M₁ →SL[σ₁₂] M₂).map_smulₛₗ c x
omit σ₂₁

@[simp] lemma map_smul [module R₁ M₂] (e : M₁ ≃L[R₁] M₂) (c : R₁) (x : M₁) :
  e (c • x) = c • (e x) :=
(e : M₁ →L[R₁] M₂).map_smul c x

include σ₂₁
@[simp] lemma map_eq_zero_iff (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : e x = 0 ↔ x = 0 :=
e.to_linear_equiv.map_eq_zero_iff

attribute [continuity]
  continuous_linear_equiv.continuous_to_fun continuous_linear_equiv.continuous_inv_fun

@[continuity]
protected lemma continuous (e : M₁ ≃SL[σ₁₂] M₂) : continuous (e : M₁ → M₂) :=
e.continuous_to_fun

protected lemma continuous_on (e : M₁ ≃SL[σ₁₂] M₂) {s : set M₁} : continuous_on (e : M₁ → M₂) s :=
e.continuous.continuous_on

protected lemma continuous_at (e : M₁ ≃SL[σ₁₂] M₂) {x : M₁} : continuous_at (e : M₁ → M₂) x :=
e.continuous.continuous_at

protected lemma continuous_within_at (e : M₁ ≃SL[σ₁₂] M₂) {s : set M₁} {x : M₁} :
  continuous_within_at (e : M₁ → M₂) s x :=
e.continuous.continuous_within_at

lemma comp_continuous_on_iff
  {α : Type*} [topological_space α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} {s : set α} :
  continuous_on (e ∘ f) s ↔ continuous_on f s :=
e.to_homeomorph.comp_continuous_on_iff _ _

lemma comp_continuous_iff
  {α : Type*} [topological_space α] (e : M₁ ≃SL[σ₁₂] M₂) {f : α → M₁} :
  continuous (e ∘ f) ↔ continuous f :=
e.to_homeomorph.comp_continuous_iff
omit σ₂₁

/-- An extensionality lemma for `R ≃L[R] M`. -/
lemma ext₁ [topological_space R₁] {f g : R₁ ≃L[R₁] M₁} (h : f 1 = g 1) : f = g :=
ext $ funext $ λ x, mul_one x ▸ by rw [← smul_eq_mul, map_smul, h, map_smul]

section
variables (R₁ M₁)

/-- The identity map as a continuous linear equivalence. -/
@[refl] protected def refl : M₁ ≃L[R₁] M₁ :=
{ continuous_to_fun := continuous_id,
  continuous_inv_fun := continuous_id,
  .. linear_equiv.refl R₁ M₁ }
end

@[simp, norm_cast] lemma coe_refl :
  ↑(continuous_linear_equiv.refl R₁ M₁) = continuous_linear_map.id R₁ M₁ := rfl

@[simp, norm_cast] lemma coe_refl' : ⇑(continuous_linear_equiv.refl R₁ M₁) = id := rfl

/-- The inverse of a continuous linear equivalence as a continuous linear equivalence-/
@[symm] protected def symm (e : M₁ ≃SL[σ₁₂] M₂) : M₂ ≃SL[σ₂₁] M₁ :=
{ continuous_to_fun := e.continuous_inv_fun,
  continuous_inv_fun := e.continuous_to_fun,
  .. e.to_linear_equiv.symm }

include σ₂₁
@[simp] lemma symm_to_linear_equiv (e : M₁ ≃SL[σ₁₂] M₂) :
  e.symm.to_linear_equiv = e.to_linear_equiv.symm :=
by { ext, refl }

@[simp] lemma symm_to_homeomorph (e : M₁ ≃SL[σ₁₂] M₂) :
  e.to_homeomorph.symm = e.symm.to_homeomorph :=
rfl

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : M₁ ≃SL[σ₁₂] M₂) : M₁ → M₂ := h

/-- See Note [custom simps projection] -/
def simps.symm_apply (h : M₁ ≃SL[σ₁₂] M₂) : M₂ → M₁ := h.symm

initialize_simps_projections continuous_linear_equiv
  (to_linear_equiv_to_fun → apply, to_linear_equiv_inv_fun → symm_apply)

lemma symm_map_nhds_eq (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : map e.symm (𝓝 (e x)) = 𝓝 x :=
e.to_homeomorph.symm_map_nhds_eq x
omit σ₂₁

include σ₂₁ σ₃₂ σ₃₁
/-- The composition of two continuous linear equivalences as a continuous linear equivalence. -/
@[trans] protected def trans (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) : M₁ ≃SL[σ₁₃] M₃ :=
{ continuous_to_fun := e₂.continuous_to_fun.comp e₁.continuous_to_fun,
  continuous_inv_fun := e₁.continuous_inv_fun.comp e₂.continuous_inv_fun,
  .. e₁.to_linear_equiv.trans e₂.to_linear_equiv }

include σ₁₃
@[simp] lemma trans_to_linear_equiv (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) :
  (e₁.trans e₂).to_linear_equiv = e₁.to_linear_equiv.trans e₂.to_linear_equiv :=
by { ext, refl }
omit σ₁₃ σ₂₁ σ₃₂ σ₃₁

/-- Product of two continuous linear equivalences. The map comes from `equiv.prod_congr`. -/
def prod [module R₁ M₂] [module R₁ M₃] [module R₁ M₄] (e : M₁ ≃L[R₁] M₂) (e' : M₃ ≃L[R₁] M₄) :
  (M₁ × M₃) ≃L[R₁] (M₂ × M₄) :=
{ continuous_to_fun := e.continuous_to_fun.prod_map e'.continuous_to_fun,
  continuous_inv_fun := e.continuous_inv_fun.prod_map e'.continuous_inv_fun,
  .. e.to_linear_equiv.prod e'.to_linear_equiv }

@[simp, norm_cast] lemma prod_apply [module R₁ M₂] [module R₁ M₃] [module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  (e' : M₃ ≃L[R₁] M₄) (x) :
  e.prod e' x = (e x.1, e' x.2) := rfl

@[simp, norm_cast] lemma coe_prod [module R₁ M₂] [module R₁ M₃] [module R₁ M₄] (e : M₁ ≃L[R₁] M₂)
  (e' : M₃ ≃L[R₁] M₄) :
  (e.prod e' : (M₁ × M₃) →L[R₁] (M₂ × M₄)) = (e : M₁ →L[R₁] M₂).prod_map (e' : M₃ →L[R₁] M₄) :=
rfl

include σ₂₁
theorem bijective (e : M₁ ≃SL[σ₁₂] M₂) : function.bijective e :=
e.to_linear_equiv.to_equiv.bijective
theorem injective (e : M₁ ≃SL[σ₁₂] M₂) : function.injective e :=
e.to_linear_equiv.to_equiv.injective
theorem surjective (e : M₁ ≃SL[σ₁₂] M₂) : function.surjective e :=
e.to_linear_equiv.to_equiv.surjective

include σ₃₂ σ₃₁ σ₁₃
@[simp] theorem trans_apply (e₁ : M₁ ≃SL[σ₁₂] M₂) (e₂ : M₂ ≃SL[σ₂₃] M₃) (c : M₁) :
  (e₁.trans e₂) c = e₂ (e₁ c) :=
rfl
omit σ₃₂ σ₃₁ σ₁₃

@[simp] theorem apply_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (c : M₂) : e (e.symm c) = c :=
e.1.right_inv c
@[simp] theorem symm_apply_apply (e : M₁ ≃SL[σ₁₂] M₂) (b : M₁) : e.symm (e b) = b := e.1.left_inv b

include σ₁₂ σ₂₃ σ₁₃ σ₃₁
@[simp] theorem symm_trans_apply (e₁ : M₂ ≃SL[σ₂₁] M₁) (e₂ : M₃ ≃SL[σ₃₂] M₂) (c : M₁) :
  (e₂.trans e₁).symm c = e₂.symm (e₁.symm c) :=
rfl
omit σ₁₂ σ₂₃ σ₁₃ σ₃₁

@[simp] theorem symm_image_image (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₁) : e.symm '' (e '' s) = s :=
e.to_linear_equiv.to_equiv.symm_image_image s
@[simp] theorem image_symm_image (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₂) : e '' (e.symm '' s) = s :=
e.symm.symm_image_image s

include σ₃₂ σ₃₁
@[simp, norm_cast]
lemma comp_coe (f : M₁ ≃SL[σ₁₂] M₂) (f' : M₂ ≃SL[σ₂₃] M₃) :
  (f' : M₂ →SL[σ₂₃] M₃).comp (f : M₁ →SL[σ₁₂] M₂) = (f.trans f' : M₁ →SL[σ₁₃] M₃) :=
rfl
omit σ₃₂ σ₃₁ σ₂₁

@[simp] theorem coe_comp_coe_symm (e : M₁ ≃SL[σ₁₂] M₂) :
  (e : M₁ →SL[σ₁₂] M₂).comp (e.symm : M₂ →SL[σ₂₁] M₁) = continuous_linear_map.id R₂ M₂ :=
continuous_linear_map.ext e.apply_symm_apply

@[simp] theorem coe_symm_comp_coe (e : M₁ ≃SL[σ₁₂] M₂) :
  (e.symm : M₂ →SL[σ₂₁] M₁).comp (e : M₁ →SL[σ₁₂] M₂) = continuous_linear_map.id R₁ M₁ :=
continuous_linear_map.ext e.symm_apply_apply

include σ₂₁
@[simp] lemma symm_comp_self (e : M₁ ≃SL[σ₁₂] M₂) :
  (e.symm : M₂ → M₁) ∘ (e : M₁ → M₂) = id :=
by{ ext x, exact symm_apply_apply e x }

@[simp] lemma self_comp_symm (e : M₁ ≃SL[σ₁₂] M₂) :
  (e : M₁ → M₂) ∘ (e.symm : M₂ → M₁) = id :=
by{ ext x, exact apply_symm_apply e x }

@[simp] theorem symm_symm (e : M₁ ≃SL[σ₁₂] M₂) : e.symm.symm = e :=
by { ext x, refl }
omit σ₂₁

@[simp] lemma refl_symm :
 (continuous_linear_equiv.refl R₁ M₁).symm = continuous_linear_equiv.refl R₁ M₁ :=
rfl

include σ₂₁
theorem symm_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) (x : M₁) : e.symm.symm x = e x :=
rfl

lemma symm_apply_eq (e : M₁ ≃SL[σ₁₂] M₂) {x y} : e.symm x = y ↔ x = e y :=
e.to_linear_equiv.symm_apply_eq

lemma eq_symm_apply (e : M₁ ≃SL[σ₁₂] M₂) {x y} : y = e.symm x ↔ e y = x :=
e.to_linear_equiv.eq_symm_apply

protected lemma image_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₁) : e '' s = e.symm ⁻¹' s :=
e.to_linear_equiv.to_equiv.image_eq_preimage s

protected lemma image_symm_eq_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₂) : e.symm '' s = e ⁻¹' s :=
by rw [e.symm.image_eq_preimage, e.symm_symm]

@[simp] protected lemma symm_preimage_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₂) :
  e.symm ⁻¹' (e ⁻¹' s) = s := e.to_linear_equiv.to_equiv.symm_preimage_preimage s

@[simp] protected lemma preimage_symm_preimage (e : M₁ ≃SL[σ₁₂] M₂) (s : set M₁) :
  e ⁻¹' (e.symm ⁻¹' s) = s := e.symm.symm_preimage_preimage s

protected lemma uniform_embedding {E₁ E₂ : Type*} [uniform_space E₁] [uniform_space E₂]
  [add_comm_group E₁] [add_comm_group E₂] [module R₁ E₁] [module R₂ E₂]
  [uniform_add_group E₁] [uniform_add_group E₂]
  (e : E₁ ≃SL[σ₁₂] E₂) :
  uniform_embedding e :=
e.to_linear_equiv.to_equiv.uniform_embedding
  e.to_continuous_linear_map.uniform_continuous
  e.symm.to_continuous_linear_map.uniform_continuous

protected lemma _root_.linear_equiv.uniform_embedding {E₁ E₂ : Type*} [uniform_space E₁]
  [uniform_space E₂] [add_comm_group E₁] [add_comm_group E₂] [module R₁ E₁] [module R₂ E₂]
  [uniform_add_group E₁] [uniform_add_group E₂]
  (e : E₁ ≃ₛₗ[σ₁₂] E₂) (h₁ : continuous e) (h₂ : continuous e.symm) :
  uniform_embedding e :=
continuous_linear_equiv.uniform_embedding
({ continuous_to_fun := h₁,
  continuous_inv_fun := h₂,
  .. e } : E₁ ≃SL[σ₁₂] E₂)

omit σ₂₁

/-- Create a `continuous_linear_equiv` from two `continuous_linear_map`s that are
inverse of each other. -/
def equiv_of_inverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ : M₂ →SL[σ₂₁] M₁) (h₁ : function.left_inverse f₂ f₁)
  (h₂ : function.right_inverse f₂ f₁) :
  M₁ ≃SL[σ₁₂] M₂ :=
{ to_fun := f₁,
  continuous_to_fun := f₁.continuous,
  inv_fun := f₂,
  continuous_inv_fun := f₂.continuous,
  left_inv := h₁,
  right_inv := h₂,
  .. f₁ }

include σ₂₁
@[simp] lemma equiv_of_inverse_apply (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂ x) :
  equiv_of_inverse f₁ f₂ h₁ h₂ x = f₁ x :=
rfl

@[simp] lemma symm_equiv_of_inverse (f₁ : M₁ →SL[σ₁₂] M₂) (f₂ h₁ h₂) :
  (equiv_of_inverse f₁ f₂ h₁ h₂).symm = equiv_of_inverse f₂ f₁ h₂ h₁ :=
rfl
omit σ₂₁

variable (M₁)

/-- The continuous linear equivalences from `M` to itself form a group under composition. -/
instance automorphism_group : group (M₁ ≃L[R₁] M₁) :=
{ mul          := λ f g, g.trans f,
  one          := continuous_linear_equiv.refl R₁ M₁,
  inv          := λ f, f.symm,
  mul_assoc    := λ f g h, by {ext, refl},
  mul_one      := λ f, by {ext, refl},
  one_mul      := λ f, by {ext, refl},
  mul_left_inv := λ f, by {ext, exact f.left_inv x} }

variables {M₁} {R₄ : Type*} [semiring R₄] [module R₄ M₄]
  {σ₃₄ : R₃ →+* R₄} {σ₄₃ : R₄ →+* R₃} [ring_hom_inv_pair σ₃₄ σ₄₃] [ring_hom_inv_pair σ₄₃ σ₃₄]
  {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R₁ →+* R₄}
  [ring_hom_comp_triple σ₂₁ σ₁₄ σ₂₄] [ring_hom_comp_triple σ₂₄ σ₄₃ σ₂₃]
  [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄]

include σ₂₁ σ₃₄ σ₂₃ σ₂₄ σ₁₃

/-- A pair of continuous (semi)linear equivalences generates an equivalence between the spaces of
continuous linear maps. See also `continuous_linear_equiv.arrow_congr`. -/
@[simps] def arrow_congr_equiv (e₁₂ : M₁ ≃SL[σ₁₂] M₂) (e₄₃ : M₄ ≃SL[σ₄₃] M₃) :
  (M₁ →SL[σ₁₄] M₄) ≃ (M₂ →SL[σ₂₃] M₃) :=
{ to_fun := λ f, (e₄₃ : M₄ →SL[σ₄₃] M₃).comp (f.comp (e₁₂.symm : M₂ →SL[σ₂₁] M₁)),
  inv_fun := λ f, (e₄₃.symm : M₃ →SL[σ₃₄] M₄).comp (f.comp (e₁₂ : M₁ →SL[σ₁₂] M₂)),
  left_inv := λ f, continuous_linear_map.ext $ λ x,
    by simp only [continuous_linear_map.comp_apply, symm_apply_apply, coe_coe],
  right_inv := λ f, continuous_linear_map.ext $ λ x,
    by simp only [continuous_linear_map.comp_apply, apply_symm_apply, coe_coe] }

end add_comm_monoid

section add_comm_group

variables {R : Type*} [semiring R]
{M : Type*} [topological_space M] [add_comm_group M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂]
{M₃ : Type*} [topological_space M₃] [add_comm_group M₃]
{M₄ : Type*} [topological_space M₄] [add_comm_group M₄]
[module R M] [module R M₂] [module R M₃] [module R M₄]

variables [topological_add_group M₄]

/-- Equivalence given by a block lower diagonal matrix. `e` and `e'` are diagonal square blocks,
  and `f` is a rectangular block below the diagonal. -/
def skew_prod (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) :
  (M × M₃) ≃L[R] M₂ × M₄ :=
{ continuous_to_fun := (e.continuous_to_fun.comp continuous_fst).prod_mk
    ((e'.continuous_to_fun.comp continuous_snd).add $ f.continuous.comp continuous_fst),
  continuous_inv_fun := (e.continuous_inv_fun.comp continuous_fst).prod_mk
    (e'.continuous_inv_fun.comp $ continuous_snd.sub $ f.continuous.comp $
      e.continuous_inv_fun.comp continuous_fst),
.. e.to_linear_equiv.skew_prod e'.to_linear_equiv ↑f }
@[simp] lemma skew_prod_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
  e.skew_prod e' f x = (e x.1, e' x.2 + f x.1) := rfl

@[simp] lemma skew_prod_symm_apply (e : M ≃L[R] M₂) (e' : M₃ ≃L[R] M₄) (f : M →L[R] M₄) (x) :
  (e.skew_prod e' f).symm x = (e.symm x.1, e'.symm (x.2 - f (e.symm x.1))) := rfl

end add_comm_group

section ring

variables {R : Type*} [ring R] {R₂ : Type*} [ring R₂]
{M : Type*} [topological_space M] [add_comm_group M] [module R M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [module R₂ M₂]
variables {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]

include σ₂₁
@[simp] lemma map_sub (e : M ≃SL[σ₁₂] M₂) (x y : M) : e (x - y) = e x - e y :=
(e : M →SL[σ₁₂] M₂).map_sub x y

@[simp] lemma map_neg (e : M ≃SL[σ₁₂] M₂) (x : M) : e (-x) = -e x := (e : M →SL[σ₁₂] M₂).map_neg x
omit σ₂₁

section
/-! The next theorems cover the identification between `M ≃L[𝕜] M`and the group of units of the ring
`M →L[R] M`. -/
variables [topological_add_group M]

/-- An invertible continuous linear map `f` determines a continuous equivalence from `M` to itself.
-/
def of_unit (f : (M →L[R] M)ˣ) : (M ≃L[R] M) :=
{ to_linear_equiv :=
  { to_fun    := f.val,
    map_add'  := by simp,
    map_smul' := by simp,
    inv_fun   := f.inv,
    left_inv  := λ x, show (f.inv * f.val) x = x, by {rw f.inv_val, simp},
    right_inv := λ x, show (f.val * f.inv) x = x, by {rw f.val_inv, simp}, },
  continuous_to_fun  := f.val.continuous,
  continuous_inv_fun := f.inv.continuous }

/-- A continuous equivalence from `M` to itself determines an invertible continuous linear map. -/
def to_unit (f : (M ≃L[R] M)) : (M →L[R] M)ˣ :=
{ val     := f,
  inv     := f.symm,
  val_inv := by {ext, simp},
  inv_val := by {ext, simp} }

variables (R M)

/-- The units of the algebra of continuous `R`-linear endomorphisms of `M` is multiplicatively
equivalent to the type of continuous linear equivalences between `M` and itself. -/
def units_equiv : (M →L[R] M)ˣ ≃* (M ≃L[R] M) :=
{ to_fun    := of_unit,
  inv_fun   := to_unit,
  left_inv  := λ f, by {ext, refl},
  right_inv := λ f, by {ext, refl},
  map_mul'  := λ x y, by {ext, refl} }

@[simp] lemma units_equiv_apply (f : (M →L[R] M)ˣ) (x : M) :
  units_equiv R M f x = f x := rfl

end

section
variables (R) [topological_space R] [has_continuous_mul R]

/-- Continuous linear equivalences `R ≃L[R] R` are enumerated by `Rˣ`. -/
def units_equiv_aut : Rˣ ≃ (R ≃L[R] R) :=
{ to_fun := λ u, equiv_of_inverse
    (continuous_linear_map.smul_right (1 : R →L[R] R) ↑u)
    (continuous_linear_map.smul_right (1 : R →L[R] R) ↑u⁻¹)
    (λ x, by simp) (λ x, by simp),
  inv_fun := λ e, ⟨e 1, e.symm 1,
    by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, symm_apply_apply],
    by rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, apply_symm_apply]⟩,
  left_inv := λ u, units.ext $ by simp,
  right_inv := λ e, ext₁ $ by simp }

variable {R}

@[simp] lemma units_equiv_aut_apply (u : Rˣ) (x : R) : units_equiv_aut R u x = x * u := rfl

@[simp] lemma units_equiv_aut_apply_symm (u : Rˣ) (x : R) :
  (units_equiv_aut R u).symm x = x * ↑u⁻¹ := rfl

@[simp] lemma units_equiv_aut_symm_apply (e : R ≃L[R] R) :
  ↑((units_equiv_aut R).symm e) = e 1 :=
rfl

end

variables [module R M₂] [topological_add_group M]

open _root_.continuous_linear_map (id fst snd mem_ker)

/-- A pair of continuous linear maps such that `f₁ ∘ f₂ = id` generates a continuous
linear equivalence `e` between `M` and `M₂ × f₁.ker` such that `(e x).2 = x` for `x ∈ f₁.ker`,
`(e x).1 = f₁ x`, and `(e (f₂ y)).2 = 0`. The map is given by `e x = (f₁ x, x - f₂ (f₁ x))`. -/
def equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M) (h : function.right_inverse f₂ f₁) :
  M ≃L[R] M₂ × f₁.ker :=
equiv_of_inverse (f₁.prod (f₁.proj_ker_of_right_inverse f₂ h)) (f₂.coprod f₁.ker.subtypeL)
  (λ x, by simp)
  (λ ⟨x, y⟩, by simp [h x])

@[simp] lemma fst_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (x : M) :
  (equiv_of_right_inverse f₁ f₂ h x).1 = f₁ x := rfl

@[simp] lemma snd_equiv_of_right_inverse (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (x : M) :
  ((equiv_of_right_inverse f₁ f₂ h x).2 : M) = x - f₂ (f₁ x) := rfl

@[simp] lemma equiv_of_right_inverse_symm_apply (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) (y : M₂ × f₁.ker) :
  (equiv_of_right_inverse f₁ f₂ h).symm y = f₂ y.1 + y.2 := rfl

end ring

section

variables (ι R M : Type*) [unique ι] [semiring R] [add_comm_monoid M] [module R M]
  [topological_space M]

/-- If `ι` has a unique element, then `ι → M` is continuously linear equivalent to `M`. -/
def fun_unique : (ι → M) ≃L[R] M :=
{ to_linear_equiv := linear_equiv.fun_unique ι R M,
  .. homeomorph.fun_unique ι M }

variables {ι R M}

@[simp] lemma coe_fun_unique : ⇑(fun_unique ι R M) = function.eval default := rfl
@[simp] lemma coe_fun_unique_symm : ⇑(fun_unique ι R M).symm = function.const ι := rfl

variables (R M)

/-- Continuous linear equivalence between dependent functions `Π i : fin 2, M i` and `M 0 × M 1`. -/
@[simps { fully_applied := ff }]
def pi_fin_two (M : fin 2 → Type*) [Π i, add_comm_monoid (M i)] [Π i, module R (M i)]
  [Π i, topological_space (M i)] :
  (Π i, M i) ≃L[R] M 0 × M 1 :=
{ to_linear_equiv := linear_equiv.pi_fin_two R M, .. homeomorph.pi_fin_two M }

/-- Continuous linear equivalence between vectors in `M² = fin 2 → M` and `M × M`. -/
@[simps { fully_applied := ff }]
def fin_two_arrow : (fin 2 → M) ≃L[R] M × M :=
{ to_linear_equiv := linear_equiv.fin_two_arrow R M, .. pi_fin_two R (λ _, M) }

end

@[simp] lemma det_coe_symm {R : Type*} [field R]
  {M : Type*} [topological_space M] [add_comm_group M] [module R M] (A : M ≃L[R] M) :
  (A.symm : M →L[R] M).det = (A : M →L[R] M).det ⁻¹ :=
linear_equiv.det_coe_symm A.to_linear_equiv

end continuous_linear_equiv

namespace continuous_linear_map

open_locale classical

variables {R : Type*} {M : Type*} {M₂ : Type*} [topological_space M] [topological_space M₂]

section
variables [semiring R]
variables [add_comm_monoid M₂] [module R M₂]
variables [add_comm_monoid M] [module R M]

/-- Introduce a function `inverse` from `M →L[R] M₂` to `M₂ →L[R] M`, which sends `f` to `f.symm` if
`f` is a continuous linear equivalence and to `0` otherwise.  This definition is somewhat ad hoc,
but one needs a fully (rather than partially) defined inverse function for some purposes, including
for calculus. -/
noncomputable def inverse : (M →L[R] M₂) → (M₂ →L[R] M) :=
λ f, if h : ∃ (e : M ≃L[R] M₂), (e : M →L[R] M₂) = f then ((classical.some h).symm : M₂ →L[R] M)
else 0

/-- By definition, if `f` is invertible then `inverse f = f.symm`. -/
@[simp] lemma inverse_equiv (e : M ≃L[R] M₂) : inverse (e : M →L[R] M₂) = e.symm :=
begin
  have h : ∃ (e' : M ≃L[R] M₂), (e' : M →L[R] M₂) = ↑e := ⟨e, rfl⟩,
  simp only [inverse, dif_pos h],
  congr,
  exact_mod_cast (classical.some_spec h)
end

/-- By definition, if `f` is not invertible then `inverse f = 0`. -/
@[simp] lemma inverse_non_equiv (f : M →L[R] M₂) (h : ¬∃ (e' : M ≃L[R] M₂), ↑e' = f) :
  inverse f = 0 :=
dif_neg h

end

section
variables [ring R]
variables [add_comm_group M] [topological_add_group M] [module R M]
variables [add_comm_group M₂] [module R M₂]

@[simp] lemma ring_inverse_equiv (e : M ≃L[R] M) :
  ring.inverse ↑e = inverse (e : M →L[R] M) :=
begin
  suffices :
    ring.inverse ((((continuous_linear_equiv.units_equiv _ _).symm e) : M →L[R] M)) = inverse ↑e,
  { convert this },
  simp,
  refl,
end

/-- The function `continuous_linear_equiv.inverse` can be written in terms of `ring.inverse` for the
ring of self-maps of the domain. -/
lemma to_ring_inverse (e : M ≃L[R] M₂) (f : M →L[R] M₂) :
  inverse f = (ring.inverse ((e.symm : (M₂ →L[R] M)).comp f)) ∘L ↑e.symm :=
begin
  by_cases h₁ : ∃ (e' : M ≃L[R] M₂), ↑e' = f,
  { obtain ⟨e', he'⟩ := h₁,
    rw ← he',
    change _ = (ring.inverse ↑(e'.trans e.symm)) ∘L ↑e.symm,
    ext,
    simp },
  { suffices : ¬is_unit ((e.symm : M₂ →L[R] M).comp f),
    { simp [this, h₁] },
    contrapose! h₁,
    rcases h₁ with ⟨F, hF⟩,
    use (continuous_linear_equiv.units_equiv _ _ F).trans e,
    ext,
    dsimp, rw [coe_fn_coe_base' F, hF], simp }
end

lemma ring_inverse_eq_map_inverse : ring.inverse = @inverse R M M _ _ _ _ _ _ _ :=
begin
  ext,
  simp [to_ring_inverse (continuous_linear_equiv.refl R M)],
end

end

end continuous_linear_map

namespace submodule

variables
{R : Type*} [ring R]
{M : Type*} [topological_space M] [add_comm_group M] [module R M]
{M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [module R M₂]

open continuous_linear_map

/-- A submodule `p` is called *complemented* if there exists a continuous projection `M →ₗ[R] p`. -/
def closed_complemented (p : submodule R M) : Prop := ∃ f : M →L[R] p, ∀ x : p, f x = x

lemma closed_complemented.has_closed_complement {p : submodule R M} [t1_space p]
  (h : closed_complemented p) :
  ∃ (q : submodule R M) (hq : is_closed (q : set M)), is_compl p q :=
exists.elim h $ λ f hf, ⟨f.ker, f.is_closed_ker, linear_map.is_compl_of_proj hf⟩

protected lemma closed_complemented.is_closed [topological_add_group M] [t1_space M]
  {p : submodule R M} (h : closed_complemented p) :
  is_closed (p : set M) :=
begin
  rcases h with ⟨f, hf⟩,
  have : ker (id R M - p.subtypeL.comp f) = p := linear_map.ker_id_sub_eq_of_proj hf,
  exact this ▸ (is_closed_ker _)
end

@[simp] lemma closed_complemented_bot : closed_complemented (⊥ : submodule R M) :=
⟨0, λ x, by simp only [zero_apply, eq_zero_of_bot_submodule x]⟩

@[simp] lemma closed_complemented_top : closed_complemented (⊤ : submodule R M) :=
⟨(id R M).cod_restrict ⊤ (λ x, trivial), λ x, subtype.ext_iff_val.2 $ by simp⟩

end submodule

lemma continuous_linear_map.closed_complemented_ker_of_right_inverse {R : Type*} [ring R]
  {M : Type*} [topological_space M] [add_comm_group M]
  {M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [module R M] [module R M₂]
  [topological_add_group M] (f₁ : M →L[R] M₂) (f₂ : M₂ →L[R] M)
  (h : function.right_inverse f₂ f₁) :
  f₁.ker.closed_complemented :=
⟨f₁.proj_ker_of_right_inverse f₂ h, f₁.proj_ker_of_right_inverse_apply_idem f₂ h⟩

section quotient

namespace submodule

variables {R M : Type*} [ring R] [add_comm_group M] [module R M] [topological_space M]
  (S : submodule R M)

lemma is_open_map_mkq [topological_add_group M] : is_open_map S.mkq :=
quotient_add_group.is_open_map_coe S.to_add_subgroup

instance topological_add_group_quotient [topological_add_group M] :
  topological_add_group (M ⧸ S) :=
topological_add_group_quotient S.to_add_subgroup

instance has_continuous_smul_quotient [topological_space R] [topological_add_group M]
  [has_continuous_smul R M] :
  has_continuous_smul R (M ⧸ S) :=
begin
  split,
  have quot : quotient_map (λ au : R × M, (au.1, S.mkq au.2)),
    from is_open_map.to_quotient_map
      (is_open_map.id.prod S.is_open_map_mkq)
      (continuous_id.prod_map continuous_quot_mk)
      (function.surjective_id.prod_map $ surjective_quot_mk _),
  rw quot.continuous_iff,
  exact continuous_quot_mk.comp continuous_smul
end

instance t3_quotient_of_is_closed [topological_add_group M] [is_closed (S : set M)] :
  t3_space (M ⧸ S) :=
begin
  letI : is_closed (S.to_add_subgroup : set M) := ‹_›,
  exact S.to_add_subgroup.t3_quotient_of_is_closed
end

end submodule

end quotient
