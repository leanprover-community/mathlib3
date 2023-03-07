/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import algebra.big_operators.finprod
import order.filter.pointwise
import topology.algebra.mul_action
import algebra.big_operators.pi
import topology.continuous_function.basic

/-!
# Theory of topological monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

universes u v
open classical set filter topological_space
open_locale classical topology big_operators pointwise

variables {ι α X M N : Type*} [topological_space X]

@[to_additive]
lemma continuous_one [topological_space M] [has_one M] : continuous (1 : X → M) :=
@continuous_const _ _ _ _ 1

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `M`, for example, is obtained by requiring both the
instances `add_monoid M` and `has_continuous_add M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_vadd α α`/`has_continuous_const_vadd αᵐᵒᵖ α`. -/
class has_continuous_add (M : Type u) [topological_space M] [has_add M] : Prop :=
(continuous_add : continuous (λ p : M × M, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `M`, for example, is obtained by requiring both the instances `monoid M`
and `has_continuous_mul M`.

Continuity in only the left/right argument can be stated using
`has_continuous_const_smul α α`/`has_continuous_const_smul αᵐᵒᵖ α`. -/
@[to_additive]
class has_continuous_mul (M : Type u) [topological_space M] [has_mul M] : Prop :=
(continuous_mul : continuous (λ p : M × M, p.1 * p.2))

section has_continuous_mul

variables [topological_space M] [has_mul M] [has_continuous_mul M]

@[to_additive] instance : has_continuous_mul Mᵒᵈ := ‹has_continuous_mul M›

@[to_additive]
lemma continuous_mul : continuous (λp:M×M, p.1 * p.2) :=
has_continuous_mul.continuous_mul

@[to_additive]
instance has_continuous_mul.to_has_continuous_smul : has_continuous_smul M M := ⟨continuous_mul⟩

@[to_additive]
instance has_continuous_mul.to_has_continuous_smul_op : has_continuous_smul Mᵐᵒᵖ M :=
⟨show continuous ((λ p : M × M, p.1 * p.2) ∘ prod.swap ∘ prod.map mul_opposite.unop id), from
  continuous_mul.comp $ continuous_swap.comp $ continuous.prod_map mul_opposite.continuous_unop
    continuous_id⟩

@[continuity, to_additive]
lemma continuous.mul {f g : X → M} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg : _)

@[to_additive]
lemma continuous_mul_left (a : M) : continuous (λ b:M, a * b) :=
continuous_const.mul continuous_id

@[to_additive]
lemma continuous_mul_right (a : M) : continuous (λ b:M, b * a) :=
continuous_id.mul continuous_const

@[to_additive]
lemma continuous_on.mul {f g : X → M} {s : set X} (hf : continuous_on f s)
  (hg : continuous_on g s) :
  continuous_on (λx, f x * g x) s :=
(continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[to_additive]
lemma tendsto_mul {a b : M} : tendsto (λp:M×M, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp has_continuous_mul.continuous_mul (a, b)

@[to_additive]
lemma filter.tendsto.mul {f g : α → M} {x : filter α} {a b : M}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x * g x) x (𝓝 (a * b)) :=
tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma filter.tendsto.const_mul (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), b * f k) l (𝓝 (b * c)) :=
tendsto_const_nhds.mul h

@[to_additive]
lemma filter.tendsto.mul_const (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), f k * b) l (𝓝 (c * b)) :=
h.mul tendsto_const_nhds

@[to_additive] lemma le_nhds_mul (a b : M) : 𝓝 a * 𝓝 b ≤ 𝓝 (a * b) :=
by { rw [← map₂_mul, ← map_uncurry_prod, ← nhds_prod_eq], exact continuous_mul.tendsto _ }

@[simp, to_additive] lemma nhds_one_mul_nhds {M} [mul_one_class M] [topological_space M]
  [has_continuous_mul M] (a : M) : 𝓝 (1 : M) * 𝓝 a = 𝓝 a :=
((le_nhds_mul _ _).trans_eq $ congr_arg _ (one_mul a)).antisymm $
  le_mul_of_one_le_left' $ pure_le_nhds 1

@[simp, to_additive] lemma nhds_mul_nhds_one {M} [mul_one_class M] [topological_space M]
  [has_continuous_mul M] (a : M) : 𝓝 a * 𝓝 1 = 𝓝 a :=
((le_nhds_mul _ _).trans_eq $ congr_arg _ (mul_one a)).antisymm $
  le_mul_of_one_le_right' $ pure_le_nhds 1

section tendsto_nhds

variables {𝕜 : Type*}
  [preorder 𝕜] [has_zero 𝕜] [has_mul 𝕜] [topological_space 𝕜] [has_continuous_mul 𝕜]
  {l : filter α} {f : α → 𝕜} {b c : 𝕜} (hb : 0 < b)

lemma filter.tendsto_nhds_within_Ioi.const_mul [pos_mul_strict_mono 𝕜] [pos_mul_reflect_lt 𝕜]
  (h : tendsto f l (𝓝[>] c)) :
  tendsto (λ a, b * f a) l (𝓝[>] (b * c)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  ((tendsto_nhds_of_tendsto_nhds_within h).const_mul b) $
  (tendsto_nhds_within_iff.mp h).2.mono (λ j, (mul_lt_mul_left hb).mpr)

lemma filter.tendsto_nhds_within_Iio.const_mul [pos_mul_strict_mono 𝕜] [pos_mul_reflect_lt 𝕜]
  (h : tendsto f l (𝓝[<] c)) :
  tendsto (λ a, b * f a) l (𝓝[<] (b * c)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  ((tendsto_nhds_of_tendsto_nhds_within h).const_mul b) $
  (tendsto_nhds_within_iff.mp h).2.mono (λ j, (mul_lt_mul_left hb).mpr)

lemma filter.tendsto_nhds_within_Ioi.mul_const [mul_pos_strict_mono 𝕜] [mul_pos_reflect_lt 𝕜]
  (h : tendsto f l (𝓝[>] c)) :
  tendsto (λ a, f a * b) l (𝓝[>] (c * b)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  ((tendsto_nhds_of_tendsto_nhds_within h).mul_const b) $
  (tendsto_nhds_within_iff.mp h).2.mono (λ j, (mul_lt_mul_right hb).mpr)

lemma filter.tendsto_nhds_within_Iio.mul_const [mul_pos_strict_mono 𝕜] [mul_pos_reflect_lt 𝕜]
  (h : tendsto f l (𝓝[<] c)) :
  tendsto (λ a, f a * b) l (𝓝[<] (c * b)) :=
tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
  ((tendsto_nhds_of_tendsto_nhds_within h).mul_const b) $
  (tendsto_nhds_within_iff.mp h).2.mono (λ j, (mul_lt_mul_right hb).mpr)

end tendsto_nhds

/-- Construct a unit from limits of units and their inverses. -/
@[to_additive filter.tendsto.add_units "Construct an additive unit from limits of additive units
and their negatives.", simps]
def filter.tendsto.units [topological_space N] [monoid N] [has_continuous_mul N] [t2_space N]
  {f : ι → Nˣ} {r₁ r₂ : N} {l : filter ι} [l.ne_bot]
  (h₁ : tendsto (λ x, ↑(f x)) l (𝓝 r₁)) (h₂ : tendsto (λ x, ↑(f x)⁻¹) l (𝓝 r₂)) : Nˣ :=
{ val := r₁,
  inv := r₂,
  val_inv := by { symmetry, simpa using h₁.mul h₂ },
  inv_val := by { symmetry, simpa using h₂.mul h₁ } }

@[to_additive]
lemma continuous_at.mul {f g : X → M} {x : X} (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x * g x) x :=
hf.mul hg

@[to_additive]
lemma continuous_within_at.mul {f g : X → M} {s : set X} {x : X} (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x * g x) s x :=
hf.mul hg

@[to_additive]
instance [topological_space N] [has_mul N] [has_continuous_mul N] : has_continuous_mul (M × N) :=
⟨(continuous_fst.fst'.mul continuous_fst.snd').prod_mk
  (continuous_snd.fst'.mul continuous_snd.snd')⟩

@[to_additive]
instance pi.has_continuous_mul {C : ι → Type*} [∀ i, topological_space (C i)]
  [∀ i, has_mul (C i)] [∀ i, has_continuous_mul (C i)] : has_continuous_mul (Π i, C i) :=
{ continuous_mul := continuous_pi (λ i, (continuous_apply i).fst'.mul (continuous_apply i).snd') }

/-- A version of `pi.has_continuous_mul` for non-dependent functions. It is needed because sometimes
Lean fails to use `pi.has_continuous_mul` for non-dependent functions. -/
@[to_additive "A version of `pi.has_continuous_add` for non-dependent functions. It is needed
because sometimes Lean fails to use `pi.has_continuous_add` for non-dependent functions."]
instance pi.has_continuous_mul' : has_continuous_mul (ι → M) :=
pi.has_continuous_mul

@[priority 100, to_additive]
instance has_continuous_mul_of_discrete_topology [topological_space N]
  [has_mul N] [discrete_topology N] : has_continuous_mul N :=
⟨continuous_of_discrete_topology⟩

open_locale filter

open function

@[to_additive]
lemma has_continuous_mul.of_nhds_one {M : Type u} [monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) $ 𝓝 1)
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hright : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x*x₀) (𝓝 1)) : has_continuous_mul M :=
⟨begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ p : M × M, x₀ * p.1 * (p.2 * y₀)) = ((λ x, x₀*x) ∘ (λ x, x*y₀)) ∘ (uncurry (*)),
    { ext p, simp [uncurry, mul_assoc] },
    have key₂ : (λ x, x₀*x) ∘ (λ x, y₀*x) = λ x, (x₀ *y₀)*x,
    { ext x, simp },
    calc map (uncurry (*)) (𝓝 (x₀, y₀))
        = map (uncurry (*)) (𝓝 x₀ ×ᶠ 𝓝 y₀) : by rw nhds_prod_eq
    ... = map (λ (p : M × M), x₀ * p.1 * (p.2 * y₀)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq, filter.map_map]
    ... = map ((λ x, x₀ * x) ∘ λ x, x * y₀) (map (uncurry (*)) (𝓝 1 ×ᶠ 𝓝 1))
            : by { rw [key, ← filter.map_map], }
    ... ≤ map ((λ (x : M), x₀ * x) ∘ λ x, x * y₀) (𝓝 1) : map_mono hmul
    ... = 𝓝 (x₀*y₀) : by rw [← filter.map_map, ← hright, hleft y₀, filter.map_map, key₂, ← hleft]
  end⟩

@[to_additive]
lemma has_continuous_mul_of_comm_of_nhds_one (M : Type u) [comm_monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1)) : has_continuous_mul M :=
begin
  apply has_continuous_mul.of_nhds_one hmul hleft,
  intros x₀,
  simp_rw [mul_comm, hleft x₀]
end

end has_continuous_mul

section pointwise_limits

variables (M₁ M₂ : Type*) [topological_space M₂] [t2_space M₂]

@[to_additive] lemma is_closed_set_of_map_one [has_one M₁] [has_one M₂] :
  is_closed {f : M₁ → M₂ | f 1 = 1} :=
is_closed_eq (continuous_apply 1) continuous_const

@[to_additive] lemma is_closed_set_of_map_mul [has_mul M₁] [has_mul M₂] [has_continuous_mul M₂] :
  is_closed {f : M₁ → M₂ | ∀ x y, f (x * y) = f x * f y} :=
begin
  simp only [set_of_forall],
  exact is_closed_Inter (λ x, is_closed_Inter (λ y, is_closed_eq (continuous_apply _)
    ((continuous_apply _).mul (continuous_apply _))))
end

variables {M₁ M₂} [mul_one_class M₁] [mul_one_class M₂] [has_continuous_mul M₂]
  {F : Type*} [monoid_hom_class F M₁ M₂] {l : filter α}

/-- Construct a bundled monoid homomorphism `M₁ →* M₂` from a function `f` and a proof that it
belongs to the closure of the range of the coercion from `M₁ →* M₂` (or another type of bundled
homomorphisms that has a `monoid_hom_class` instance) to `M₁ → M₂`. -/
@[to_additive "Construct a bundled additive monoid homomorphism `M₁ →+ M₂` from a function `f`
and a proof that it belongs to the closure of the range of the coercion from `M₁ →+ M₂` (or another
type of bundled homomorphisms that has a `add_monoid_hom_class` instance) to `M₁ → M₂`.",
  simps { fully_applied := ff }]
def monoid_hom_of_mem_closure_range_coe (f : M₁ → M₂)
  (hf : f ∈ closure (range (λ (f : F) (x : M₁), f x))) : M₁ →* M₂ :=
{ to_fun := f,
  map_one' := (is_closed_set_of_map_one M₁ M₂).closure_subset_iff.2 (range_subset_iff.2 map_one) hf,
  map_mul' := (is_closed_set_of_map_mul M₁ M₂).closure_subset_iff.2
    (range_subset_iff.2 map_mul) hf }

/-- Construct a bundled monoid homomorphism from a pointwise limit of monoid homomorphisms. -/
@[to_additive "Construct a bundled additive monoid homomorphism from a pointwise limit of additive
monoid homomorphisms", simps { fully_applied := ff }]
def monoid_hom_of_tendsto (f : M₁ → M₂) (g : α → F) [l.ne_bot]
  (h : tendsto (λ a x, g a x) l (𝓝 f)) : M₁ →* M₂ :=
monoid_hom_of_mem_closure_range_coe f $ mem_closure_of_tendsto h $
  eventually_of_forall $ λ a, mem_range_self _

variables (M₁ M₂)

@[to_additive] lemma monoid_hom.is_closed_range_coe :
  is_closed (range (coe_fn : (M₁ →* M₂) → (M₁ → M₂))) :=
is_closed_of_closure_subset $ λ f hf, ⟨monoid_hom_of_mem_closure_range_coe f hf, rfl⟩

end pointwise_limits

@[to_additive] lemma inducing.has_continuous_mul {M N F : Type*} [has_mul M] [has_mul N]
  [mul_hom_class F M N] [topological_space M] [topological_space N] [has_continuous_mul N]
  (f : F) (hf : inducing f) :
  has_continuous_mul M :=
⟨hf.continuous_iff.2 $ by simpa only [(∘), map_mul f]
  using (hf.continuous.fst'.mul hf.continuous.snd')⟩

@[to_additive] lemma has_continuous_mul_induced {M N F : Type*} [has_mul M] [has_mul N]
  [mul_hom_class F M N] [topological_space N] [has_continuous_mul N] (f : F) :
  @has_continuous_mul M (induced f ‹_›) _ :=
by { letI := induced f ‹_›, exact inducing.has_continuous_mul f ⟨rfl⟩ }

@[to_additive] instance subsemigroup.has_continuous_mul [topological_space M] [semigroup M]
  [has_continuous_mul M] (S : subsemigroup M) :
  has_continuous_mul S :=
inducing.has_continuous_mul (⟨coe, λ _ _, rfl⟩ : mul_hom S M) ⟨rfl⟩

@[to_additive] instance submonoid.has_continuous_mul [topological_space M] [monoid M]
  [has_continuous_mul M] (S : submonoid M) :
  has_continuous_mul S :=
S.to_subsemigroup.has_continuous_mul

section has_continuous_mul

variables [topological_space M] [monoid M] [has_continuous_mul M]

@[to_additive]
lemma submonoid.top_closure_mul_self_subset (s : submonoid M) :
  closure (s : set M) * closure s ⊆ closure s :=
image2_subset_iff.2 $ λ x hx y hy, map_mem_closure₂ continuous_mul hx hy $
  λ a ha b hb, s.mul_mem ha hb

@[to_additive]
lemma submonoid.top_closure_mul_self_eq (s : submonoid M) :
  closure (s : set M) * closure s = closure s :=
subset.antisymm
  s.top_closure_mul_self_subset
  (λ x hx, ⟨x, 1, hx, subset_closure s.one_mem, mul_one _⟩)

/-- The (topological-space) closure of a submonoid of a space `M` with `has_continuous_mul` is
itself a submonoid. -/
@[to_additive "The (topological-space) closure of an additive submonoid of a space `M` with
`has_continuous_add` is itself an additive submonoid."]
def submonoid.topological_closure (s : submonoid M) : submonoid M :=
{ carrier := closure (s : set M),
  one_mem' := subset_closure s.one_mem,
  mul_mem' := λ a b ha hb, s.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩ }

@[to_additive]
lemma submonoid.le_topological_closure (s : submonoid M) :
  s ≤ s.topological_closure :=
subset_closure

@[to_additive]
lemma submonoid.is_closed_topological_closure (s : submonoid M) :
  is_closed (s.topological_closure : set M) :=
by convert is_closed_closure

@[to_additive]
lemma submonoid.topological_closure_minimal
  (s : submonoid M) {t : submonoid M} (h : s ≤ t) (ht : is_closed (t : set M)) :
  s.topological_closure ≤ t :=
closure_minimal h ht

/-- If a submonoid of a topological monoid is commutative, then so is its topological closure. -/
@[to_additive "If a submonoid of an additive topological monoid is commutative, then so is its
topological closure."]
def submonoid.comm_monoid_topological_closure [t2_space M] (s : submonoid M)
  (hs : ∀ (x y : s), x * y = y * x) : comm_monoid s.topological_closure :=
{ mul_comm :=
    have ∀ (x ∈ s) (y ∈ s), x * y = y * x,
      from λ x hx y hy, congr_arg subtype.val (hs ⟨x, hx⟩ ⟨y, hy⟩),
    λ ⟨x, hx⟩ ⟨y, hy⟩, subtype.ext $
      eq_on_closure₂ this continuous_mul (continuous_snd.mul continuous_fst) x hx y hy,
  ..s.topological_closure.to_monoid }

@[to_additive exists_open_nhds_zero_half]
lemma exists_open_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
have ((λa:M×M, a.1 * a.2) ⁻¹' s) ∈ 𝓝 ((1, 1) : M × M),
  from tendsto_mul (by simpa only [one_mul] using hs),
by simpa only [prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_zero_half]
lemma exists_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M), ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
in ⟨V, is_open.mem_nhds Vo V1, hV⟩

@[to_additive exists_nhds_zero_quarter]
lemma exists_nhds_one_split4 {u : set M} (hu : u ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M),
    ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩,
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩,
  use [V, V1],
  intros v w s t v_in w_in s_in t_in,
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
end

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
lemma exists_open_nhds_one_mul_subset {U : set M} (hU : U ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ V * V ⊆ U :=
begin
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩,
  use [V, Vo, V1],
  rintros _ ⟨x, y, hx, hy, rfl⟩,
  exact hV _ hx _ hy
end

@[to_additive]
lemma is_compact.mul {s t : set M} (hs : is_compact s) (ht : is_compact t) : is_compact (s * t) :=
by { rw [← image_mul_prod], exact (hs.prod ht).image continuous_mul }

@[to_additive]
lemma tendsto_list_prod {f : ι → α → M} {x : filter α} {a : ι → M} :
  ∀ l:list ι, (∀i∈l, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive]
lemma continuous_list_prod {f : ι → X → M} (l : list ι)
  (h : ∀ i ∈ l, continuous (f i)) :
  continuous (λ a, (l.map (λ i, f i a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

@[to_additive]
lemma continuous_on_list_prod {f : ι → X → M} (l : list ι) {t : set X}
  (h : ∀ i ∈ l, continuous_on (f i) t) :
  continuous_on (λ a, (l.map (λ i, f i a)).prod) t :=
begin
  intros x hx,
  rw continuous_within_at_iff_continuous_at_restrict _ hx,
  refine tendsto_list_prod _ (λ i hi, _),
  specialize h i hi x hx,
  rw continuous_within_at_iff_continuous_at_restrict _ hx at h,
  exact h,
end

@[continuity, to_additive]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : M, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := by { simp only [pow_succ], exact continuous_id.mul (continuous_pow _) }

instance add_monoid.has_continuous_const_smul_nat {A} [add_monoid A] [topological_space A]
  [has_continuous_add A] : has_continuous_const_smul ℕ A := ⟨continuous_nsmul⟩

instance add_monoid.has_continuous_smul_nat {A} [add_monoid A] [topological_space A]
  [has_continuous_add A] : has_continuous_smul ℕ A :=
⟨continuous_uncurry_of_discrete_topology continuous_nsmul⟩

@[continuity, to_additive continuous.nsmul]
lemma continuous.pow {f : X → M} (h : continuous f) (n : ℕ) :
  continuous (λ b, (f b) ^ n) :=
(continuous_pow n).comp h

@[to_additive]
lemma continuous_on_pow {s : set M} (n : ℕ) : continuous_on (λ x, x ^ n) s :=
(continuous_pow n).continuous_on

@[to_additive]
lemma continuous_at_pow (x : M) (n : ℕ) : continuous_at (λ x, x ^ n) x :=
(continuous_pow n).continuous_at

@[to_additive filter.tendsto.nsmul]
lemma filter.tendsto.pow {l : filter α} {f : α → M} {x : M} (hf : tendsto f l (𝓝 x)) (n : ℕ) :
  tendsto (λ x, f x ^ n) l (𝓝 (x ^ n)) :=
(continuous_at_pow _ _).tendsto.comp hf

@[to_additive continuous_within_at.nsmul]
lemma continuous_within_at.pow {f : X → M} {x : X} {s : set X} (hf : continuous_within_at f s x)
  (n : ℕ) : continuous_within_at (λ x, f x ^ n) s x :=
hf.pow n

@[to_additive continuous_at.nsmul]
lemma continuous_at.pow {f : X → M} {x : X} (hf : continuous_at f x) (n : ℕ) :
  continuous_at (λ x, f x ^ n) x :=
hf.pow n

@[to_additive continuous_on.nsmul]
lemma continuous_on.pow {f : X → M} {s : set X} (hf : continuous_on f s) (n : ℕ) :
  continuous_on (λ x, f x ^ n) s :=
λ x hx, (hf x hx).pow n

/-- Left-multiplication by a left-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) :
  filter.tendsto (λ x : M, a * x) (filter.cocompact M) (filter.cocompact M) :=
begin
  refine filter.tendsto.of_tendsto_comp _ (filter.comap_cocompact_le (continuous_mul_left b)),
  convert filter.tendsto_id,
  ext x,
  simp [ha],
end

/-- Right-multiplication by a right-invertible element of a topological monoid is proper, i.e.,
inverse images of compact sets are compact. -/
lemma filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) :
  filter.tendsto (λ x : M, x * a) (filter.cocompact M) (filter.cocompact M) :=
begin
  refine filter.tendsto.of_tendsto_comp _ (filter.comap_cocompact_le (continuous_mul_right b)),
  convert filter.tendsto_id,
  ext x,
  simp [ha],
end

/-- If `R` acts on `A` via `A`, then continuous multiplication implies continuous scalar
multiplication by constants.

Notably, this instances applies when `R = A`, or when `[algebra R A]` is available. -/
@[priority 100, to_additive  "If `R` acts on `A` via `A`, then continuous addition implies
continuous affine addition by constants."]
instance is_scalar_tower.has_continuous_const_smul {R A : Type*} [monoid A] [has_smul R A]
  [is_scalar_tower R A A] [topological_space A] [has_continuous_mul A] :
  has_continuous_const_smul R A :=
{ continuous_const_smul := λ q, begin
    simp only [←smul_one_mul q (_ : A)] { single_pass := tt },
    exact continuous_const.mul continuous_id,
  end }

/-- If the action of `R` on `A` commutes with left-multiplication, then continuous multiplication
implies continuous scalar multiplication by constants.

Notably, this instances applies when `R = Aᵐᵒᵖ` -/
@[priority 100, to_additive "If the action of `R` on `A` commutes with left-addition, then
continuous addition implies continuous affine addition by constants.

Notably, this instances applies when `R = Aᵃᵒᵖ`. "]
instance smul_comm_class.has_continuous_const_smul {R A : Type*} [monoid A] [has_smul R A]
  [smul_comm_class R A A] [topological_space A] [has_continuous_mul A] :
  has_continuous_const_smul R A :=
{ continuous_const_smul := λ q, begin
    simp only [←mul_smul_one q (_ : A)] { single_pass := tt },
    exact continuous_id.mul continuous_const,
  end }

end has_continuous_mul

namespace mul_opposite

/-- If multiplication is continuous in `α`, then it also is in `αᵐᵒᵖ`. -/
@[to_additive "If addition is continuous in `α`, then it also is in `αᵃᵒᵖ`."]
instance [topological_space α] [has_mul α] [has_continuous_mul α] : has_continuous_mul αᵐᵒᵖ :=
⟨continuous_op.comp (continuous_unop.snd'.mul continuous_unop.fst')⟩

end mul_opposite

namespace units

open mul_opposite

variables [topological_space α] [monoid α] [has_continuous_mul α]

/-- If multiplication on a monoid is continuous, then multiplication on the units of the monoid,
with respect to the induced topology, is continuous.

Inversion is also continuous, but we register this in a later file, `topology.algebra.group`,
because the predicate `has_continuous_inv` has not yet been defined. -/
@[to_additive "If addition on an additive monoid is continuous, then addition on the additive units
of the monoid, with respect to the induced topology, is continuous.

Negation is also continuous, but we register this in a later file, `topology.algebra.group`, because
the predicate `has_continuous_neg` has not yet been defined."]
instance : has_continuous_mul αˣ := inducing_embed_product.has_continuous_mul (embed_product α)

end units

@[to_additive] lemma continuous.units_map [monoid M] [monoid N] [topological_space M]
  [topological_space N] (f : M →* N) (hf : continuous f) : continuous (units.map f) :=
units.continuous_iff.2 ⟨hf.comp units.continuous_coe, hf.comp units.continuous_coe_inv⟩

section

variables [topological_space M] [comm_monoid M]

@[to_additive]
lemma submonoid.mem_nhds_one (S : submonoid M) (oS : is_open (S : set M)) :
  (S : set M) ∈ 𝓝 (1 : M) :=
is_open.mem_nhds oS S.one_mem

variable [has_continuous_mul M]

@[to_additive]
lemma tendsto_multiset_prod {f : ι → α → M} {x : filter α} {a : ι → M} (s : multiset ι) :
  (∀ i ∈ s, tendsto (f i) x (𝓝 (a i))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simpa using tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : ι → α → M} {x : filter α} {a : ι → M} (s : finset ι) :
  (∀ i ∈ s, tendsto (f i) x (𝓝 (a i))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[continuity, to_additive]
lemma continuous_multiset_prod {f : ι → X → M} (s : multiset ι) :
  (∀ i ∈ s, continuous (f i)) → continuous (λ a, (s.map (λ i, f i a)).prod) :=
by { rcases s with ⟨l⟩, simpa using continuous_list_prod l }

@[to_additive]
lemma continuous_on_multiset_prod {f : ι → X → M} (s : multiset ι) {t : set X} :
  (∀i ∈ s, continuous_on (f i) t) → continuous_on (λ a, (s.map (λ i, f i a)).prod) t :=
by { rcases s with ⟨l⟩, simpa using continuous_on_list_prod l }

@[continuity, to_additive]
lemma continuous_finset_prod {f : ι → X → M} (s : finset ι) :
  (∀ i ∈ s, continuous (f i)) → continuous (λ a, ∏ i in s, f i a) :=
continuous_multiset_prod _

@[to_additive]
lemma continuous_on_finset_prod {f : ι → X → M} (s : finset ι) {t : set X} :
  (∀ i ∈ s, continuous_on (f i) t) → continuous_on (λ a, ∏ i in s, f i a) t :=
continuous_on_multiset_prod _

@[to_additive] lemma eventually_eq_prod {X M : Type*} [comm_monoid M]
  {s : finset ι} {l : filter X} {f g : ι → X → M} (hs : ∀ i ∈ s, f i =ᶠ[l] g i) :
  ∏ i in s, f i =ᶠ[l] ∏ i in s, g i :=
begin
  replace hs: ∀ᶠ x in l, ∀ i ∈ s, f i x = g i x,
  { rwa eventually_all_finset },
  filter_upwards [hs] with x hx,
  simp only [finset.prod_apply, finset.prod_congr rfl hx],
end

open function

@[to_additive]
lemma locally_finite.exists_finset_mul_support {M : Type*} [comm_monoid M] {f : ι → X → M}
  (hf : locally_finite (λ i, mul_support $ f i)) (x₀ : X) :
  ∃ I : finset ι, ∀ᶠ x in 𝓝 x₀, mul_support (λ i, f i x) ⊆ I :=
begin
  rcases hf x₀ with ⟨U, hxU, hUf⟩,
  refine ⟨hUf.to_finset, mem_of_superset hxU $ λ y hy i hi, _⟩,
  rw [hUf.coe_to_finset],
  exact ⟨y, hi, hy⟩
end

@[to_additive] lemma finprod_eventually_eq_prod {M : Type*} [comm_monoid M]
  {f : ι → X → M} (hf : locally_finite (λ i, mul_support (f i))) (x : X) :
  ∃ s : finset ι, ∀ᶠ y in 𝓝 x, (∏ᶠ i, f i y) = ∏ i in s, f i y :=
let ⟨I, hI⟩ := hf.exists_finset_mul_support x in
  ⟨I, hI.mono (λ y hy, finprod_eq_prod_of_mul_support_subset _ $ λ i hi, hy hi)⟩

@[to_additive] lemma continuous_finprod {f : ι → X → M} (hc : ∀ i, continuous (f i))
  (hf : locally_finite (λ i, mul_support (f i))) :
  continuous (λ x, ∏ᶠ i, f i x) :=
begin
  refine continuous_iff_continuous_at.2 (λ x, _),
  rcases finprod_eventually_eq_prod hf x with ⟨s, hs⟩,
  refine continuous_at.congr _ (eventually_eq.symm hs),
  exact tendsto_finset_prod _ (λ i hi, (hc i).continuous_at),
end

@[to_additive] lemma continuous_finprod_cond {f : ι → X → M} {p : ι → Prop}
  (hc : ∀ i, p i → continuous (f i)) (hf : locally_finite (λ i, mul_support (f i))) :
  continuous (λ x, ∏ᶠ i (hi : p i), f i x) :=
begin
  simp only [← finprod_subtype_eq_finprod_cond],
  exact continuous_finprod (λ i, hc i i.2) (hf.comp_injective subtype.coe_injective)
end

end

instance [topological_space M] [has_mul M] [has_continuous_mul M] :
  has_continuous_add (additive M) :=
{ continuous_add := @continuous_mul M _ _ _ }

instance [topological_space M] [has_add M] [has_continuous_add M] :
  has_continuous_mul (multiplicative M) :=
{ continuous_mul := @continuous_add M _ _ _ }

section lattice_ops

variables {ι' : Sort*} [has_mul M]

@[to_additive] lemma has_continuous_mul_Inf {ts : set (topological_space M)}
  (h : Π t ∈ ts, @has_continuous_mul M t _) :
  @has_continuous_mul M (Inf ts) _ :=
{ continuous_mul := continuous_Inf_rng.2 (λ t ht, continuous_Inf_dom₂ ht ht
  (@has_continuous_mul.continuous_mul M t _ (h t ht))) }

@[to_additive] lemma has_continuous_mul_infi {ts : ι' → topological_space M}
  (h' : Π i, @has_continuous_mul M (ts i) _) :
  @has_continuous_mul M (⨅ i, ts i) _ :=
by { rw ← Inf_range, exact has_continuous_mul_Inf (set.forall_range_iff.mpr h') }

@[to_additive] lemma has_continuous_mul_inf {t₁ t₂ : topological_space M}
  (h₁ : @has_continuous_mul M t₁ _) (h₂ : @has_continuous_mul M t₂ _) :
  @has_continuous_mul M (t₁ ⊓ t₂) _ :=
by { rw inf_eq_infi, refine has_continuous_mul_infi (λ b, _), cases b; assumption }

end lattice_ops

namespace continuous_map

variables [has_mul X] [has_continuous_mul X]

/-- The continuous map `λ y, y * x` -/
@[to_additive "The continuous map `λ y, y + x"]
protected def mul_right (x : X) : C(X, X) := mk _ (continuous_mul_right x)

@[to_additive, simp]
lemma coe_mul_right (x : X) : ⇑(continuous_map.mul_right x) = λ y, y * x := rfl

/-- The continuous map `λ y, x * y` -/
@[to_additive "The continuous map `λ y, x + y"]
protected def mul_left (x : X) : C(X, X) := mk _ (continuous_mul_left x)

@[to_additive, simp]
lemma coe_mul_left (x : X) : ⇑(continuous_map.mul_left x) = λ y, x * y := rfl

end continuous_map
