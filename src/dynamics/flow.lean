import topology.metric_space.hausdorff_distance
import algebra.add_torsor
import analysis.convex.caratheodory

-- stolen from #3694:
section uncurry

variables {α β γ δ : Type*}

/-- Records a way to turn an element of `α` into a function from `β` to `γ`. -/
class has_uncurry (α : Type*) (β : out_param Type*) (γ : out_param Type*) := (uncurry : α → (β → γ))

notation `↿`:max x:max := has_uncurry.uncurry x
instance has_uncurry_base : has_uncurry (α → β) α β := ⟨id⟩

instance has_uncurry_induction [has_uncurry β γ δ] : has_uncurry (α → β) (α × γ) δ :=
⟨λ f p, ↿(f p.1) p.2⟩

end uncurry

-- some lemmas that possibly should be in mathlib / have equivalents
-- in mathlib somewhere (topology/constructions?) if not already:
section

open function

variables
{α : Type*} [topological_space α]
{β : Type*} [topological_space β]
{γ : Type*} [topological_space γ]

variables (f : α → β → γ) (g : α × β → γ)

lemma continuous_uncurry_left (a : α) (h : continuous ↿f) : continuous (f a) :=
show continuous (↿f ∘ (λ b, (a, b))), from h.comp (by continuity)

lemma continuous_uncurry_right (b : β) (h : continuous ↿f) : continuous (λ a, f a b) :=
show continuous (↿f ∘ (λ a, (a, b))), from h.comp (by continuity)

lemma continuous_curry (a : α) (h : continuous g) : continuous (curry g a) :=
show continuous (g ∘ (λ b, (a, b))), from h.comp (by continuity)

end

-- here begins the dynamical systems content.

section

set_option default_priority 100

open set function filter

/-- a semigroup flow is a continuous act of a (topological,
   additive) semigroup on a topological space. -/

-- `algebra/add_torsor` already defines additive monoid actions. But
-- we will want to consider families of flows on the same space, in
-- which case we probably don't want the type class
-- resolution. Additionally, the `+̬` notation isn't typical in this
-- context, and also I thiiink the order of some arguments are
-- different.

structure semigroup_flow
  (T : Type*) [topological_space T] [add_semigroup T] [has_continuous_add T]
  (X : Type*) [topological_space X] :=
(to_fun    : T → X → X)
(cont      : continuous ↿to_fun)
(map_add'  : ∀ t₁ t₂ x, to_fun t₂ (to_fun t₁ x) = to_fun (t₁ + t₂) x)

-- at the moment, I am not familiar with the study of continuous
-- semigroup flows beyond being aware that the literature
-- exists. Nevertheless, it is probably easier to refactor for
-- stronger hypotheses than for weaker ones, so this is what the code
-- looks like now.

namespace semigroup_flow

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T] [add_semigroup T] [has_continuous_add T]

variables (f : filter T) (ϕ : semigroup_flow T X)

instance : has_coe_to_fun (semigroup_flow T X) := ⟨_, semigroup_flow.to_fun⟩
instance has_uncurry_semigroup_flow : has_uncurry (semigroup_flow T X) (T × X) X :=
⟨λ f p, f.to_fun p.1 p.2⟩

@[ext] lemma ext : ∀ {ϕ₁ ϕ₂ : semigroup_flow T X}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _, _⟩ ⟨f₂, _, _⟩ h := by { congr, funext, apply h }

@[continuity] protected lemma continuous : continuous ↿ϕ := ϕ.cont

@[simp] lemma map_add (t₁ t₂ : T) (x : X): ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x := ϕ.map_add' _ _ _

/-!
### invariant sets and omega limits
-/

variable (S : set X)

/-- a set S ⊆ X is invariant under a flow ϕ on X if ϕ x t ∈ ϕ for all
    x ∈ S, t ∈ T. -/
def invariant : Prop := ∀ (x ∈ S) t, ϕ t x ∈ S

lemma invariant_of_image2_subset {S} (h : image2 ϕ univ S ⊆ S) : invariant ϕ S :=
λ _ hx _, h ⟨_, _, mem_univ _, hx, rfl⟩

/-- the induced semigroup flow on an invariant set S ⊆ X. -/
def restrict (h : invariant ϕ S) : semigroup_flow T ↥S :=
{ to_fun    := λ t x, ⟨ϕ t x,h _ x.property _⟩,
  cont     := continuous_subtype_mk _ $
    show continuous (↿ϕ ∘ λ p : T × ↥S, (p.fst, ↑p.snd)),
    from ϕ.continuous.comp (continuous.prod_map continuous_id continuous_subtype_coe),
  map_add'  := λ _ _ _, subtype.ext (ϕ.map_add _ _ _) }

/-- the ω-limit of S ⊆ X w.r.t a filter f on T is the intersection of
    all the closures of ϕ S u where u ∈ f.

    When T is ℕ or ℝ and f is `filter.at_top`, this coincides with the
    usual definition; `omega_limit at_bot ϕ S` is the α-limit set. -/
def omega_limit : set X := ⋂ u ∈ f, closure (image2 ϕ u S)

local notation `ω` := omega_limit

lemma is_closed_omega_limit : is_closed (ω f ϕ S) :=
is_closed_Inter $ λ _, is_closed_Inter $ λ _, is_closed_closure

lemma omega_limit_mono {S₁ S₂} (h : S₁ ⊆ S₂) : ω f ϕ S₁ ⊆ ω f ϕ S₂ :=
Inter_subset_Inter $ λ _, Inter_subset_Inter $ λ _, closure_mono $ image2_subset subset.rfl h

lemma omega_limit_inter_subset {S₁ S₂} : ω f ϕ (S₁ ∩ S₂) ⊆ ω f ϕ S₁ ∩ ω f ϕ S₂ :=
subset_inter
  (omega_limit_mono _ _ (inter_subset_left  _ _))
  (omega_limit_mono _ _ (inter_subset_right _ _))

lemma union_omega_limit_subset {S₁ S₂} : ω f ϕ S₁ ∪ ω f ϕ S₂ ⊆ ω f ϕ (S₁ ∪ S₂) :=
union_subset
  (omega_limit_mono _ _ (subset_union_left  _ _))
  (omega_limit_mono _ _ (subset_union_right _ _))

lemma flow_image2_eq (I : set T) (t : T) : ϕ t '' image2 ϕ I S = image2 ϕ ((+ t) '' I) S :=
by simp_rw [image_image2, map_add, image2_image_left]

-- because of the way omega_limit is defined, the next proof & many
-- more in the sequel contain nested invocations of things like
-- Inter_subset_Inter. Is this unavoidable? is there a tactic
-- analogous to `funext` that allows for intro-ing all the indicies at
-- once?

/-- a filter f is translation-invariant if u ∈ f ↔ (+ t) ⁻¹' u ∈ f.

    the omega limit w.r.t a translation-invariant filter is invariant. -/
lemma invariant_omega_limit (h : ∀ (t : T), tendsto (+ t) f f) :
  invariant ϕ (ω f ϕ S) :=
begin
  rintro x hx t cϕu ⟨u, hcϕu⟩,
  rw ←hcϕu,
  calc ϕ t x ∈ ϕ t '' (⋂ u ∈ f, closure (image2 ϕ u S)) : mem_image_of_mem _ hx
  ...        ⊆ ⋂ u ∈ f, ϕ t '' closure (image2 ϕ u S) :
  subset.trans (image_Inter_subset _ _) (Inter_subset_Inter (λ _, image_Inter_subset _ _))
  ...        ⊆ ⋂ u ∈ f, closure (ϕ t '' image2 ϕ u S) :
  Inter_subset_Inter (λ _, Inter_subset_Inter (λ _,
    image_closure_subset_closure_image (continuous_uncurry_left _ _ ϕ.cont)))
  ...        ⊆ ⋂ u ∈ f, closure (image2 ϕ ((+ t) '' u) S) :
  by simp_rw [flow_image2_eq, subset.rfl]
  ...        ⊆ ⋂ u ∈ f, closure (image2 ϕ u S) :
  begin
    apply Inter_subset_Inter2, intro u,
    use (+ t) ⁻¹' u,
    apply Inter_subset_Inter2, intro hu,
    simp_rw tendsto_def at h, use h t _ hu,
    exact closure_mono (image2_subset (image_preimage_subset _ _) subset.rfl)
  end
  ...        ⊆ ⋂ (hu : u ∈ f), closure (image2 ϕ u S) : Inter_subset _ _
end

-- a point x is in the ω-limit of S if the forward-images of S
-- frequently intersect arbitrarily small neighbourhoods of x.
--
-- for T = ℕ and f = at_top, recover the "there exists sequences..."
-- definition.
lemma mem_omega_limit_iff_frequently (x : X) :
  x ∈ ω f ϕ S ↔ ∀ v ∈ nhds x, ∃ᶠ t in f, (S ∩ ϕ t ⁻¹' v).nonempty :=
begin
  unfold omega_limit,
  simp_rw frequently_iff,
  split,
  { intros h v hv u hu,
    simp_rw mem_Inter at h,
    have h₂, from mem_closure_iff_nhds.mp (h u hu) v hv,
    rcases h₂ with ⟨ϕty, hyv, t, y, ht, hy, hϕty⟩,
    exact ⟨t, ht, y, hy, show ϕ t y ∈ v, by rwa hϕty⟩ },
  { rintro h c ⟨u, hc⟩,
    rw [←hc, mem_Inter],
    intro hu,
    rw mem_closure_iff_nhds,
    intros v hv,
    rcases  h v hv hu with ⟨t, ht, y, hy, hϕty⟩,
    exact ⟨ϕ t y, hϕty, t, y, ht, hy, rfl⟩ },
end

-- (work in progress.)

end semigroup_flow

/-- a flow on a topological space X by an additive monoid T is a
    continuous monoid act. -/
structure flow
  (T : Type*) [topological_space T] [add_monoid T] [has_continuous_add T]
  (X : Type*) [topological_space X] extends semigroup_flow T X :=
(map_zero' : ∀ x, to_fun 0 x = x)

namespace flow
open semigroup_flow

section

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T] [add_monoid T] [has_continuous_add T]

instance : has_coe (flow T X) (semigroup_flow T X) := ⟨flow.to_semigroup_flow⟩
instance : has_coe_to_fun (flow T X) := ⟨_, λ ϕ, ϕ.to_semigroup_flow.to_fun⟩

instance has_uncurry_flow : has_uncurry (flow T X) (T × X) X := ⟨λ ϕ, ↿ϕ.to_semigroup_flow⟩

variables (f : filter T) (ϕ : flow T X)

@[ext] lemma ext : ∀ {ϕ₁ ϕ₂ : flow T X}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _⟩ ⟨f₂, _⟩ h := by { congr, apply semigroup_flow.ext, apply h }

-- several definitions follow that duplicate the corresponding
-- statements for semigroup_flow, so that they can be referred to
-- without explicitly asking lean to do the coercion. is there a nicer
-- way to do this?

-- (https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/preferred.20alternatives.20to.20type.20ascriptions.20everywhere.3F)

@[continuity] protected lemma continuous : continuous ↿ϕ := ϕ.cont

@[simp] lemma map_add (t₁ t₂ : T) (x : X) : ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x := ϕ.map_add' _ _ _

@[simp] lemma map_zero (x : X) : ϕ 0 x = x := ϕ.map_zero' _

-- make some lemmas available to `simp` so that a flow is always
-- applied in terms of its coercion to a function.

-- (is this a bad idea?)

@[simp] lemma to_fun_eq_coe : ϕ.to_fun = ⇑ϕ := rfl
@[simp] lemma coe_coe : ((ϕ : semigroup_flow T X) : T → X → X) = ϕ := rfl

variable (S : set X)

/-- a set is invariant under a flow ϕ if it is invariant under ϕ as a semigroup-flow. -/
def invariant : Prop := (ϕ : semigroup_flow T X).invariant S

lemma invariant_iff_image2_eq : ϕ.invariant S ↔ image2 ϕ univ S = S :=
iff.intro
  (λ h, subset.antisymm
    (λ _ ⟨_, _, _, hx, htx⟩, htx ▸ h _ hx _)
    (λ _ hx, ⟨0, _, mem_univ _, hx, map_zero _ _⟩))
  (λ h, invariant_of_image2_subset ϕ (h.symm ▸ subset.refl S))

/-- the induced flow on an invariant set S ⊆ X. -/
def restrict (h : ϕ.invariant S) : flow T ↥S :=
{ map_zero' := λ x, subtype.ext (map_zero _ _)
  .. ϕ.to_semigroup_flow.restrict _ h }

/-- the ω-limit of S ⊆ X under a flow ϕ w.r.t. a filter f on T is the
    ω-limit of S under ϕ as a semigroup-flow w.r.t f. -/
def omega_limit : set X := semigroup_flow.omega_limit f ϕ S

lemma omega_limit_def (f : filter T) (ϕ : flow T X) (S : set X) :
  omega_limit f ϕ S = ⋂ u ∈ f, closure (image2 ϕ u S) :=
by { rw ←coe_coe, refl }

end

section

-- henceforth we let T be a linearly ordered (additive, commutative)
-- group in addition to a topological monoid, with the expectation
-- that T is ℕ or ℝ. this makes it possible to speak of time-reversal
-- of a flow, among other things.

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T]
[decidable_linear_ordered_add_comm_group T] [topological_add_group T]

/-- the time-reversal of a flow ϕ is defined ϕ.reverse t x = ϕ (-t) x. -/
def reverse (ϕ : flow T X) : flow T X :=
{ to_fun    := λ t x, ϕ (-t) x,
  cont      := show continuous $ ↿ϕ ∘ λ p : T × X, (-p.fst, p.snd),
               from ϕ.continuous.comp (by continuity),
  map_add'  := λ _ _ _, by rw [map_add, neg_add],
  map_zero' := λ x, show ϕ (-0) x = x, by rw [neg_zero, map_zero] }

variables (ϕ : flow T X)

lemma reverse_def (t : T) (x : X): ϕ.reverse t x = ϕ (-t) x := rfl
lemma reverse_def' (t : T) : ϕ.reverse t = ϕ (-t) := funext (λ x, reverse_def _ _ _)

@[simp] lemma reverse_reverse : ϕ.reverse.reverse = ϕ :=
ext $ λ _ _, by simp only [reverse_def, neg_neg]

variable (S : set X)

local notation `ω₊` := omega_limit at_top
local notation `ω₋` := omega_limit at_bot

lemma invariant_omega_limit_at_top : ϕ.invariant (ω₊ ϕ S) :=
invariant_omega_limit _ _ _ (λ t, tendsto_at_top_add_const_right _ _ tendsto_id)

lemma invariant_omega_limit_at_bot : ϕ.invariant (ω₋ ϕ S) :=
invariant_omega_limit _ _ _ (λ t, tendsto_at_bot_add_const_right _ _ tendsto_id)

-- recover the usual definition of ω-limit sets:
lemma omega_limit_at_top_eq : ω₊ ϕ S = ⋂ t, closure (image2 ϕ (Ici t) S) :=
begin
  apply subset.antisymm,
  { apply Inter_subset_Inter2, intro t, use Ici t,
    exact Inter_subset_of_subset (mem_at_top _) (closure_mono subset.rfl) },
  { apply subset_Inter, intro u,
    apply subset_Inter, intro hu,
    rcases mem_at_top_sets.mp hu with ⟨b, hb⟩,
    calc (⋂ t, closure (image2 ϕ (Ici t) S))
    ⊆ closure (image2 ϕ (Ici b) S) : Inter_subset _ _
... ⊆ closure (image2 ϕ u S) : closure_mono (image2_subset (λ _ hs, hb _ hs) subset.rfl) }
end

lemma image2_reverse_eq (I : set T) (S : set X):
  image2 ϕ.reverse I S = image2 ϕ (has_neg.neg '' I) S :=
by simp_rw [image2_image_left, ←reverse_def']

/-- the α-limit of ϕ is the ω-limit of the time-reversal of ϕ -/

-- I think this amounts to proving tendsto_neg_at_bot_at_top.
-- TODO : refactor to make this obvious.
lemma omega_limit_at_top_reverse : ω₋ ϕ S = ω₊ ϕ.reverse S :=
begin
  rw [omega_limit_def, omega_limit_def],
  apply subset.antisymm,
  all_goals { apply Inter_subset_Inter2, intro u, use has_neg.neg '' u,
              apply Inter_subset_Inter2, intro hu },
  { rcases mem_at_top_sets.mp hu with ⟨b, hb⟩,
    use mem_at_bot_sets.mpr
      ⟨_, λ _ hs, (mem_image _ _ _).mpr ⟨_, hb _ (le_neg.mp hs), neg_neg _⟩⟩,
    rw image2_reverse_eq,
    exact subset.rfl },
  { rcases mem_at_bot_sets.mp hu with ⟨b, hb⟩,
    use mem_at_top_sets.mpr
      ⟨_, λ _ hs, (mem_image _ _ _).mpr ⟨_, hb _ (neg_le.mp hs), neg_neg _⟩⟩,
    simp_rw [image2_reverse_eq, image_image, neg_neg, image_id'],
    exact subset.rfl }
end

end

end flow

end
