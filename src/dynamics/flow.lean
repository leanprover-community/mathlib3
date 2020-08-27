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

open set function filter

/-- a flow is a continuous action of a (topological, additive) monoid
    on a topological space. -/
structure flow
  (T : Type*) [topological_space T] [add_monoid T] [has_continuous_add T] 
  (X : Type*) [topological_space X] :=
(to_fun    : T → X → X)
(cont'     : continuous ↿to_fun)
(map_add'  : ∀ t₁ t₂ x, to_fun t₂ (to_fun t₁ x) = to_fun (t₁ + t₂) x)
(map_zero' : ∀ x, to_fun 0 x = x)

namespace flow

section

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T] [add_monoid T] [has_continuous_add T]

variables (ϕ : flow T X)

instance : has_coe_to_fun (flow T X) := ⟨λ _,  _, flow.to_fun⟩
instance has_uncurry_flow : has_uncurry (flow T X) (T × X) X :=
⟨λ f p, f.to_fun p.1 p.2⟩

@[ext]
lemma ext : ∀ {ϕ₁ ϕ₂ : flow T X}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _, _, _⟩ ⟨f₂, _, _, _⟩ h := by { congr, funext, apply h }

@[continuity]
lemma cont : continuous ↿ϕ := ϕ.cont'

@[simp]
lemma map_add (t₁ t₂ : T) (x : X): ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x := ϕ.map_add' _ _ _

@[simp]
lemma map_zero (x : X) : ϕ 0 x = x := ϕ.map_zero' _

/-!
### invariant sets and omega limits
-/

variable (S : set X)

/-- a set S ⊆ X is invariant under a flow ϕ on X if ϕ x t ∈ ϕ for all
    x ∈ S, t ∈ T. -/
def invariant : Prop := ∀ (x ∈ S) t, ϕ t x ∈ S

lemma invariant_of_image2_subset {S} (h : image2 ϕ univ S ⊆ S) : invariant ϕ S :=
λ _ hx _, h ⟨_, _, mem_univ _, hx, rfl⟩

lemma invariant_iff_image2_eq (S : set X) : invariant ϕ S ↔ image2 ϕ univ S = S :=
iff.intro
  (λ h, subset.antisymm
    (λ _ ⟨_, _, _, hx, htx⟩, htx ▸ h _ hx _)
    (λ x hx, ⟨0, x, mem_univ _, hx, map_zero _ _⟩))
  (λ h, invariant_of_image2_subset ϕ (h.symm ▸ subset.refl S))

/-- the induced flow on an invariant set S ⊆ X. -/
def restrict (h : invariant ϕ S) : flow T ↥S :=
{ to_fun    := λ t x, ⟨ϕ t x,h _ x.property _⟩,
  cont'     := continuous_subtype_mk _ $
    show continuous (↿ϕ ∘ λ p : T × ↥S, (p.fst, ↑p.snd)),
    from ϕ.cont.comp (continuous.prod_map continuous_id continuous_subtype_coe),
  map_zero' := λ _, subtype.ext (ϕ.map_zero _),
  map_add'  := λ _ _ _, subtype.ext (ϕ.map_add _ _ _) }

/-- the ω-limit of S ⊆ X w.r.t a filter f on T is the intersection of
    all the closures of ϕ S u where u ∈ f.

    When T is ℕ or ℝ and f is `filter.at_top`, this coincides with the
    usual definition; `omega_limit at_bot ϕ S` is the α-limit set. -/
def omega_limit (f : filter T) (ϕ : flow T X) (S : set X) : set X :=
⋂ u ∈ f, closure (image2 ϕ u S)
local notation `ω` := omega_limit

variables (f : filter T)

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

/-- the omega limit w.r.t a translation-invariant filter is invariant. -/
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

end

section

-- henceforth we let T be a linearly ordered group in addition to a
-- topological monoid, with the expectation that T is ℕ or ℝ. this
-- allows us to speak of time-reversal of a flow, among other things.

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T]
[decidable_linear_ordered_add_comm_group T] [topological_add_group T]

variables (ϕ : flow T X)

instance : has_inv (flow T X) := ⟨λ ϕ, {
  to_fun    := λ t x, ϕ (-t) x,
  cont'     := show continuous $ ↿ϕ ∘ λ p : T × X, (-p.fst, p.snd),
               from ϕ.cont.comp (by continuity),
  map_add'  := λ _ _ _, by rw [map_add, neg_add],
  map_zero' := λ _, by rw [neg_zero, map_zero]
}⟩

lemma inv_def (t : T) (x : X): ϕ⁻¹ t x = ϕ (-t) x := rfl

@[simp]
lemma inv_inv : (ϕ⁻¹)⁻¹ = ϕ := ext $ λ _ _, by rw [inv_def, inv_def, neg_neg]

variable (S : set X)

local notation `ω₊` := omega_limit at_top
local notation `ω₋` := omega_limit at_bot

end

end flow

