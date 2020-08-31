import topology.metric_space.hausdorff_distance

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

section -- invariant subsets & omega limits

variables {T : Type*} {X : Type*} {Y : Type*}

/-! ### invariant subsets -/
section is_invariant

/-- a set `S ⊆ X` is invariant under `ϕ : T → X → X` if `ϕ t S ⊆ S`
    for all `t`. -/
def is_invariant (ϕ : T → X → X) (S : set X) : Prop :=
∀ t (x ∈ S), ϕ t x ∈ S

variables (ϕ : T → X → X) (S : set X)

lemma is_invariant_iff_image2_subset : is_invariant ϕ S ↔ image2 ϕ univ S ⊆ S :=
iff.intro
  (λ h _ ⟨_, _, ht, hx, htx⟩, htx ▸ h _ _ hx)
  (λ h _ _ hx, h ⟨_, _, mem_univ _, hx, rfl⟩)

lemma is_invariant_iff_subset_preimage : is_invariant ϕ S ↔  ∀ t, S ⊆ ϕ t ⁻¹' S := iff.rfl

lemma is_invariant_iff_image_subset : is_invariant ϕ S ↔ ∀  t, ϕ t '' S ⊆ S :=
iff.intro
  (λ h t y ⟨_, hx, hy⟩, hy ▸ h t _ hx)
  (λ h t x hx, (@image_subset_iff _ _ _ _ (ϕ t)).mp (h t) hx)

variable [topological_space X]

lemma is_invariant_closure (hϕ : ∀ t, continuous (ϕ t)) (hS : is_invariant ϕ S) :
  is_invariant ϕ (closure S) :=
λ t, calc closure S ⊆ closure (ϕ t ⁻¹' S) : closure_mono (hS _)
     ...            ⊆ ϕ t ⁻¹' (closure S) : closure_minimal (preimage_mono subset_closure)
                                            (is_closed.preimage (hϕ _) is_closed_closure)

end is_invariant

/-! ### ω-limits -/

-- we define ω-limits of sets `S ⊆ X` under `ϕ : T → X → Y` with
-- reference a filter `f` on `T`. An element `y ∈ Y` is in the ω-limit
-- of `S` if the forward images of `S` intersect arbitrarily small
-- neighbourhoods of `y` frequently "in the direction of `f`".

-- In the case where `T` is `ℕ` or `ℝ` and `f` is `at_top`, we recover the usual
-- definition of the ω-limit set as the set of all `y ∈ Y` such that
-- there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y` as `n ⟶ ∞`.

-- in practice `ϕ` is often a flow on `X`, but the definitions make
-- sense so long as `ϕ` has a coercion to the appropriate function
-- type.

section omega_limit

/-- the ω-limit of `S ⊆ X` under `ϕ : T → X → Y` w.r.t. a filter `f`
    on `T` is defined as `⋂ u ∈ f, cl (ϕ u S)`.  -/
def omega_limit [topological_space Y]
  (f : filter T) (ϕ : T → X → Y) (S : set X) : set Y :=
⋂ n ∈ f, closure (image2 ϕ n S)

localized "notation `ω` := omega_limit" in omega_limit

variables [topological_space Y]
variables (m : T → T) (f f₁ f₂: filter T)

section -- omega limits under ϕ : T → X → Y

variables (ϕ : T → X → Y) (S S₁ S₂: set X)

lemma omega_limit_def : ω f ϕ S = ⋂ n ∈ f, closure (image2 ϕ n S) := rfl

lemma mem_omega_limit_iff_frequently (y : Y) :
  y ∈ ω f ϕ S ↔ ∀ v ∈ nhds y, ∃ᶠ t in f, (S ∩ ϕ t ⁻¹' v).nonempty :=
begin
  simp_rw frequently_iff,
  split,
  { intros h _ hv _ hu,
    simp_rw [omega_limit_def, mem_Inter] at h,
    rcases mem_closure_iff_nhds.mp (h _ hu) _ hv with
      ⟨ϕtx, hxv, t, x, ht, hx, hϕtx⟩,
    exact ⟨_, ht, _, hx, show ϕ t x ∈ v, by rwa hϕtx⟩ },
  { rintro h _ ⟨_, hc⟩,
    rw [←hc, mem_Inter],
    intro hu,
    rw mem_closure_iff_nhds,
    intros _ hv,
    rcases h _ hv hu with ⟨t, ht, x, hx, hϕtx⟩,
    exact ⟨ϕ t x, hϕtx, _, _, ht, hx, rfl⟩ }
end

lemma mem_omega_limit_singleton_iff_frequently (x : X) (y : Y) :
  y ∈ ω f ϕ {x} ↔ ∀ v ∈ nhds y, ∃ᶠ t in f, ϕ t x ∈ v :=
have l : ∀ t x v, ϕ t x ∈ v ↔ ({x} ∩ ϕ t ⁻¹' v).nonempty, from
 λ _ _ _, iff.intro (λ h, ⟨_, mem_singleton _, h⟩) (λ ⟨_, hx, h⟩, eq_of_mem_singleton hx ▸ h),
by simp_rw [mem_omega_limit_iff_frequently, l]

lemma is_closed_omega_limit : is_closed (ω f ϕ S) :=
is_closed_Inter (λ _, is_closed_Inter (λ _, is_closed_closure))

lemma omega_limit_subset_of_tendsto (h : tendsto m f₁ f₂) :
  ω f₁ (λ t x, ϕ (m t) x) S ⊆ ω f₂ ϕ S :=
begin
  apply Inter_subset_Inter2, intro u₂,  use m ⁻¹' u₂,
  apply Inter_subset_Inter2, intro hu₁, use h hu₁,
  apply closure_mono,
  rw ←image2_image_left,
  exact image2_subset (image_preimage_subset _ _) subset.rfl,
end

lemma omega_limit_mono (hf : f₁ ≤ f₂) (hS : S₁ ⊆ S₂) : ω f₁ ϕ S₁ ⊆ ω f₂ ϕ S₂ :=
begin
  apply Inter_subset_Inter2, intro u,  use u,
  apply Inter_subset_Inter2, intro hu, use hf hu,
  exact closure_mono (image2_subset subset.rfl hS),
end

-- ω-limits in compact spaces: choose to require a `compact_space`
-- instance rather than include an additional hypothesis for e.g. the
-- orbits being precompact; with the expectation that we proceed by
-- finding a compact invariant set and work in the subtype.

lemma is_compact_omega_limit [compact_space Y] : is_compact (ω f ϕ S) :=
(is_closed_omega_limit _ _ _).compact

/-- in a compact space, a set is eventually carried into any
    neighbourhood of its ω-limit.  -/
lemma eventually_subset_nhd_omega_limit [compact_space Y]
  (v : set Y) (ho : is_open v) (hv : ω f ϕ S ⊆ v) :
  ∃ u ∈ f, image2 ϕ u S ⊆ v :=
begin
  let j := λ u, (closure (image2 ϕ u S))ᶜ,
  have hj₁ : ∀ u ∈ f.sets, is_open (j u),
    from λ _ _, is_open_compl_iff.mpr is_closed_closure,
  have hj₂ : vᶜ ⊆ ⋃ u ∈ f, j u, begin
    rw [compl_subset_comm, compl_Union], simp_rw compl_Union,
    calc (⋂ u ∈ f, (closure (image2 ϕ u S))ᶜᶜ)
        ⊆ ⋂ u ∈ f, closure (image2 ϕ u S) :
          by { simp_rw compl_compl', exact subset.rfl }
    ... ⊆ v : hv,
  end,
  have h : is_compact vᶜ, from (is_closed_compl_iff.mpr ho).compact,
  rcases h.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁, hg₂, hg₃⟩,
  let w := ⋂₀ g,
  have hw₁ : w ∈ f, from sInter_mem_sets_of_finite hg₂ hg₁,
  have hw₂ : image2 ϕ w S ⊆ v, begin
    rw [compl_subset_comm, compl_Union] at hg₃,
    simp_rw compl_Union at hg₃,
    calc image2 ϕ w S
        ⊆ ⋂ u ∈ g, image2 ϕ u S :
          subset_Inter (λ _, subset_Inter (λ hu,
            image2_subset (sInter_subset_of_mem hu) subset.rfl))
    ... ⊆ ⋂ u ∈ g, (closure (image2 ϕ u S))ᶜᶜ :
          Inter_subset_Inter (λ u, Inter_subset_Inter (λ hu,
            by { rw compl_compl', exact subset_closure }))
    ... ⊆ v : hg₃,
  end,
  exact ⟨w, hw₁, hw₂⟩,
end

end

section -- omega limits under ϕ : T → Y → Y

variables (ϕ : T → Y → Y) (S : set Y)

lemma omega_limit_subset_closure (h : is_invariant ϕ S) : ω f ϕ S ⊆ closure S :=
Inter_subset_of_subset univ (Inter_subset_of_subset univ_mem_sets (closure_mono
  ((is_invariant_iff_image2_subset _ _).mp h)))

end

end omega_limit

/-! ### attractors -/
section attractor

open_locale omega_limit

/-- a set `A ⊆ X` is an attractor for `ϕ` w.r.t a filter `f` if it has
    a neighbourhood of which it is the ω-limit. -/
def is_attractor [topological_space X]
  (f : filter T) (ϕ : T → X → X) (A : set X) : Prop :=
∃ u, is_open u ∧ A ⊆ u ∧ ω f ϕ u = A

--variables [topological_space X] (f : filter T) (ϕ : T → X → X) (A : set X)

-- (work in progress.)

end attractor

end

/-! ### semigroup flows -/

-- a semigroup-flow on a topological space `X` by a topological
-- semigroup `T` is a continuous semigroup-act of `T` on
-- `X`. anticipating the cases `T = ℕ` or `ℝ`, we use additive
-- notation. Furthermore, since we expect to consider families of
-- flows, we do not register semigroup_flow as a class (as opposed to
-- `add_action` from `algebra/add_torsor`, which also implements
-- additive actions.)

section

/-- a semigroup-flow on a topological space `X` by an (additive)
    topological semigroup `T` is a continuous semigroup-act of `T` on
    `X`. -/
structure semigroup_flow
  (T : Type*) [topological_space T] [add_semigroup T] [has_continuous_add T]
  (X : Type*) [topological_space X] :=
(to_fun   : T → X → X)
(cont     : continuous ↿to_fun)
(map_add' : ∀ t₁ t₂ x, to_fun t₂ (to_fun t₁ x) = to_fun (t₁ + t₂) x)

namespace semigroup_flow

variables
{X : Type*} [topological_space X]
{T : Type*} [topological_space T] [add_semigroup T] [has_continuous_add T]

instance : has_coe_to_fun (semigroup_flow T X) := ⟨_, semigroup_flow.to_fun⟩
instance has_uncurry_semigroup_flow : has_uncurry (semigroup_flow T X) (T × X) X :=
⟨λ f p, f.to_fun p.fst p.snd⟩

@[ext]
lemma ext : ∀ {ϕ₁ ϕ₂ : semigroup_flow T X}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _, _⟩ ⟨f₂, _, _⟩ h := by { congr, funext, apply h }

lemma ext_iff {ϕ₁ ϕ₂ : semigroup_flow T X} : ϕ₁ = ϕ₂ ↔ (∀ x t, ϕ₁ x t = ϕ₂ x t) :=
⟨λ h _ _, by rw h, ext⟩

variables (f : filter T) (ϕ : semigroup_flow T X) (A S : set X)

@[continuity]
protected lemma continuous : continuous ↿ϕ := ϕ.cont

@[simp]
lemma map_add (t₁ t₂ : T) (x : X) : ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x := ϕ.map_add' _ _ _

open_locale omega_limit

/-- if `f` tends to itself under the (right-) action of `T` on itself,
    an ω-limit w.r.t. an invariant `f` is invariant. -/
lemma is_invariant_omega_limit (h : ∀ t, tendsto (+ t) f f) : is_invariant ϕ (ω f ϕ S) :=
begin
  unfold omega_limit,
  simp_rw [is_invariant_iff_subset_preimage, preimage_Inter],
  intro t,
  apply Inter_subset_Inter2, intro u,  use (+ t) ⁻¹' u,
  apply Inter_subset_Inter2, intro hu, use tendsto_def.mp (h t) _ hu,
  calc closure (image2 ϕ ((+ t) ⁻¹' u) S)
    ⊆ closure (ϕ t ⁻¹' image2 ϕ u S) :
    begin
      apply closure_mono,
      simp_rw [←image_subset_iff, image_image2, map_add],
      rw ←image2_image_left,
      exact image2_subset (image_preimage_subset _ _) subset.rfl,
    end
... ⊆ ϕ t ⁻¹' closure (image2 ϕ u S) :
    closure_minimal (preimage_mono subset_closure)
      (continuous_iff_is_closed.mp
        (continuous_uncurry_left _ _ ϕ.continuous) _ is_closed_closure),
end

end semigroup_flow

/-- a flow on a topological space X by a topological (additive) group
    T is a continuous group a action of T on X. -/
structure flow
  (T : Type*) [topological_space T] [add_group T] [topological_add_group T]
  (X : Type*) [topological_space X] extends semigroup_flow T X :=
(map_zero' : ∀ x, to_fun 0 x =  x)

namespace flow

open_locale omega_limit
open semigroup_flow

variables
{X : Type*} [topological_space X]
{T : Type*} [topological_space T]

section

variables [add_group T] [topological_add_group T]

instance : has_coe (flow T X) (semigroup_flow T X) := ⟨flow.to_semigroup_flow⟩
instance : has_coe_to_fun (flow T X) := ⟨_, λ ϕ, ϕ.to_semigroup_flow.to_fun⟩

instance has_uncurry_flow : has_uncurry (flow T X) (T × X) X := ⟨λ ϕ, ↿(ϕ : semigroup_flow T X)⟩

@[ext] lemma ext : ∀ {ϕ₁ ϕ₂ : flow T X}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _⟩ ⟨f₂, _⟩ h := by { congr, apply semigroup_flow.ext, apply h }

variable (ϕ : flow T X)

@[simp]
lemma coe_coe : ⇑(ϕ : semigroup_flow T X) = ⇑ϕ := rfl

@[continuity]
protected lemma continuous : continuous ↿ϕ := ϕ.cont

@[simp]
lemma map_add (t₁ t₂ : T) (x : X) : ϕ t₂ (ϕ t₁ x) = ϕ (t₁ + t₂) x := ϕ.map_add' _ _ _

@[simp]
lemma map_zero (x : X) : ϕ 0 x = x := ϕ.map_zero' _

end

section

variables [add_comm_group T] [topological_add_group T]
variables (f f₁ f₂ : filter T) (ϕ : flow T X) (A S : set X)

/-- the time-reversal of a flow, defined `ϕ.reverse t x = ϕ (-t) x` -/
def reverse : (flow T X) :=
{ to_fun    := λ t x, ϕ (-t) x,
  cont      := show continuous (↿ϕ ∘ λ p : T × X, (-p.fst, p.snd)), from
               ϕ.continuous.comp (by continuity),
  map_add'  := λ s t _, by rw [map_add, neg_add],
  map_zero' := λ _, show ϕ (-0) _ = _, by rw [neg_zero, map_zero] }

-- (it might be convenient to register `ϕ.reverse` as `has_inv` or
-- `has_neg` so that there is access to the notation `ϕ⁻¹` or `-ϕ`,
-- but lean might try to coerce to a function first and then complain
-- about not being able to find the appropriate instances.)

-- also, the following lemmas are either redundant or need more descriptive names:
lemma reverse_def (t : T) (x : X) : ϕ.reverse t x = ϕ (-t) x := rfl
lemma reverse_def₁ (t : T) : ϕ.reverse t = ϕ (-t) := funext (λ x, reverse_def _ _ _)
lemma reverse_def₂ : ⇑ϕ.reverse = λ t x, ϕ (-t) x := rfl

@[simp] lemma reverse_twice : ϕ.reverse.reverse = ϕ :=
ext (λ _ _, by simp only [reverse_def, neg_neg])

lemma image2_reverse_eq (I : set T) (S : set X):
  image2 ϕ.reverse I S = image2 ϕ (has_neg.neg '' I) S :=
by simp_rw [image2_image_left, ←reverse_def₁]

-- TODO: the statements/proofs/names of the following few results are
-- ugly and likely should be refactored into nicer versions of
-- themselves, once it is figured out what those are.

lemma tendsto_add_iff_tendsto_sub :
  (∀ t, tendsto (+ t) f₁ f₂) ↔ ∀ t, tendsto (λ x, x - t) f₁ f₂ :=
iff.intro (λ h t, h (-t)) (λ h t, by { simp_rw ←sub_neg_eq_add, exact h (-t) })

lemma omega_limit_forward_image (h : ∀ t, tendsto (+ t) f f) (t : T) :
  ω f ϕ S = ω f ϕ (ϕ t '' S) :=
begin
  rw subset.antisymm_iff, split,
  { calc ω f ϕ S
        ⊆ ω f (λ s x, ϕ (s - t) x) (ϕ t '' S) :
          begin
            apply Inter_subset_Inter, intro u,
            apply Inter_subset_Inter, intro hu,
            apply closure_mono,
            rw image2_image_right, simp
          end
    ... ⊆ ω f ϕ (ϕ t '' S) :
          omega_limit_subset_of_tendsto _ _ _ _ (ϕ t '' S)
            ((tendsto_add_iff_tendsto_sub _ _).mp h _) },
  { apply Inter_subset_Inter2, intro u, use (+ t) ⁻¹' u,
    apply Inter_subset_Inter2, intro hu, use tendsto_def.mp (h t) _ hu,
    apply closure_mono,
    simp_rw [image2_image_right, map_add],
    rintro y ⟨s, x, hs, hx, hsx⟩,
    exact ⟨s + t, x, hs, hx, by rwa add_comm⟩ }
end

lemma attractor_maximal (x : X) (h : ∀ t, tendsto (+ t) f f)
  (ha : is_attractor f ϕ A) (hs : A ⊆ S) (he : (ω f ϕ {x} ∩ A).nonempty) :
  ω f ϕ {x} ⊆ A :=
begin
  rcases ha with ⟨n, hn₁, hn₂, hn₃⟩, rw ←hn₃,
  rcases he with ⟨y, hy₁, hy₂⟩,
  rw mem_omega_limit_singleton_iff_frequently at hy₁,
  rcases (hy₁ _ (mem_nhds_sets hn₁ (hn₂ hy₂))).exists with ⟨t, ht⟩,
  calc ω f ϕ {x}
      ⊆ ω f ϕ (ϕ t '' {x}) :
        by { rw omega_limit_forward_image _ _ _ h t, exact subset.rfl, }
  ... ⊆ ω f ϕ {ϕ t x} :
        by { rw image_singleton, exact subset.rfl }
  ... ⊆ ω f ϕ n : omega_limit_mono _ _ _ _ _ le_rfl (singleton_subset_iff.mpr ht),
end

end

section

-- recover some results for ω- and α-limit sets in the case where `T = ℕ or ℝ`:
variables [decidable_linear_ordered_add_comm_group T] [topological_add_group T]

variables (ϕ : flow T X)

localized "notation `ω₊` := omega_limit at_top" in omega_limit
localized "notation `ω₋` := omega_limit at_bot" in omega_limit

variable (S : set X)

-- recover the usual definition of ω-limit sets as the intersection of
-- the closures of forward orbits.
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

-- the α-limit set is the ω limit set under time-reversal.
lemma omega_limit_at_top_reverse : ω₋ ϕ S = ω₊ ϕ.reverse S :=
begin
  have l₁, from omega_limit_subset_of_tendsto _ _ _ ϕ.reverse S tendsto_neg_at_bot_at_top,
  have l₂, from omega_limit_subset_of_tendsto _ _ _ ϕ S tendsto_neg_at_top_at_bot,
  rw [←reverse_def₂, reverse_twice] at l₁,
  exact subset.antisymm l₁ l₂,
end

lemma omega_limit_at_bot_reverse : ω₋ ϕ.reverse S = ω₊ ϕ S :=
begin
  have l₁, from omega_limit_subset_of_tendsto _ _ _ ϕ S tendsto_neg_at_bot_at_top,
  have l₂, from omega_limit_subset_of_tendsto _ _ _ ϕ.reverse S tendsto_neg_at_top_at_bot,
  rw [←reverse_def₂, reverse_twice] at l₂,
  exact subset.antisymm l₁ l₂,
end

end

end flow

end
