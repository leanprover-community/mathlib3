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

open set function

/-- a flow is a continuous action of a (topological, additive) monoid
    on a topological space. -/

-- this is probably not an ideal definition of generality reasons: we
-- usually also care about flows defined on some subset U ⊆ X × T, and
-- may want stronger/weaker hypotheses on e.g. differentiability.
--
-- The intended content for the remainder of this file are We later
-- require T to be an ordered_add_comm_group in addition to an a
-- add_monoid, so that it is possible to make statements about
-- e.g. ω-limit sets. The expectation is that T is usually either ℕ or
-- ℝ.

structure flow
  (X : Type*) [topological_space X]
  (T : Type*) [add_monoid T] [topological_space T] [has_continuous_add T]:=
(to_fun    : X → T → X)
(cont'     : continuous ↿to_fun)
(map_zero' : ∀ x, to_fun x 0 = x)
(map_add'  : ∀ x t₁ t₂, to_fun (to_fun x t₁) t₂ = to_fun x (t₁ + t₂))

section

variables {X : Type*} [topological_space X]
variables {T : Type*} [topological_space T] [ordered_add_comm_group T] [topological_add_group T]
variables (ϕ : flow X T) (S : set X)

local notation `T₊` := Ici (0 : T)
local notation `T₋` := Iic (0 : T)

noncomputable theory

instance : has_coe_to_fun (flow X T) := ⟨λ _, _, flow.to_fun⟩
instance has_uncurry_flow : has_uncurry (flow X T) (X × T) X := ⟨λ f p, f.to_fun p.1 p.2⟩

namespace flow

@[continuity]
lemma cont : continuous ↿ϕ := ϕ.cont'

@[simp]
lemma map_zero (x : X) : ϕ x 0 = x := ϕ.map_zero' _

@[simp]
lemma map_add (x : X) (t₁ t₂ : T) : ϕ (ϕ x t₁) t₂ = ϕ x (t₁ + t₂) := ϕ.map_add' _ _ _

/-- two flows are the same if they are the same as functions. -/
@[ext]
lemma ext : ∀ {ϕ₁ ϕ₂ : flow X T}, (∀ x t, ϕ₁ x t = ϕ₂ x t) → ϕ₁ = ϕ₂
| ⟨f₁, _, _, _⟩ ⟨f₂, _, _, _⟩ h := by { congr, funext, apply h }

/-- time-reversal of a flow: ϕ.reverse x t = ϕ x (-t). -/
def reverse : flow X T :=
{ to_fun    := λ x t, ϕ x (-t),
  cont'     := show continuous $ ↿ϕ ∘ λ p : X × T, (p.fst, -p.snd),
               from ϕ.cont.comp (by continuity),
  map_zero' := λ _, by rw [neg_zero, map_zero],
  map_add'  := λ _ _ _, by rw [neg_add, map_add] }

lemma reverse_def (x : X) (t : T) : ϕ.reverse x t = ϕ x (-t) := rfl

lemma reverse_image2 (I : set T) : image2 ϕ.reverse S I = image2 ϕ S ((λ t, -t) '' I) :=
subset.antisymm
  (λ _ ⟨_, _, hx, ht, hxt⟩, ⟨_, _, hx, ⟨_, ht, rfl⟩, by rw [←hxt, reverse_def]⟩)
  (λ _ ⟨_, _, hx, ⟨_, ht', htt'⟩, hxt⟩, ⟨_, _, hx, ht', by rw [←hxt, reverse_def, ←htt']⟩)

/-- reversing a flow twice yields the original flow. -/
@[simp] lemma reverse_twice : ϕ.reverse.reverse = ϕ :=
ext (λ x t, show ϕ x (- -t) = ϕ x t, by rw neg_neg)

/-! ### positively/negatively invariant sets -/

-- the nonnegativity hypothesis seems to force the for-all to look
-- like one of:
--
-- ∀ (x ∈ S) (t ≥ 0), ...
-- ∀ (x ∈ S) (t) (ht : 0 ≤ t), ...
-- ∀ x t, x ∈ S → 0 ≤ t → ...
-- ∀ {x t}, x ∈ S → 0 ≤ t → ...
--
-- none of these seem ideal. combing mathlib in an attempt to identify
-- an established convention led me to the beginning of
-- `data/set/lattice.lean`, where a comment reads:
--
--   QUESTION: can make the first argument in ∀ x ∈ a, ... implicit?
--
-- has there since been an answer to this question?

/-- a set S is positively invariant under ϕ if ϕ x t ∈ S for all x ∈ S, t ≥ 0. -/
def pos_invariant : Prop := ∀ (x ∈ S) (t) (ht : 0 ≤ t), ϕ x t ∈ S

/-- a set S is negatively invariant under ϕ iff it is positively invariant under
    time-reversed ϕ. -/
def neg_invariant : Prop := pos_invariant ϕ.reverse S

/-- a set is invariant if ϕ S t = S for all t. -/
def invariant : Prop := ∀ (x ∈ S) t, ϕ x t ∈ S

-- some equivalent characterisations of positive & negative invariance.
--
-- there are a few slightly-different ways sources state these
-- definitions, and all of the equivalences here are entirely
-- straightforward. Most of the proofs amount to destructing the
-- hypotheses and putting them back together in a different order ---
-- which maybe suggests it would be excessive to have /all/ of them in
-- mathlib.

lemma neg_invariant_iff_reverse : neg_invariant ϕ S ↔ pos_invariant ϕ.reverse S :=
iff.rfl

lemma neg_invariant_iff : neg_invariant ϕ S ↔ ∀ (x ∈ S) (t ≤ 0), ϕ x t ∈ S :=
begin
  rw neg_invariant_iff_reverse,
  split,
  all_goals { intros h _ hx _ ht },
  { rw ←neg_nonneg at ht,
    exact reverse_twice ϕ ▸ h _ hx _ ht },
  { rw ←neg_nonpos at ht,
    exact h _ hx _ ht },
end

/-- a set S is positively invariant under ϕ iff it is negatively invariant under
    time-reversed ϕ. -/
lemma pos_invariant_iff_reverse : pos_invariant ϕ S ↔ neg_invariant ϕ.reverse S :=
by conv_lhs { rw [←reverse_twice ϕ, ←neg_invariant_iff_reverse] }

/-- a set S is positively invariant under ϕ iff ϕ S T₊ ⊆ S. -/
lemma pos_invariant_iff_image2 : pos_invariant ϕ S ↔ image2 ϕ S T₊ ⊆ S :=
iff.intro
  (λ h _ ⟨_, _, hx, ht, hxt⟩, hxt ▸ h _ hx _ ht)
  (λ h _ hx _ ht, h ⟨_, _, hx, ht, rfl⟩)

/-- a set S is positively invariant under ϕ iff ϕ S t ⊆ S for all nonnegative t. -/
lemma pos_invariant_iff_image : pos_invariant ϕ S ↔ ∀ (t) (ht : 0 ≤ t), (λ x, ϕ x t) '' S ⊆ S :=
iff.intro
  (λ h _ ht _ ⟨_, hx, hxt⟩, hxt ▸ h _ hx _ ht)
  (λ h _ hx _ ht, h _ ht ⟨_, hx, rfl⟩)

/-- a set S is negatively invariant under ϕ iff ϕ S T₋ ⊆ S. -/
lemma neg_invariant_iff_image2 : neg_invariant ϕ S ↔ image2 ϕ S T₋ ⊆ S :=
by conv_rhs { rw [←reverse_twice ϕ, reverse_image2, image_neg_Iic, neg_zero,
                  ←pos_invariant_iff_image2, ←neg_invariant_iff_reverse ] }

/-- a set S is negatively invariant under ϕ iff ϕ S t ⊆ S for all nonnegative t. -/
lemma neg_invariant_iff_image : neg_invariant ϕ S ↔ ∀ (t) (ht : 0 ≤ t), S ⊆ (λ x, ϕ x t) '' S :=
begin
  split,
  { rintro h t ht x hx, use ϕ x (-t), split,
    by { rw neg_invariant_iff at h, exact h _ hx _ (neg_nonpos.mpr ht) },
    show ϕ (ϕ x (-t)) t = x, by rw [map_add, neg_add_self, map_zero] },
  { intros h ϕxt hϕxt _ ht,
    rw reverse_def,
    rcases h _ ht hϕxt with ⟨_, hx, hxt⟩,
    rwa [←hxt, map_add, add_neg_self, map_zero] }
end

/-- a set is invariant iff it is both positively and negatively invariant. -/
lemma invariant_iff : invariant ϕ S ↔ pos_invariant ϕ S ∧ neg_invariant ϕ S :=
begin
  rw [neg_invariant_iff_image2, pos_invariant_iff_image2],
  sorry
end

lemma invariant_reverse : invariant ϕ S ↔ invariant ϕ.reverse S :=
begin
  unfold invariant,
  simp_rw [reverse_def],
  split,
  { intros h x hx t, exact h _ hx _ },
  { intros h x hx t, exact neg_neg t ▸ h _ hx (-t) }
end

/-- a flow on X induces a flow on a ϕ-invariant set S ⊆ X. -/
def restrict (h : invariant ϕ S) : flow ↥S T :=
{ to_fun    := λ x t, ⟨ϕ x.val t, h _ x.prop _⟩,
  cont'     := sorry,
  map_zero' := λ ⟨_, _⟩, subtype.ext (ϕ.map_zero _),
  map_add'  := λ ⟨_, _⟩ _ _, subtype.ext (ϕ.map_add _ _ _),
}

/-- the invariant sets under a flow form a boolean lattice. -/

-- TODO: fill out the rest of the fields.
instance : bounded_lattice (subtype (invariant ϕ)) := {
  -- partial order
  le           := λ S₁ S₂, (S₁ : set X) ⊆ S₂,
  le_refl      := λ _, subset.rfl,
  le_trans     := λ _ _ _, subset.trans,
  le_antisymm  := λ _ _ h₁ h₂, subtype.ext (subset.antisymm h₁ h₂),
  -- lattice
  inf          := λ S₁ S₂, ⟨S₁ ∩ S₂, λ _ ⟨hx₁, hx₂⟩ _, ⟨S₁.prop _ hx₁ _, S₂.prop _ hx₂ _⟩⟩,
  le_inf       := λ _ _ _ h₁ h₂, subset_inter h₁ h₂,
  inf_le_left  := λ _ _, inter_subset_left _ _,
  inf_le_right := λ _ _, inter_subset_right _ _,
  sup          := λ S₁ S₂, ⟨S₁ ∪ S₂, λ x hx t, or.elim hx
                    (λ h, subset_union_left  _ _ $ S₁.prop _ h _)
                    (λ h, subset_union_right _ _ $ S₂.prop _ h _)⟩,
  sup_le       := λ _ _ _ h₁ h₂, union_subset h₁ h₂,
  le_sup_left  := λ _ _, subset_union_left _ _,
  le_sup_right := λ _ _, subset_union_right _ _,
  -- bounded
  top          := ⟨univ, λ _ _ _, mem_univ _⟩,
  le_top       := λ _, subset_univ _,
  bot          := ⟨∅, λ x h _, false.elim $ mem_empty_eq x ▸ h⟩,
  bot_le       := λ _, empty_subset _,
}

/-! ### ω-limits of subsets -/

/-- the ω-limit set of S under ϕ is the intersection of
    the closures of all the forward orbits of S:
    ω(ϕ, S) = ⋂ t, cl (ϕ S [t, ∞)). -/
def omega_limit : set X := ⋂ t, closure (image2 ϕ S (Ici t))

/-- the α-limit set of S under ϕ is its ω-limit set under the time
    reversal of ϕ. -/
def alpha_limit : set X := omega_limit ϕ.reverse S

/-- the ω-limit set of S under ϕ are invariant under ϕ. -/
lemma invariant_omega_limit : invariant ϕ (omega_limit ϕ S) :=
begin
  intros x hx t₁,
  rintro cϕt₂ ⟨t₂, hcϕt₂⟩, rw ←hcϕt₂,

  -- TODO : there is surely a more concise proof of this:
  have l₁, from
  calc ϕ x t₁ ∈ (λ x, ϕ x t₁) '' omega_limit ϕ S : mem_image_of_mem _ hx
  ...         ⊆ ⋂ t, (λ x, ϕ x t₁) '' closure (image2 ϕ S (Ici t))
  : image_Inter_subset _ _
  ...         ⊆ (λ x, ϕ x t₁) '' closure (image2 ϕ S (Ici (t₂ - t₁)))
  : by { intros x hx, rw mem_Inter at hx, apply hx }
  ...         ⊆ closure ((λ x, ϕ x t₁) '' image2 ϕ S (Ici (t₂ - t₁)))
  : image_closure_subset_closure_image (continuous_uncurry_right _ _ ϕ.cont),

  -- ... and also this part feels like it has a version worth extracting as a lemma:
  have l₂ : (λ x, ϕ x t₁) '' image2 ϕ S (Ici (t₂ - t₁)) ⊆ image2 ϕ S (Ici t₂), from
  begin
    rintro ϕxt₂ ⟨x₂, ⟨x₁, t, hx₁, ht, hx₂⟩, hϕxt₁⟩,
    rw [←hϕxt₁, ←hx₂],
    show ϕ (ϕ x₁ t) t₁ ∈ image2 ϕ S (Ici t₂),
    rw ϕ.map_add,
    have : t + t₁ ∈ Ici t₂, by { rw mem_Ici at ht, rw mem_Ici,
                                 exact le_add_of_sub_right_le ht, },
    exact ⟨_, _, hx₁, this, rfl⟩,
  end,

  exact (closure_mono l₂) l₁,
end

/-- the α-limit set of S under ϕ is invariant under ϕ. -/
lemma invariant_alpha_limit : invariant ϕ (alpha_limit ϕ S) :=
by { rw invariant_reverse, apply invariant_omega_limit }

/-- ω-limit sets are closed. -/
lemma is_closed_omega_limit : is_closed (omega_limit ϕ S) :=
is_closed_Inter $ λ i, is_closed_closure

lemma is_compact_omega_limit [compact_space X] : is_compact (omega_limit ϕ S) :=
sorry

-- miscellaneous properties of ω-limits:

/-- for U ⊆ V ⊆ X, ω (ϕ, U) ⊆ ω (ϕ, V). -/
lemma omega_limit_mono {U V : set X} (h : U ⊆ V) : omega_limit ϕ U ⊆ omega_limit ϕ V :=
Inter_subset_Inter $ λ t, closure_mono $ image2_subset h subset.rfl

/-! ### trapping regions, attractors, repellers -/

-- (work in progress.)

end flow

end
