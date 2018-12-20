/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Extended metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

This file is devoted to the definition and study of `emetric_spaces`, i.e., metric
spaces in which the distance is allowed to take the value ∞. This extended distance is
called `edist`, and takes values in `ennreal`.

Many definitions and theorems expected on emetric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity

The class `emetric_space` therefore extends `uniform_space` (and `topological_space`).
-/

import data.real.nnreal data.real.ennreal analysis.topology.topological_structures
open lattice set filter classical
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/--Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity.-/
theorem uniformity_dist_of_mem_uniformity [linear_order β] {U : filter (α × α)} (z : β) (D : α → α → β)
  (H : ∀ s, s ∈ U.sets ↔ ∃ε>z, ∀{a b:α}, D a b < ε → (a, b) ∈ s) :
  U = ⨅ ε>z, principal {p:α×α | D p.1 p.2 < ε} :=
le_antisymm
  (le_infi $ λ ε, le_infi $ λ ε0, le_principal_iff.2 $ (H _).2 ⟨ε, ε0, λ a b, id⟩)
  (λ r ur, let ⟨ε, ε0, h⟩ := (H _).1 ur in
    mem_infi_sets ε $ mem_infi_sets ε0 $ mem_principal_sets.2 $ λ ⟨a, b⟩, h)

/-Design note: one could define an `emetric_space` just by giving `edist`, and then
derive an instance of `uniform_space` by taking the natural uniform structure
associated to the distance. This creates diamonds problem for products, as the
uniform structure on the product of two emetric spaces could be obtained first
by obtaining two uniform spaces and then taking their products, or by taking
the product of the emetric spaces and then the associated uniform structure.
The two uniform structure we have just described are equal, but not defeq, which
creates a lot of problem.

The idea is to add, in the very definition of an `emetric_space`, a uniform structure
with a uniformity which equal to the one given by the distance, but maybe not defeq.
And the instance from `emetric_space` to `uniform_space` uses this uniformity.
In this way, when we create the product of emetric spaces, we put in the product
the uniformity corresponding to the product of the uniformities. There is one more
proof obligation, that this product uniformity is equal to the uniformity corresponding
to the product metric. But the diamond problem disappears.

The same trick is used in the definition of a metric space, where one stores as well
a uniform structure and an edistance.
 -/

/--Creating a uniform space from an extended distance.-/
def emetric_space.uniform_space_of_edist
  (edist : α → α → ennreal)
  (edist_self : ∀ x : α, edist x x = 0)
  (edist_comm : ∀ x y : α, edist x y = edist y x)
  (edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z) : uniform_space α :=
uniform_space.of_core {
  uniformity := (⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε}),
  refl       := le_infi $ assume ε, le_infi $
    by simp [set.subset_def, id_rel, edist_self, (>)] {contextual := tt},
  comp       :=
    le_infi $ assume ε, le_infi $ assume h,
    have (2 : ennreal) = (2 : ℕ) := by simp,
    have A : 0 < ε / 2 := ennreal.div_pos_iff.2 ⟨ne_of_gt h, this ▸ ennreal.nat_ne_top 2⟩,
    lift'_le
    (mem_infi_sets (ε / 2) $ mem_infi_sets A (subset.refl _)) $
    have ∀ (a b c : α), edist a c < ε / 2 → edist c b < ε / 2 → edist a b < ε,
      from assume a b c hac hcb,
      calc edist a b ≤ edist a c + edist c b : edist_triangle _ _ _
        ... < ε / 2 + ε / 2 : ennreal.add_lt_add hac hcb
        ... = ε : by rw [ennreal.add_halves],
    by simpa [comp_rel],
  symm       := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ by simp [edist_comm] }

/--Extended metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each emetric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating an `emetric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating an `emetric_space` structure
on a product.-/
class emetric_space (α : Type u) :=
(edist : α → α → ennreal)
(edist_self : ∀ x : α, edist x x = 0)
(eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y)
(edist_comm : ∀ x y : α, edist x y = edist y x)
(edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z)
(to_uniform_space : uniform_space α := emetric_space.uniform_space_of_edist edist edist_self edist_comm edist_triangle)
(uniformity_edist : uniformity = ⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε} . control_laws_tac)

/-emetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace.-/
namespace emetric_space
variables [emetric_space α]

instance emetric_space.to_uniform_space' : uniform_space α :=
emetric_space.to_uniform_space α

attribute [simp] edist_self

/--Characterize the equality of points by the vanishing of their extended distance-/
@[simp] theorem edist_eq_zero {x y : α} : edist x y = 0 ↔ x = y :=
iff.intro eq_of_edist_eq_zero (assume : x = y, this ▸ edist_self _)

@[simp] theorem zero_eq_edist {x y : α} : 0 = edist x y ↔ x = y :=
iff.intro (assume h, eq_of_edist_eq_zero (h.symm))
          (assume : x = y, this ▸ (edist_self _).symm)

/--Triangle inequality for the extended distance-/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y :=
by rw edist_comm z; apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z :=
by rw edist_comm y; apply edist_triangle

/--Reformulation of the uniform structure in terms of the extended distance-/
theorem uniformity_edist' : uniformity = (⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε}) :=
uniformity_edist _

/--Reformulation of the uniform structure in terms of the extended distance on a subtype-/
theorem uniformity_edist'' : uniformity = (⨅ε:{ε:ennreal // ε>0}, principal {p:α×α | edist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_edist'

/--Characterization of the elements of the uniformity in terms of the extended distance-/
theorem mem_uniformity_edist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s) :=
begin
  rw [uniformity_edist'', infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, ennreal.zero_lt_one⟩⟩
end

/--Fixed size neighborhoods of the diagonal belong to the uniform structure-/
theorem edist_mem_uniformity {ε:ennreal} (ε0 : 0 < ε) :
  {p:α×α | edist p.1 p.2 < ε} ∈ (@uniformity α _).sets :=
mem_uniformity_edist.2 ⟨ε, ε0, λ a b, id⟩

/-- ε-δ characterization of uniform continuity on emetric spaces-/
theorem uniform_continuous_of_emetric [emetric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, edist a b < δ → edist (f a) (f b) < ε :=
uniform_continuous_def.trans
⟨λ H ε ε0, mem_uniformity_edist.1 $ H _ $ edist_mem_uniformity ε0,
 λ H r ru,
  let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_uniformity_edist.2 ⟨δ, δ0, λ a b h, hε (hδ h)⟩⟩

/-- ε-δ characterization of uniform embeddings on emetric spaces-/
theorem uniform_embedding_of_emetric [emetric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (edist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_edist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, edist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

/-- ε-δ characterization of Cauchy sequences on emetric spaces-/
lemma cauchy_of_emetric {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f.sets, ∀ x y ∈ t, edist x y < ε :=
cauchy_iff.trans $ and_congr iff.rfl
⟨λ H ε ε0, let ⟨t, tf, ts⟩ := H _ (edist_mem_uniformity ε0) in
   ⟨t, tf, λ x y xt yt, @ts (x, y) ⟨xt, yt⟩⟩,
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, tf, h⟩ := H ε ε0 in
   ⟨t, tf, λ ⟨x, y⟩ ⟨hx, hy⟩, hε (h x y hx hy)⟩⟩

/--Two points coincide if their distance is `< ε` for all positive ε-/
theorem eq_of_forall_edist_le {x y : α} (h : ∀ε, ε > 0 → edist x y ≤ ε) : x = y :=
eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense (by simp) h)

/--An emetric space is separated-/
instance to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_edist_le $
λ ε ε0, le_of_lt (h _ (edist_mem_uniformity ε0))

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity.-/
def replace_uniformity {α} [U : uniform_space α] (m : emetric_space α)
  (H : @uniformity _ U = @uniformity _ (emetric_space.to_uniform_space α)) :
  emetric_space α :=
{ edist               := @edist _ m,
  edist_self          := edist_self,
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _,
  edist_comm          := edist_comm,
  edist_triangle      := edist_triangle,
  to_uniform_space    := U,
  uniformity_edist    := H.trans (@uniformity_edist α _) }

/--The extended metric induced by an injective function taking values in an emetric space.-/
def induced {α β} (f : α → β) (hf : function.injective f)
  (m : emetric_space β) : emetric_space α :=
{ edist               := λ x y, edist (f x) (f y),
  edist_self          := λ x, edist_self _,
  eq_of_edist_eq_zero := λ x y h, hf (edist_eq_zero.1 h),
  edist_comm          := λ x y, edist_comm _ _,
  edist_triangle      := λ x y z, edist_triangle _ _ _,
  to_uniform_space    := uniform_space.comap f m.to_uniform_space,
  uniformity_edist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, edist (f x) (f y)),
    refine λ s, mem_comap_sets.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases emetric_space.mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, emetric_space.edist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

/--Emetric space instance on subsets of emetric spaces-/
instance {p : α → Prop} [t : emetric_space α] : emetric_space (subtype p) :=
emetric_space.induced subtype.val (λ x y, subtype.eq) t

/--The extended distance on a subset of an emetric space is the restriction of
the original distance, by definition-/
theorem subtype.edist_eq {p : α → Prop} [t : emetric_space α] (x y : subtype p) :
  edist x y = edist x.1 y.1 := rfl

/--The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems.-/
instance prod.emetric_space_max [emetric_space β] : emetric_space (α × β) :=
{ edist := λ x y, max (edist x.1 y.1) (edist x.2 y.2),
  edist_self := λ x, by simp,
  eq_of_edist_eq_zero := λ x y h, begin
    cases max_le_iff.1 (le_of_eq h) with h₁ h₂,
    have A : x.fst = y.fst := eq_of_edist_eq_zero (by simpa using h₁),
    have B : x.snd = y.snd := eq_of_edist_eq_zero (by simpa using h₂),
    exact prod.ext_iff.2 ⟨A, B⟩
  end,
  edist_comm := λ x y, by simp [edist_comm],
  edist_triangle := λ x y z, max_le
    (le_trans (edist_triangle _ _ _) (add_le_add' (le_max_left _ _) (le_max_left _ _)))
    (le_trans (edist_triangle _ _ _) (add_le_add' (le_max_right _ _) (le_max_right _ _))),
  uniformity_edist := begin
    refine uniformity_prod.trans _,
    simp [uniformity_edist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

section pi
open finset
variables {π : β → Type*} [fintype β]

/--The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces.-/
instance emetric_space_pi [∀b, emetric_space (π b)] : emetric_space (Πb, π b) :=
{ edist := λ f g, finset.sup univ (λb, edist (f b) (g b)),
  edist_self := assume f, bot_unique $ finset.sup_le $ by simp,
  edist_comm := assume f g, by congr; funext a; exact edist_comm _ _,
  edist_triangle := assume f g h,
    begin
      simp only [finset.sup_le_iff],
      assume b hb,
      exact le_trans (edist_triangle _ (g b) _) (add_le_add' (le_sup hb) (le_sup hb))
    end,
  eq_of_edist_eq_zero := assume f g eq0,
    begin
      have eq1 : sup univ (λ (b : β), edist (f b) (g b)) ≤ 0 := le_of_eq eq0,
      simp only [finset.sup_le_iff] at eq1,
      exact (funext $ assume b, eq_of_edist_eq_zero $ bot_unique $ eq1 b $ mem_univ b),
    end }

end pi

end emetric_space