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

import data.real.nnreal data.real.ennreal
import topology.uniform_space.separation topology.uniform_space.uniform_embedding
open lattice set filter classical
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Characterizing uniformities associated to a (generalized) distance function `D`
in terms of the elements of the uniformity. -/
theorem uniformity_dist_of_mem_uniformity [linear_order β] {U : filter (α × α)} (z : β) (D : α → α → β)
  (H : ∀ s, s ∈ U.sets ↔ ∃ε>z, ∀{a b:α}, D a b < ε → (a, b) ∈ s) :
  U = ⨅ ε>z, principal {p:α×α | D p.1 p.2 < ε} :=
le_antisymm
  (le_infi $ λ ε, le_infi $ λ ε0, le_principal_iff.2 $ (H _).2 ⟨ε, ε0, λ a b, id⟩)
  (λ r ur, let ⟨ε, ε0, h⟩ := (H _).1 ur in
    mem_infi_sets ε $ mem_infi_sets ε0 $ mem_principal_sets.2 $ λ ⟨a, b⟩, h)

class has_edist (α : Type*) := (edist : α → α → ennreal)
export has_edist (edist)

/- Design note: one could define an `emetric_space` just by giving `edist`, and then
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
a uniform structure and an edistance. -/

/-- Creating a uniform space from an extended distance. -/
def uniform_space_of_edist
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

/-- Extended metric spaces, with an extended distance `edist` possibly taking the
value ∞

Each emetric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating an `emetric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. There is a default value for the uniformity, that can be substituted
in cases of interest, for instance when instantiating an `emetric_space` structure
on a product.

Continuity of `edist` is finally proving in `topology.instances.ennreal`
-/
class emetric_space (α : Type u) extends has_edist α : Type u :=
(edist_self : ∀ x : α, edist x x = 0)
(eq_of_edist_eq_zero : ∀ {x y : α}, edist x y = 0 → x = y)
(edist_comm : ∀ x y : α, edist x y = edist y x)
(edist_triangle : ∀ x y z : α, edist x z ≤ edist x y + edist y z)
(to_uniform_space : uniform_space α := uniform_space_of_edist edist edist_self edist_comm edist_triangle)
(uniformity_edist : uniformity = ⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε} . control_laws_tac)

/- emetric spaces are less common than metric spaces. Therefore, we work in a dedicated
namespace, while notions associated to metric spaces are mostly in the root namespace. -/
variables [emetric_space α]

instance emetric_space.to_uniform_space' : uniform_space α :=
emetric_space.to_uniform_space α

export emetric_space (edist_self eq_of_edist_eq_zero edist_comm edist_triangle)

attribute [simp] edist_self

/-- Characterize the equality of points by the vanishing of their extended distance -/
@[simp] theorem edist_eq_zero {x y : α} : edist x y = 0 ↔ x = y :=
iff.intro eq_of_edist_eq_zero (assume : x = y, this ▸ edist_self _)

@[simp] theorem zero_eq_edist {x y : α} : 0 = edist x y ↔ x = y :=
iff.intro (assume h, eq_of_edist_eq_zero (h.symm))
          (assume : x = y, this ▸ (edist_self _).symm)

/-- Triangle inequality for the extended distance -/
theorem edist_triangle_left (x y z : α) : edist x y ≤ edist z x + edist z y :=
by rw edist_comm z; apply edist_triangle

theorem edist_triangle_right (x y z : α) : edist x y ≤ edist x z + edist y z :=
by rw edist_comm y; apply edist_triangle

lemma edist_triangle4 (x y z t : α) :
  edist x t ≤ edist x y + edist y z + edist z t :=
calc
  edist x t ≤ edist x z + edist z t : edist_triangle x z t
... ≤ (edist x y + edist y z) + edist z t : add_le_add_right' (edist_triangle x y z)

/-- Two points coincide if their distance is `< ε` for all positive ε -/
theorem eq_of_forall_edist_le {x y : α} (h : ∀ε, ε > 0 → edist x y ≤ ε) : x = y :=
eq_of_edist_eq_zero (eq_of_le_of_forall_le_of_dense (by simp) h)

/-- Reformulation of the uniform structure in terms of the extended distance -/
theorem uniformity_edist' : uniformity = (⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε}) :=
emetric_space.uniformity_edist _

/-- Reformulation of the uniform structure in terms of the extended distance on a subtype -/
theorem uniformity_edist'' : uniformity = (⨅ε:{ε:ennreal // ε>0}, principal {p:α×α | edist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_edist'

theorem uniformity_edist_nnreal :
  uniformity = (⨅(ε:nnreal) (h : ε > 0), principal {p:α×α | edist p.1 p.2 < ε}) :=
begin
  rw [uniformity_edist', ennreal.infi_ennreal, inf_of_le_left],
  { congr, funext ε, refine infi_congr_Prop ennreal.coe_pos _, assume h, refl },
  refine le_infi (assume h, infi_le_of_le 1 $ infi_le_of_le ennreal.zero_lt_one $ _),
  exact principal_mono.2 (assume p h, lt_of_lt_of_le h le_top)
end

/-- Characterization of the elements of the uniformity in terms of the extended distance -/
theorem mem_uniformity_edist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s) :=
begin
  rw [uniformity_edist'', infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, ennreal.zero_lt_one⟩⟩
end

/-- Fixed size neighborhoods of the diagonal belong to the uniform structure -/
theorem edist_mem_uniformity {ε:ennreal} (ε0 : 0 < ε) :
  {p:α×α | edist p.1 p.2 < ε} ∈ (@uniformity α _).sets :=
mem_uniformity_edist.2 ⟨ε, ε0, λ a b, id⟩

namespace emetric

/-- ε-δ characterization of uniform continuity on emetric spaces -/
theorem uniform_continuous_iff [emetric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, edist a b < δ → edist (f a) (f b) < ε :=
uniform_continuous_def.trans
⟨λ H ε ε0, mem_uniformity_edist.1 $ H _ $ edist_mem_uniformity ε0,
 λ H r ru,
  let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_uniformity_edist.2 ⟨δ, δ0, λ a b h, hε (hδ h)⟩⟩

/-- ε-δ characterization of uniform embeddings on emetric spaces -/
theorem uniform_embedding_iff [emetric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (edist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_edist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, edist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

/-- ε-δ characterization of Cauchy sequences on emetric spaces -/
protected lemma cauchy_iff {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f.sets, ∀ x y ∈ t, edist x y < ε :=
cauchy_iff.trans $ and_congr iff.rfl
⟨λ H ε ε0, let ⟨t, tf, ts⟩ := H _ (edist_mem_uniformity ε0) in
   ⟨t, tf, λ x y xt yt, @ts (x, y) ⟨xt, yt⟩⟩,
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, tf, h⟩ := H ε ε0 in
   ⟨t, tf, λ ⟨x, y⟩ ⟨hx, hy⟩, hε (h x y hx hy)⟩⟩

end emetric

open emetric

/-- An emetric space is separated -/
instance to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_edist_le $
λ ε ε0, le_of_lt (h _ (edist_mem_uniformity ε0))

/-- Auxiliary function to replace the uniformity on an emetric space with
a uniformity which is equal to the original one, but maybe not defeq.
This is useful if one wants to construct an emetric space with a
specified uniformity. -/
def emetric_space.replace_uniformity {α} [U : uniform_space α] (m : emetric_space α)
  (H : @uniformity _ U = @uniformity _ (emetric_space.to_uniform_space α)) :
  emetric_space α :=
{ edist               := @edist _ m.to_has_edist,
  edist_self          := edist_self,
  eq_of_edist_eq_zero := @eq_of_edist_eq_zero _ _,
  edist_comm          := edist_comm,
  edist_triangle      := edist_triangle,
  to_uniform_space    := U,
  uniformity_edist    := H.trans (@emetric_space.uniformity_edist α _) }

/-- The extended metric induced by an injective function taking values in an emetric space. -/
def emetric_space.induced {α β} (f : α → β) (hf : function.injective f)
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
      rcases mem_uniformity_edist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, edist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

/-- Emetric space instance on subsets of emetric spaces -/
instance {p : α → Prop} [t : emetric_space α] : emetric_space (subtype p) :=
t.induced subtype.val (λ x y, subtype.eq)

/-- The extended distance on a subset of an emetric space is the restriction of
the original distance, by definition -/
theorem subtype.edist_eq {p : α → Prop} [t : emetric_space α] (x y : subtype p) :
  edist x y = edist x.1 y.1 := rfl

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
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
    simp [emetric_space.uniformity_edist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

section pi
open finset
variables {π : β → Type*} [fintype β]

/-- The product of a finite number of emetric spaces, with the max distance, is still
an emetric space.
This construction would also work for infinite products, but it would not give rise
to the product topology. Hence, we only formalize it in the good situation of finitely many
spaces. -/
instance emetric_space_pi [∀b, emetric_space (π b)] : emetric_space (Πb, π b) :=
{ edist := λ f g, finset.sup univ (λb, edist (f b) (g b)),
  edist_self := assume f, bot_unique $ finset.sup_le $ by simp,
  edist_comm := assume f g, by unfold edist; congr; funext a; exact edist_comm _ _,
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

namespace emetric
variables {x y z : α} {ε ε₁ ε₂ : ennreal} {s : set α}

/-- `emetric.ball x ε` is the set of all points `y` with `edist y x < ε` -/
def ball (x : α) (ε : ennreal) : set α := {y | edist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ edist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ edist x y < ε := by rw edist_comm; refl

/-- `emetric.closed_ball x ε` is the set of all points `y` with `edist y x ≤ ε` -/
def closed_ball (x : α) (ε : ennreal) := {y | edist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ edist y x ≤ ε := iff.rfl

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
assume y, by simp; intros h; apply le_of_lt h

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : 0 < ε :=
lt_of_le_of_lt (zero_le _) hy

theorem mem_ball_self (h : 0 < ε) : x ∈ ball x ε :=
show edist x x < ε, by rw edist_self; assumption

theorem mem_closed_ball_self : x ∈ closed_ball x ε :=
show edist x x ≤ ε, by rw edist_self; exact bot_le

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by simp [edist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

theorem closed_ball_subset_closed_ball (h : ε₁ ≤ ε₂) :
  closed_ball x ε₁ ⊆ closed_ball x ε₂ :=
λ y (yx : _ ≤ ε₁), le_trans yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ edist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ z ⟨h₁, h₂⟩,
not_lt_of_le (edist_triangle_left x y z)
  (lt_of_lt_of_le (ennreal.add_lt_add h₁ h₂) h)

theorem ball_subset (h : edist x y + ε₁ ≤ ε₂) (h' : edist x y < ⊤): ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, calc
  edist z y ≤ edist z x + edist x y : edist_triangle _ _ _
  ... = edist x y + edist z x : add_comm _ _
  ... < edist x y + ε₁ : (ennreal.add_lt_add_iff_left h').2 zx
  ... ≤ ε₂ : h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
begin
  have : 0 < ε - edist y x := by simpa using h,
  refine ⟨ε - edist y x, this, ball_subset _ _⟩,
  { rw ennreal.add_sub_cancel_of_le (le_of_lt h), apply le_refl _},
  { have : edist y x ≠ ⊤ := lattice.ne_top_of_lt h, apply lt_top_iff_ne_top.2 this }
end

theorem ball_eq_empty_iff : ball x ε = ∅ ↔ ε = 0 :=
eq_empty_iff_forall_not_mem.trans
⟨λh, le_bot_iff.1 (le_of_not_gt (λ ε0, h _ (mem_ball_self ε0))),
λε0 y h, not_lt_of_le (le_of_eq ε0) (pos_of_mem_ball h)⟩

theorem nhds_eq : nhds x = (⨅ε:{ε:ennreal // ε>0}, principal (ball x ε.val)) :=
begin
  rw [nhds_eq_uniformity, uniformity_edist'', lift'_infi],
  { apply congr_arg, funext ε,
    rw [lift'_principal],
    { simp [ball, edist_comm] },
    { exact monotone_preimage } },
  { exact ⟨⟨1, ennreal.zero_lt_one⟩⟩ },
  { intros, refl }
end

theorem mem_nhds_iff : s ∈ (nhds x).sets ↔ ∃ε>0, ball x ε ⊆ s :=
begin
  rw [nhds_eq, infi_sets_eq],
  { simp },
  { intros y z, cases y with y hy, cases z with z hz,
    refine ⟨⟨min y z, lt_min hy hz⟩, _⟩,
    simp [ball_subset_ball, min_le_left, min_le_right, (≥)] },
  { exact ⟨⟨1, ennreal.zero_lt_one⟩⟩ }
end

theorem is_open_iff : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp [is_open_iff_nhds, mem_nhds_iff]

theorem is_open_ball : is_open (ball x ε) :=
is_open_iff.2 $ λ y, exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ennreal} (ε0 : 0 < ε) : ball x ε ∈ (nhds x).sets :=
mem_nhds_sets is_open_ball (mem_ball_self ε0)

/-- ε-characterization of the closure in emetric spaces -/
theorem mem_closure_iff' :
  x ∈ closure s ↔ ∀ε>0, ∃y ∈ s, edist x y < ε :=
⟨begin
  intros hx ε hε,
  have A : ball x ε ∩ s ≠ ∅ := mem_closure_iff.1 hx _ is_open_ball (mem_ball_self hε),
  cases ne_empty_iff_exists_mem.1 A with y hy,
  simp,
  exact ⟨y, ⟨hy.2, by have B := hy.1; simpa [mem_ball'] using B⟩⟩
end,
begin
  intros H,
  apply mem_closure_iff.2,
  intros o ho xo,
  rcases is_open_iff.1 ho x xo with ⟨ε, ⟨εpos, hε⟩⟩,
  rcases H ε εpos with ⟨y, ⟨ys, ydist⟩⟩,
  have B : y ∈ o ∩ s := ⟨hε (by simpa [edist_comm]), ys⟩,
  apply ne_empty_of_mem B
end⟩

theorem tendsto_nhds {f : filter β} {u : β → α} {a : α} :
  tendsto u f (nhds a) ↔ ∀ ε > 0, ∃ n ∈ f.sets, ∀x ∈ n, edist (u x) a < ε :=
⟨λ H ε ε0, ⟨u⁻¹' (ball a ε), H (ball_mem_nhds _ ε0), by simp⟩,
 λ H s hs,
  let ⟨ε, ε0, hε⟩ := mem_nhds_iff.1 hs, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  f.sets_of_superset δ0 (λx xδ, hε (hδ x xδ))⟩

theorem tendsto_at_top [inhabited β] [semilattice_sup β] (u : β → α) {a : α} :
  tendsto u at_top (nhds a) ↔ ∀ε>0, ∃N, ∀n≥N, edist (u n) a < ε :=
begin
  rw tendsto_nhds,
  apply forall_congr,
  intro ε,
  apply forall_congr,
  intro hε,
  simp,
  exact ⟨λ ⟨s, ⟨N, hN⟩, hs⟩, ⟨N, λn hn, hs _ (hN _ hn)⟩, λ ⟨N, hN⟩, ⟨{n | n ≥ N}, ⟨⟨N, by simp⟩, hN⟩⟩⟩,
end

/-- In an emetric space, Cauchy sequences are characterized by the fact that, eventually,
the edistance between its elements is arbitrarily small -/
theorem cauchy_seq_iff [inhabited β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀m n≥N, edist (u n) (u m) < ε :=
begin
  simp only [cauchy_seq, emetric.cauchy_iff, true_and, exists_prop, filter.mem_at_top_sets,
    filter.at_top_ne_bot, filter.mem_map, ne.def, filter.map_eq_bot_iff, not_false_iff, set.mem_set_of_eq],
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨t, ⟨N, hN⟩, ht⟩,
    exact ⟨N, λm n hm hn, ht _ _ (hN _ hn) (hN _ hm)⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (ennreal.half_pos εpos) with ⟨N, hN⟩,
    existsi ball (u N) (ε/2),
    split,
    { exact ⟨N, λx hx, hN _ _ (le_refl N) hx⟩ },
    { exact λx y hx hy, calc
        edist x y ≤ edist x (u N) + edist y (u N) : edist_triangle_right _ _ _
        ... < ε/2 + ε/2 : ennreal.add_lt_add hx hy
        ... = ε : ennreal.add_halves _ } }
end

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchy_seq_iff' [inhabited β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ ∀ε>(0 : ennreal), ∃N, ∀n≥N, edist (u n) (u N) < ε :=
begin
  rw cauchy_seq_iff,
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨N, hN⟩,
    exact ⟨N, λn hn, hN _ _ (le_refl N) hn⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (ennreal.half_pos εpos) with ⟨N, hN⟩,
    exact ⟨N, λ m n hm hn, calc
       edist (u n) (u m) ≤ edist (u n) (u N) + edist (u m) (u N) : edist_triangle_right _ _ _
                    ... < ε/2 + ε/2 : ennreal.add_lt_add (hN _ hn) (hN _ hm)
                    ... = ε : ennreal.add_halves _⟩ }
end

theorem totally_bounded_iff {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (edist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

theorem totally_bounded_iff' {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t⊆s, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, (totally_bounded_iff_subset.1 H) _ (edist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru,
               ⟨t, _, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

section compact

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set -/
lemma countable_closure_of_compact {α : Type u} [emetric_space α] {s : set α} (hs : compact s) :
  ∃ t ⊆ s, (countable t ∧ s = closure t) :=
begin
  have A : ∀ (e:ennreal), e > 0 → ∃ t ⊆ s, (finite t ∧ s ⊆ (⋃x∈t, ball x e)) :=
    totally_bounded_iff'.1 (compact_iff_totally_bounded_complete.1 hs).1,
--    assume e, finite_cover_balls_of_compact hs,
  have B : ∀ (e:ennreal), ∃ t ⊆ s, finite t ∧ (e > 0 → s ⊆ (⋃x∈t, ball x e)),
  { intro e,
    cases le_or_gt e 0 with h,
    { exact ⟨∅, by finish⟩ },
    { rcases A e h with ⟨s, ⟨finite_s, closure_s⟩⟩, existsi s, finish }},
  /-The desired countable set is obtained by taking for each `n` the centers of a finite cover
  by balls of radius `1/n`, and then the union over `n`. -/
  choose T T_in_s finite_T using B,
  let t := ⋃n:ℕ, T n⁻¹,
  have T₁ : t ⊆ s := begin apply Union_subset, assume n, apply T_in_s end,
  have T₂ : countable t := by finish [countable_Union, countable_finite],
  have T₃ : s ⊆ closure t,
  { intros x x_in_s,
    apply mem_closure_iff'.2,
    intros ε εpos,
    rcases ennreal.exists_inv_nat_lt (bot_lt_iff_ne_bot.1 εpos) with ⟨n, hn⟩,
    have inv_n_pos : (0 : ennreal) < (n : ℕ)⁻¹ := by simp [ennreal.bot_lt_iff_ne_bot],
    have C : x ∈ (⋃y∈ T (n : ℕ)⁻¹, ball y (n : ℕ)⁻¹) :=
      mem_of_mem_of_subset x_in_s ((finite_T (n : ℕ)⁻¹).2 inv_n_pos),
    rcases mem_Union.1 C with ⟨y, _, ⟨y_in_T, rfl⟩, Dxy⟩,
    simp at Dxy,  -- Dxy : edist x y < 1 / ↑n
    have : y ∈ t := mem_of_mem_of_subset y_in_T (by apply subset_Union (λ (n:ℕ), T (n : ℕ)⁻¹)),
    have : edist x y < ε := lt_trans Dxy hn,
    exact ⟨y, ‹y ∈ t›, ‹edist x y < ε›⟩ },
  have T₄ : closure t ⊆ s := calc
    closure t ⊆ closure s : closure_mono T₁
    ... = s : closure_eq_of_is_closed (closed_of_compact _ hs),
  exact ⟨t, ⟨T₁, T₂, subset.antisymm T₃ T₄⟩⟩
end

end compact

section first_countable

instance (α : Type u) [emetric_space α] :
  topological_space.first_countable_topology α :=
⟨assume a, ⟨⋃ i:ℕ, {ball a i⁻¹},
  countable_Union $ assume n, countable_singleton _,
  suffices (⨅ i:{ i : ennreal // i > 0}, principal (ball a i)) = ⨅ (n : ℕ), principal (ball a n⁻¹),
    by simpa [nhds_eq, @infi_comm _ _ ℕ],
  begin
    apply le_antisymm,
    { refine le_infi (assume n, infi_le_of_le _ _),
      exact ⟨n⁻¹, by apply bot_lt_iff_ne_bot.2; simp⟩,
      exact le_refl _ },
    refine le_infi (assume ε, _),
    rcases ennreal.exists_inv_nat_lt (bot_lt_iff_ne_bot.1 ε.2) with ⟨n, εn⟩,
    exact infi_le_of_le n (principal_mono.2 $ ball_subset_ball $ le_of_lt εn)
  end⟩⟩

end first_countable

section second_countable
open topological_space

/-- A separable emetric space is second countable: one obtains a countable basis by taking
the balls centered at points in a dense subset, and with rational radii. We do not register
this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
lemma second_countable_of_separable (α : Type u) [emetric_space α] [separable_space α] :
  second_countable_topology α :=
let ⟨S, ⟨S_countable, S_dense⟩⟩ := separable_space.exists_countable_closure_eq_univ α in
⟨⟨⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)},
⟨show countable ⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)},
{ apply countable_bUnion S_countable,
  intros a aS,
  apply countable_Union,
  simp },
show uniform_space.to_topological_space α = generate_from (⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)}),
{ have A : ∀ (u : set α), (u ∈ ⋃x ∈ S, ⋃ (n : nat), ({ball x ((n : ennreal)⁻¹)} : set (set α))) → is_open u,
  { simp only [and_imp, exists_prop, set.mem_Union, set.mem_singleton_iff, exists_imp_distrib],
    intros u x hx i u_ball,
    rw [u_ball],
    exact is_open_ball },
  have B : is_topological_basis (⋃x ∈ S, ⋃ (n : nat), ({ball x (n⁻¹)} : set (set α))),
  { refine is_topological_basis_of_open_of_nhds A (λa u au open_u, _),
    rcases is_open_iff.1 open_u a au with ⟨ε, εpos, εball⟩,
    have : ε / 2 > 0 := ennreal.half_pos εpos,
    /- The ball `ball a ε` is included in `u`. We need to find one of our balls `ball x (n⁻¹)`
    containing `a` and contained in `ball a ε`. For this, we take `n` larger than `2/ε`, and
    then `x` in `S` at distance at most `n⁻¹` of `a` -/
    rcases ennreal.exists_inv_nat_lt (bot_lt_iff_ne_bot.1 (ennreal.half_pos εpos)) with ⟨n, εn⟩,
    have : (0 : ennreal) < n⁻¹ := by simp [ennreal.bot_lt_iff_ne_bot],
    have : (a : α) ∈ closure (S : set α) := by rw [S_dense]; simp,
    rcases mem_closure_iff'.1 this _ ‹(0 : ennreal) <  n⁻¹› with ⟨x, xS, xdist⟩,
    existsi ball x (↑n)⁻¹,
    have I : ball x (n⁻¹) ⊆ ball a ε := λy ydist, calc
      edist y a = edist a y : edist_comm _ _
      ... ≤ edist a x + edist y x : edist_triangle_right _ _ _
      ... < n⁻¹ + n⁻¹ : ennreal.add_lt_add xdist ydist
      ... < ε/2 + ε/2 : ennreal.add_lt_add εn εn
      ... = ε : ennreal.add_halves _,
    simp only [emetric.mem_ball, exists_prop, set.mem_Union, set.mem_singleton_iff],
    exact ⟨⟨x, ⟨xS, ⟨n, rfl⟩⟩⟩, ⟨by simpa, subset.trans I εball⟩⟩ },
  exact B.2.2 }⟩⟩⟩

end second_countable

section diam

/-- The diameter of a set in an emetric space, named `emetric.diam` -/
def diam (s : set α) := Sup ((λp : α × α, edist p.1 p.2) '' (set.prod s s))

/-- If two points belong to some set, their edistance is bounded by the diameter of the set -/
lemma edist_le_diam_of_mem (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ diam s :=
le_Sup ((mem_image _ _ _).2 ⟨(⟨x, y⟩ : α × α), by simp [hx, hy]⟩)

/-- If the distance between any two points in a set is bounded by some constant, this constant
bounds the diameter. -/
lemma diam_le_of_forall_edist_le {d : ennreal} (h : ∀x y ∈ s, edist x y ≤ d) : diam s ≤ d :=
begin
  apply Sup_le _,
  simp only [and_imp, set.mem_image, set.mem_prod, exists_imp_distrib, prod.exists],
  assume b x y xs ys dxy,
  rw ← dxy,
  exact h x y xs ys
end

/-- The diameter of the empty set vanishes -/
@[simp] lemma diam_empty : diam (∅ : set α) = 0 :=
by simp [diam]

/-- The diameter of a singleton vanishes -/
@[simp] lemma diam_singleton : diam ({x} : set α) = 0 :=
by simp [diam]

/-- The diameter is monotonous with respect to inclusion -/
lemma diam_mono {s t : set α} (h : s ⊆ t) : diam s ≤ diam t :=
begin
  refine Sup_le_Sup (λp hp, _),
  simp only [set.mem_image, set.mem_prod, prod.exists] at hp,
  rcases hp with ⟨x, y, ⟨⟨xs, ys⟩, dxy⟩⟩,
  exact (mem_image _ _ _).2 ⟨⟨x, y⟩, ⟨⟨h xs, h ys⟩, dxy⟩⟩
end

/-- The diameter of a union is controlled by the diameter of the sets, and the edistance
between two points in the sets. -/
lemma diam_union {t : set α} (xs : x ∈ s) (yt : y ∈ t) : diam (s ∪ t) ≤ diam s + edist x y + diam t :=
begin
  have A : ∀a ∈ s, ∀b ∈ t, edist a b ≤ diam s + edist x y + diam t := λa ha b hb, calc
    edist a b ≤ edist a x + edist x y + edist y b : edist_triangle4 _ _ _ _
    ... ≤ diam s + edist x y + diam t :
      add_le_add' (add_le_add' (edist_le_diam_of_mem ha xs) (le_refl _)) (edist_le_diam_of_mem yt hb),
  refine diam_le_of_forall_edist_le (λa b ha hb, _),
  cases (mem_union _ _ _).1 ha with h'a h'a; cases (mem_union _ _ _).1 hb with h'b h'b,
  { calc edist a b ≤ diam s : edist_le_diam_of_mem h'a h'b
        ... ≤ diam s + (edist x y + diam t) : le_add_right (le_refl _)
        ... = diam s + edist x y + diam t : by simp only [add_comm, eq_self_iff_true, add_left_comm] },
  { exact A a h'a b h'b },
  { have Z := A b h'b a h'a, rwa [edist_comm] at Z },
  { calc edist a b ≤ diam t : edist_le_diam_of_mem h'a h'b
        ... ≤ (diam s + edist x y) + diam t : le_add_left (le_refl _) }
end

lemma diam_union' {t : set α} (h : s ∩ t ≠ ∅) : diam (s ∪ t) ≤ diam s + diam t :=
let ⟨x, ⟨xs, xt⟩⟩ := ne_empty_iff_exists_mem.1 h in by simpa using diam_union xs xt

lemma diam_closed_ball {r : ennreal} : diam (closed_ball x r) ≤ 2 * r :=
diam_le_of_forall_edist_le $ λa b ha hb, calc
  edist a b ≤ edist a x + edist b x : edist_triangle_right _ _ _
  ... ≤ r + r : add_le_add' ha hb
  ... = 2 * r : by simp [mul_two, mul_comm]

lemma diam_ball {r : ennreal} : diam (ball x r) ≤ 2 * r :=
le_trans (diam_mono ball_subset_closed_ball) diam_closed_ball

end diam

end emetric --namespace
