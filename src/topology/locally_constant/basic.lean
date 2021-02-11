/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.subset_properties
import topology.connected
import topology.algebra.monoid

/-!
# Locally constant functions

This file setups the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if everything set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/

variables {X Y Z α : Type*} [topological_space X]

open_locale topological_space

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def is_locally_constant (f : X → Y) : Prop := ∀ s : set Y, is_open (f ⁻¹' s)

namespace is_locally_constant

lemma exists_open {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
⟨f ⁻¹' {(f x)}, hf _, set.mem_singleton _, λ x' hx', set.mem_singleton_iff.mp hx'⟩

lemma exists_nhds {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ U ∈ 𝓝 x, ∀ x' ∈ U, f x' = f x :=
let ⟨U, hU, hx, H⟩ := hf.exists_open x in ⟨U, mem_nhds_sets hU hx, H⟩

lemma iff_exists_open (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
begin
  refine ⟨exists_open, _⟩,
  assume h s,
  rw is_open_iff_forall_mem_open,
  assume x hx,
  obtain ⟨U, hU, hxU, H⟩ := h x,
  refine ⟨U, _, hU, hxU⟩,
  assume x' hx',
  simp only [*, set.mem_preimage] at *,
end

lemma iff_exists_nhds (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∃ U ∈ 𝓝 x, ∀ x' ∈ U, f x' = f x :=
begin
  refine ⟨exists_nhds, _⟩,
  assume h,
  rw iff_exists_open,
  assume x,
  obtain ⟨U, hU, H⟩ := h x,
  obtain ⟨V, hVU, hV, hxV⟩ : ∃ (V : set X) (H : V ⊆ U), is_open V ∧ x ∈ V,
  by rwa mem_nhds_sets_iff at hU,
  refine ⟨V, hV, hxV, _⟩,
  assume x' hx',
  solve_by_elim only [H, hxV, hx', hVU]
end

lemma of_constant (f : X → Y) (h : ∃ y, ∀ x, f x = y) :
  is_locally_constant f :=
begin
  obtain ⟨y, hy⟩ := h,
  rw iff_exists_nhds,
  intro x,
  refine ⟨set.univ, filter.univ_mem_sets, _⟩,
  rintro x -,
  rw [hy, hy]
end

lemma const (y : Y) : is_locally_constant (function.const X y) :=
of_constant _ ⟨y, λ _, rfl⟩

protected lemma continuous {_ : topological_space Y} {f : X → Y} (hf : is_locally_constant f) :
  continuous f :=
⟨λ U hU, hf _⟩

lemma iff_continuous {_ : topological_space Y} [discrete_topology Y] (f : X → Y) :
  is_locally_constant f ↔ continuous f :=
⟨is_locally_constant.continuous, λ h s, h.is_open_preimage s (is_open_discrete _)⟩

lemma iff_continuous_bot (f : X → Y) :
  is_locally_constant f ↔ @continuous X Y _ ⊥ f :=
iff_continuous f

lemma apply_eq_of_is_preconnected {f : X → Y} (hf : is_locally_constant f)
  (s : set X) (hs : is_preconnected s) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
  f y = f x :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  have aux := is_preconnected.image hs f hf.continuous.continuous_on {f x} (f '' s \ {f x})
    (is_open_discrete _) (is_open_discrete _),
  simp only [set.union_diff_self, ← set.inter_diff_assoc, set.inter_self, set.inter_diff_self,
    set.inter_empty, ← @set.ne_empty_iff_nonempty _ ∅, eq_self_iff_true, not_true, ne.def] at aux,
  classical, by_contra hxy,
  exact aux (set.subset_union_right _ _)
    ⟨f x, set.mem_inter (set.mem_image_of_mem f hx) (set.mem_singleton _)⟩
    ⟨f y, set.mem_diff_singleton.mpr ⟨set.mem_image_of_mem f hy, hxy⟩⟩
end

lemma range_finite [compact_space X] {f : X → Y} (hf : is_locally_constant f) :
  (set.range f).finite :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  rw @iff_continuous X Y ‹_› ‹_› at hf,
  exact finite_of_is_compact_of_discrete _ (compact_range hf)
end

@[to_additive]
lemma one [has_one Y] : is_locally_constant (1 : X → Y) := const 1

@[to_additive]
lemma inv [has_inv Y] ⦃f : X → Y⦄ (hf : is_locally_constant f) :
  is_locally_constant f⁻¹ :=
begin
  intro s,
  suffices : f⁻¹ ⁻¹' s = f ⁻¹' (has_inv.inv ⁻¹' s), by { rw this, exact hf _ },
  ext, simp only [set.mem_preimage, pi.inv_apply],
end

@[to_additive]
lemma mul [has_mul Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f * g) :=
begin
  letI : topological_space Y := ⊥,
  haveI : discrete_topology Y := ⟨rfl⟩,
  rw @iff_continuous X Y ‹_› ‹_› at hf hg ⊢,
  exact hf.mul hg
end

@[to_additive]
lemma div [has_div Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f / g) :=
begin
  rw iff_exists_open at hf hg ⊢,
  intro x,
  obtain ⟨U, hU, hxU, HU⟩ := hf x,
  obtain ⟨V, hV, hxV, HV⟩ := hg x,
  use [U ∩ V, is_open_inter hU hV, ⟨hxU, hxV⟩],
  rintro x' ⟨hx'U, hx'V⟩,
  simp only [pi.div_apply, HU x' hx'U, HV x' hx'V]
end

end is_locally_constant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure locally_constant (X Y : Type*) [topological_space X] :=
(to_fun : X → Y)
(is_locally_constant : is_locally_constant to_fun)

namespace locally_constant

instance [inhabited Y] : inhabited (locally_constant X Y) :=
⟨⟨_, is_locally_constant.const (default Y)⟩⟩

instance : has_coe_to_fun (locally_constant X Y) := ⟨_, locally_constant.to_fun⟩

initialize_simps_projections locally_constant (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : locally_constant X Y) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : locally_constant X Y) = f := rfl

theorem congr_fun {f g : locally_constant X Y} (h : f = g) (x : X) : f x = g x :=
congr_arg (λ h : locally_constant X Y, h x) h

theorem congr_arg (f : locally_constant X Y) {x y : X} (h : x = y) : f x = f y :=
congr_arg (λ x : X, f x) h

theorem coe_inj ⦃f g : locally_constant X Y⦄ (h : (f : X → Y) = g) : f = g :=
by cases f; cases g; cases h; refl

@[ext] theorem ext ⦃f g : locally_constant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

theorem ext_iff {f g : locally_constant X Y} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

protected lemma continuous [topological_space Y] (f : locally_constant X Y) : continuous f :=
f.is_locally_constant.continuous

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type*) {Y : Type*} [topological_space X] (y : Y) :
  locally_constant X Y :=
⟨function.const X y, is_locally_constant.const _⟩

lemma range_finite [compact_space X] (f : locally_constant X Y) :
  (set.range f).finite :=
f.is_locally_constant.range_finite

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : locally_constant X Y → locally_constant X Z :=
λ g, ⟨f ∘ g, λ s, by { rw set.preimage_comp, apply g.is_locally_constant }⟩

@[simp] lemma map_apply (f : Y → Z) (g : locally_constant X Y) : ⇑(map f g) = f ∘ g := rfl

@[simp] lemma map_id : @map X Y Y _ id = id := by { ext, refl }

@[simp] lemma map_comp {Y₁ Y₂ Y₃ : Type*} (g : Y₂ → Y₃) (f : Y₁ → Y₂) :
  @map X _ _ _ g ∘ map f = map (g ∘ f) := by { ext, refl }

section comap

open_locale classical

variables [topological_space Y]

/-- Pull back of locally constant maps under any map, by pre-composition. -/
noncomputable
def comap (f : X → Y) :
  locally_constant Y Z → locally_constant X Z :=
if hf : continuous f
then λ g, ⟨g ∘ f, λ s,
  by { rw set.preimage_comp, apply hf.is_open_preimage, apply g.is_locally_constant }⟩
else
begin
  by_cases H : nonempty X,
  { introsI g, exact const X (g $ f $ classical.arbitrary X) },
  { intro g, refine ⟨λ x, (H ⟨x⟩).elim, _⟩,
    intro s, rw is_open_iff_nhds, intro x, exact (H ⟨x⟩).elim }
end

@[simp] lemma coe_comap (f : X → Y) (g : locally_constant Y Z) (hf : continuous f) :
  ⇑(comap f g) = g ∘ f :=
by { rw [comap, dif_pos hf], refl }

@[simp] lemma comap_id : @comap X X Z _ _ id = id :=
by { ext, simp only [continuous_id, id.def, function.comp.right_id, coe_comap] }

lemma comap_comp [topological_space Z]
  (f : X → Y) (g : Y → Z) (hf : continuous f) (hg : continuous g) :
  @comap _ _ α _ _ f ∘ comap g = comap (g ∘ f) :=
by { ext, simp only [hf, hg, hg.comp hf, coe_comap] }

lemma comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
  (comap f : locally_constant Y Z → locally_constant X Z) =
  λ g, ⟨λ x, g y, is_locally_constant.const _⟩ :=
begin
  ext, rw coe_comap,
  { simp only [h, coe_mk, function.comp_app] },
  { rw show f = λ x, y, by ext; apply h,
    exact continuous_const }
end

end comap

end locally_constant

