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
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/

variables {X Y Z α : Type*} [topological_space X]

open_locale topological_space

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def is_locally_constant (f : X → Y) : Prop := ∀ s : set Y, is_open (f ⁻¹' s)

namespace is_locally_constant

lemma is_open_fiber {f : X → Y} (hf : is_locally_constant f) (y : Y) :
  is_open {x | f x = y} :=
have {x | f x = y} = f ⁻¹' {y},
by { ext, simp only [set.mem_preimage, iff_self, set.mem_singleton_iff, set.mem_set_of_eq] },
by { rw this, exact hf _ }

lemma exists_open {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ (U : set X) (hU : is_open U) (hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
⟨f ⁻¹' {(f x)}, hf _, set.mem_singleton _, λ x' hx', set.mem_singleton_iff.mp hx'⟩

lemma exists_nhds {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∃ U ∈ 𝓝 x, ∀ x' ∈ U, f x' = f x :=
let ⟨U, hU, hx, H⟩ := hf.exists_open x in ⟨U, mem_nhds_sets hU hx, H⟩

protected lemma eventually_eq {f : X → Y} (hf : is_locally_constant f) (x : X) :
  ∀ᶠ y in 𝓝 x, f y = f x :=
begin
  rw eventually_nhds_iff,
  obtain ⟨U, hU, hx, H⟩ := hf.exists_open x,
  exact ⟨U, H, hU, hx⟩
end

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

lemma iff_eventually_eq (f : X → Y) :
  is_locally_constant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
begin
  refine ⟨is_locally_constant.eventually_eq, _⟩,
  assume h,
  rw iff_exists_open,
  assume x,
  specialize h x,
  rw eventually_nhds_iff at h,
  obtain ⟨U, H, hU, hxU⟩ := h,
  exact ⟨U, hU, hxU, H⟩
end

protected lemma continuous [topological_space Y] {f : X → Y} (hf : is_locally_constant f) :
  continuous f :=
⟨λ U hU, hf _⟩

lemma iff_continuous {_ : topological_space Y} [discrete_topology Y] (f : X → Y) :
  is_locally_constant f ↔ continuous f :=
⟨is_locally_constant.continuous, λ h s, h.is_open_preimage s (is_open_discrete _)⟩

lemma iff_continuous_bot (f : X → Y) :
  is_locally_constant f ↔ @continuous X Y _ ⊥ f :=
iff_continuous f

lemma of_constant (f : X → Y) (h : ∀ x y, f x = f y) :
  is_locally_constant f :=
begin
  rw iff_exists_nhds,
  intro x,
  refine ⟨set.univ, filter.univ_mem_sets, _⟩,
  rintro y -,
  exact h _ _
end

lemma const (y : Y) : is_locally_constant (function.const X y) :=
of_constant _ $ λ _ _, rfl

lemma comp {f : X → Y} (hf : is_locally_constant f) (g : Y → Z) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf _ }

lemma comp₂ {Y₁ Y₂ Z : Type*} {f : X → Y₁} {g : X → Y₂}
  (hf : is_locally_constant f) (hg : is_locally_constant g) (h : Y₁ → Y₂ → Z) :
  is_locally_constant (λ x, h (f x) (g x)) :=
begin
  letI : topological_space Y₁ := ⊥,
  haveI : discrete_topology Y₁ := ⟨rfl⟩,
  letI : topological_space Y₂ := ⊥,
  haveI : discrete_topology Y₂ := ⟨rfl⟩,
  letI : topological_space Z := ⊥,
  haveI : discrete_topology Z := ⟨rfl⟩,
  rw iff_continuous_bot at hf hg ⊢,
  let fg : X → Y₁ × Y₂ := λ x, (f x, g x),
  have fg_ctu : continuous fg := hf.prod_mk hg,
  let h' : Y₁ × Y₂ → Z := λ y, h y.1 y.2,
  have h'_ctu : continuous h' := continuous_of_discrete_topology,
  exact h'_ctu.comp fg_ctu
end

lemma comp_continuous [topological_space Y] {g : Y → Z} {f : X → Y}
  (hg : is_locally_constant g) (hf : continuous f) :
  is_locally_constant (g ∘ f) :=
λ s, by { rw set.preimage_comp, exact hf.is_open_preimage _ (hg _) }

lemma apply_eq_of_is_preconnected {f : X → Y} (hf : is_locally_constant f)
  (s : set X) (hs : is_preconnected s) (x y : X) (hx : x ∈ s) (hy : y ∈ s) :
  f y = f x :=
begin
  let U := f ⁻¹' {f x},
  let V := f ⁻¹' (set.univ \ {f x}),
  specialize hs U V (hf _) (hf _),
  simp only [U, V, set.mem_empty_eq, set.inter_empty, set.preimage_diff, ne.def,
    set.union_diff_self, ← set.inter_diff_assoc, set.inter_self, set.inter_diff_self,
    ← @set.ne_empty_iff_nonempty _ ∅, not_true, eq_self_iff_true, set.preimage_univ] at hs,
  classical, by_contra hxy,
  exact hs (λ z hz, or.inr trivial) ⟨x, hx, rfl⟩ ⟨y, ⟨hy, trivial⟩, hxy⟩,
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
hf.comp (λ x, x⁻¹)

@[to_additive]
lemma mul [has_mul Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f * g) :=
hf.comp₂ hg (*)

@[to_additive]
lemma div [has_div Y] ⦃f g : X → Y⦄ (hf : is_locally_constant f) (hg : is_locally_constant g) :
  is_locally_constant (f / g) :=
hf.comp₂ hg (/)

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
then λ g, ⟨g ∘ f, g.is_locally_constant.comp_continuous hf⟩
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
