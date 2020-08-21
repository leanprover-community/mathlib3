import geometry.manifold.local_diffeomorph
import geometry.manifold.tangent_bundle_derivation
import linear_algebra.dual

noncomputable theory

section

open set

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E_B : Type*} [normed_group E_B] [normed_space 𝕜 E_B]
{E_F : Type*} [normed_group E_F] [normed_space 𝕜 E_F]
{E_Z : Type*} [normed_group E_Z] [normed_space 𝕜 E_Z]
{H_B : Type*} [topological_space H_B] (I_B : model_with_corners 𝕜 E_B H_B)
{H_F : Type*} [topological_space H_F] (I_F : model_with_corners 𝕜 E_F H_F)
{H_Z : Type*} [topological_space H_Z] (I_Z : model_with_corners 𝕜 E_Z H_Z)
{B : Type*} [topological_space B] [charted_space H_B B] [smooth_manifold_with_corners I_B B]
{Z : Type*} [topological_space Z] [charted_space H_Z Z] [smooth_manifold_with_corners I_Z Z]
{F : Type*} [topological_space F] [charted_space H_F F] [smooth_manifold_with_corners I_F F]
(proj : Z → B)

variable (F)

#check linear_map.trace_aux

/--
A structure extending local homeomorphisms, defining a local trivialization of a projection
`proj : Z → B` with fiber `F`, as a local homeomorphism between `Z` and `B × F` defined between two
sets of the form `proj ⁻¹' base_set` and `base_set × F`, acting trivially on the first coordinate.
-/
structure smooth_bundle_trivialization extends local_times_diffeomorph I_Z (I_B.prod I_F) Z (B × F) ⊤ :=
(base_set      : set B)
(open_base_set : is_open base_set)
(source_eq     : source = proj ⁻¹' base_set)
(target_eq     : target = set.prod base_set univ)
(proj_to_fun   : ∀ p ∈ source, (to_fun p).1 = proj p)

instance : has_coe_to_fun (smooth_bundle_trivialization I_B I_F I_Z F proj) := ⟨_, λ e, e.to_fun⟩

@[simp, mfld_simps] lemma smooth_bundle_trivialization.coe_coe (e : smooth_bundle_trivialization I_B I_F I_Z F proj) (x : Z) :
  e.to_local_times_diffeomorph x = e x := rfl

@[simp, mfld_simps] lemma smooth_bundle_trivialization.coe_mk (e : local_times_diffeomorph I_Z (I_B.prod I_F) Z (B × F) ⊤) (i j k l m) (x : Z) :
  (bundle_trivialization.mk e i j k l m : bundle_trivialization F proj) x = e x := sorry

variables {I_B} {I_F} {I_Z} {F} {proj}

def smooth_bundle_trivialization.to_bundle_trivialization (e : smooth_bundle_trivialization I_B I_F I_Z F proj) : bundle_trivialization F proj :=
{ base_set := e.base_set,
  open_base_set := e.open_base_set,
  source_eq := e.source_eq,
  target_eq := e.target_eq,
  proj_to_fun := e.proj_to_fun,
  .. e.to_local_times_diffeomorph.to_local_homeomorph }

instance smooth_bundle_triv_to_bunlde_triv : has_coe (smooth_bundle_trivialization I_B I_F I_Z F proj) (bundle_trivialization F proj) :=
⟨λ e, e.to_bundle_trivialization⟩

variables (I_B) (I_F) (I_Z) (F) (proj)

/-- A smooth fiber bundle with fiber F over a base B is a space projecting on B for which the
fibers are all diffeomorphic to F, such that the local situation around each point is a direct
product. -/
def is_smooth_fiber_bundle : Prop :=
∀ x : Z, ∃e : smooth_bundle_trivialization I_B I_F I_Z F proj, x ∈ e.source

instance smooth_fiber_bundle_is_topological_fiber_bundle :
  has_coe (is_smooth_fiber_bundle I_B I_F I_Z F proj) (is_topological_fiber_bundle F proj) :=
⟨λ h x, by { cases h x with e h_e, use [e, h_e] }⟩

variables {I_F} {F}

def smooth_sections /-[is_topological_fiber_bundle F proj]-/ :=
  {f : B → Z // proj ∘ f = id ∧ smooth I_B I_Z f}

instance : has_coe_to_fun (smooth_sections I_B I_Z proj) := ⟨_, subtype.val⟩

variables {f g : smooth_sections I_B I_Z proj}

namespace smooth_sections

variables {I_B} {I_F} {I_Z} {F} {proj}

@[ext] lemma ext (H : ∀x, f x = g x) : f = g :=
subtype.eq $ funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x :=
⟨λ h, λ x, h ▸ rfl, ext⟩

end smooth_sections

end

section

open topological_space set

namespace basic_smooth_bundle_core

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
(Z : basic_smooth_bundle_core I M F)

/-- Local diffeomorphism version of the trivialization change. -/
def triv_change (i j : atlas H M) : local_diffeomorph (I.prod (model_with_corners_self 𝕜 F)) (I.prod (model_with_corners_self 𝕜 F)) (M × F) (M × F) :=
{ source      := set.prod (Z.to_topological_fiber_bundle_core.base_set i ∩ Z.to_topological_fiber_bundle_core.base_set j) univ,
  target      := set.prod (Z.to_topological_fiber_bundle_core.base_set i ∩ Z.to_topological_fiber_bundle_core.base_set j) univ,
  to_fun      := λp, ⟨p.1, Z.to_topological_fiber_bundle_core.coord_change i j p.1 p.2⟩,
  inv_fun     := λp, ⟨p.1, Z.to_topological_fiber_bundle_core.coord_change j i p.1 p.2⟩,
  map_source' := λp hp, by simpa using hp,
  map_target' := λp hp, by simpa using hp,
  left_inv'   := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.to_topological_fiber_bundle_core.coord_change_comp, Z.to_topological_fiber_bundle_core.coord_change_self],
    { exact hx.1 },
    { simp only [mem_inter_eq, base_set, subtype.val_eq_coe],
      cases hx, cases j, cases i, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { assumption }, assumption }, assumption, }
  end,
  right_inv'  := begin
    rintros ⟨x, v⟩ hx,
    simp only [prod_mk_mem_set_prod_eq, mem_inter_eq, and_true, mem_univ] at hx,
    rw [Z.to_topological_fiber_bundle_core.coord_change_comp, Z.to_topological_fiber_bundle_core.coord_change_self],
    { exact hx.2 },
    { simp only [mem_inter_eq, base_set, subtype.val_eq_coe],
      cases hx, cases j, cases i, dsimp at *, fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { assumption }, assumption }, assumption, },
  end,
  open_source :=
    is_open_prod (is_open_inter (Z.to_topological_fiber_bundle_core.is_open_base_set i) (Z.to_topological_fiber_bundle_core.is_open_base_set j)) is_open_univ,
  open_target :=
    is_open_prod (is_open_inter (Z.to_topological_fiber_bundle_core.is_open_base_set i) (Z.to_topological_fiber_bundle_core.is_open_base_set j)) is_open_univ,
  times_cont_mdiff_to_fun := sorry,
  times_cont_mdiff_inv_fun := sorry,}

/-- Local trivialization of a smooth bundle created from core, as a local diffeomorphism. -/
def local_triv (i : atlas H M) : local_homeomorph Z.to_topological_fiber_bundle_core.total_space (M × F) := sorry

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv_ext (i :  atlas H M) : smooth_bundle_trivialization I (model_with_corners_self 𝕜 F) (I.prod (model_with_corners_self 𝕜 F)) F Z.to_topological_fiber_bundle_core.proj := sorry

end basic_smooth_bundle_core

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(F : Type*) [normed_group F] [normed_space 𝕜 F]
(Z : basic_smooth_bundle_core I M F)

def basic_smooth_bundle_core.total_space := Z.to_topological_fiber_bundle_core.total_space /- Not working! -/
def basic_smooth_bundle_core.proj : Z.to_topological_fiber_bundle_core.total_space → M := Z.to_topological_fiber_bundle_core.proj /- Not working! -/

/-- A smooth fiber bundle constructed from core is indeed a smooth fiber bundle. -/
theorem is_smooth_fiber_bundle_from_core : is_smooth_fiber_bundle I (model_with_corners_self 𝕜 F) (I.prod (model_with_corners_self 𝕜 F)) F Z.to_topological_fiber_bundle_core.proj :=
λx, ⟨Z.local_triv_ext (Z.to_topological_fiber_bundle_core.index_at (Z.to_topological_fiber_bundle_core.proj x)), by sorry⟩

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

lemma tangent_bundle_is_smooth_fiber_bundle :
  is_smooth_fiber_bundle I (model_with_corners_self 𝕜 E) I.tangent E (tangent_bundle.proj I M) :=
  is_smooth_fiber_bundle_from_core E _

end

section

namespace vector_bundle

section

variables (𝕜 : Type*) {B : Type*} (F : Type*) {Z : Type*}
  [topological_space B] [topological_space Z] [normed_field 𝕜]
  [topological_space F] [add_comm_group F] [module 𝕜 F] [topological_module 𝕜 F] (proj : Z → B)
  [∀ (x : B), add_comm_group {y : Z // proj y = x}] [∀ (x : B), module 𝕜 {y : Z // proj y = x}]
  [∀ (x : B), topological_module 𝕜 {y : Z // proj y = x}]

structure vector_bundle_trivialization extends bundle_trivialization F proj :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ (y : {y : Z // proj y = x}), (to_fun y).2))

def is_topological_vector_bundle : Prop :=
∀ x : Z, ∃e : vector_bundle_trivialization 𝕜 F proj, x ∈ e.source

variables {𝕜} {F} {proj}

def topological_vector_bundle.to_topological_fiber_bundle (V : is_topological_vector_bundle 𝕜 F proj)
: is_topological_fiber_bundle F proj :=
begin
  intro x,
  have V_triv := V x,
  cases V_triv with T h_T,
  use T.to_bundle_trivialization,
  exact h_T,
end

instance topological_vector_bundle_to_topological_bundle :
  has_coe (is_topological_vector_bundle 𝕜 F proj) (is_topological_fiber_bundle F proj) :=
⟨λ V, topological_vector_bundle.to_topological_fiber_bundle V⟩

end

end vector_bundle

namespace vector_bundle_2

section

variables (𝕜 : Type*) {B : Type*} (E : B → Type*) (F : Type*)
  [normed_field 𝕜] [topological_space B] [∀ x, add_comm_group (E x)] [∀ x, topological_space (E x)]
  [∀ x, module 𝕜 (E x)] /- [∀ x, topological_vector_space 𝕜 (E x)] -/
  [topological_space F] [add_comm_group F] [module 𝕜 F] /- [topological_module 𝕜 F] -/
  [topological_space Σ x, E x]

def proj : (Σ x, E x) → B := λ y : Σ x, E x, y.1

notation V `ᵛ` 𝕜 := module.dual 𝕜 V

@[reducible] def dual := (Σ x, (E x)ᵛ𝕜)

instance {x : B} : has_coe (E x) (Σ x, E x) := ⟨λ y, (⟨x, y⟩ : (Σ x, E x))⟩

structure vector_bundle_trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ (y : (E x)), (to_fun y).2))

variables (B)

def is_topological_vector_bundle : Prop :=
∀ x : (Σ x, E x), ∃ e : vector_bundle_trivialization 𝕜 E F, x ∈ e.source

variables {𝕜} {F} {E} {B}

def topological_vector_bundle.to_topological_fiber_bundle (V : is_topological_vector_bundle 𝕜 B E F)
: is_topological_fiber_bundle F (proj E) :=
λ x, by { cases V x with T h_T, exact ⟨T.to_bundle_trivialization, h_T⟩ }

instance topological_vector_bundle.to_topological_bundle :
  has_coe (is_topological_vector_bundle 𝕜 B E F) (is_topological_fiber_bundle F (proj E)) :=
⟨λ V, topological_vector_bundle.to_topological_fiber_bundle V⟩

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
[∀ (x : M), topological_space (point_derivation I x)] /- Can be removed for finite dimensional manifolds-/

lemma tangent_bundle_derivation : is_topological_vector_bundle 𝕜 M (point_derivation I) E :=
begin
  intro v,
  sorry,
end

end

end vector_bundle_2

end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E_B : Type*} [normed_group E_B] [normed_space 𝕜 E_B]
{E_Z : Type*} [normed_group E_Z] [normed_space 𝕜 E_Z]
{H_B : Type*} [topological_space H_B] (I_B : model_with_corners 𝕜 E_B H_B)
{H_Z : Type*} [topological_space H_Z] (I_Z : model_with_corners 𝕜 E_Z H_Z)
{B : Type*} [topological_space B] [charted_space H_B B] [smooth_manifold_with_corners I_B B]
(F : Type*) [normed_group F] [normed_space 𝕜 F]
{Z : Type*} [topological_space Z] [charted_space H_Z Z] [smooth_manifold_with_corners I_Z Z]
(proj : Z → B)
[∀ (x : B), add_comm_group {y : Z // proj y = x}] [∀ (x : B), module 𝕜 {y : Z // proj y = x}]
[∀ (x : B), topological_module 𝕜 {y : Z // proj y = x}]

structure smooth_vector_bundle_trivialization extends smooth_bundle_trivialization I_B (model_with_corners_self 𝕜 F) I_Z F proj :=
(linear : ∀ x ∈ base_set, is_linear_map 𝕜 (λ (y : {y : Z // proj y = x}), (to_fun y).2))

def is_smooth_vector_bundle : Prop :=
∀ x : Z, ∃ e : smooth_vector_bundle_trivialization I_B I_Z F proj, x ∈ e.source

instance add_comm_group_section_of_vector_bundle [h : ∀ (x : B), add_comm_group {y : Z // proj y = x}] : add_comm_group (smooth_sections I_B I_Z proj) :=
{ add := λ f g, ⟨λ x, by exact
  ((⟨f x, congr_fun f.property.1 x⟩ : {y : Z // proj y = x}) + (⟨g x, congr_fun g.property.1 x⟩ : {y : Z // proj y = x}) : {y : Z // proj y = x}),
    begin
      ext,
      let sum := ((⟨f x, congr_fun f.property.1 x⟩ : {y : Z // proj y = x}) + (⟨g x, congr_fun g.property.1 x⟩ : {y : Z // proj y = x}) : {y : Z // proj y = x}),
      exact sum.property,
    end,
    begin
      sorry,
    end⟩,
  add_assoc :=
  begin
    sorry,
  end,
  zero := ⟨λ x : B, (h x).zero, by { ext, exact (h x).zero.property, },
  begin
    sorry,
  end⟩,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry, }
end

section

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

def F : Π x : M, {y : tangent_bundle I M // tangent_bundle.proj I M y = x} → tangent_space I x :=
begin
  intro x,
  intro y,
  have f := (tangent_bundle_core I M).to_topological_fiber_bundle_core.local_triv,
  unfold tangent_space,
  sorry,
end

def F2 : Π x : M, {y : tangent_bundle_derivation I M // tangent_bundle_derivation.proj I M y = x} → point_derivation I x :=
begin
  intros x y,
  let g := y.val.2,
  let h : y.val.fst = x := y.prop,
  rw h at g,
  exact g,
end

def G : Π x : M, tangent_space I x → {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
sorry

def G2 : Π x : M, point_derivation I x → {y : tangent_bundle_derivation I M // tangent_bundle_derivation.proj I M y = x} :=
by { intros x v, use ⟨x, v⟩ }

instance add_comm_group_fiber_tangent_bundle : ∀ (x : M), add_comm_group {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ add := λ a b, G x (F x a + F x b),
  add_assoc := sorry,
  zero := sorry,
  zero_add := sorry,
  add_zero := sorry,
  neg := sorry,
  add_left_neg := sorry,
  add_comm := sorry, }

instance vector_space_fiber_tangent_bundle : ∀ (x : M), module 𝕜 {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  one_smul := sorry,
  mul_smul := sorry,
  add_smul := sorry,
  zero_smul := sorry, }

instance topological_vector_space_fiber_tangent_bundle : ∀ (x : M), topological_module 𝕜 {y : tangent_bundle I M // tangent_bundle.proj I M y = x} :=
λ x,
{ continuous_smul := sorry, }

lemma tangent_bundle_is_smooth_vector_bundle :
  is_smooth_vector_bundle I I.tangent E (tangent_bundle.proj I M) :=
begin
  intro x,
  sorry,
end

end

end
