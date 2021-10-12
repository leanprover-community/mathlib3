/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import analysis.convex.hull
import analysis.inner_product_space.basic

/-!
# Convex cones

In a `𝕜`-module `E`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We also define `convex.to_cone` to be the minimal cone that includes a given convex set.

We define `set.inner_dual_cone` to be the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`.

## Main statements

We prove two extension theorems:
* `riesz_extension`:
  [M. Riesz extension theorem](https://en.wikipedia.org/wiki/M._Riesz_extension_theorem) says that
  if `s` is a convex cone in a real vector space `E`, `p` is a submodule of `E`
  such that `p + s = E`, and `f` is a linear function `p → ℝ` which is
  nonnegative on `p ∩ s`, then there exists a globally defined linear function
  `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.
* `exists_extension_of_le_sublinear`:
  Hahn-Banach theorem: if `N : E → ℝ` is a sublinear map, `f` is a linear map
  defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
  then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
  for all `x`

## Implementation notes

While `convex 𝕜` is a predicate on sets, `convex_cone 𝕜 E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
-/


open set linear_map
open_locale classical pointwise

variables {𝕜 E F G : Type*}

/-! ### Definition of `convex_cone` and basic properties -/

section definitions
variables (𝕜 E) [ordered_semiring 𝕜]

/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure convex_cone [add_comm_monoid E] [has_scalar 𝕜 E] :=
(carrier : set E)
(smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier)
(add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier)

end definitions

variables {𝕜 E}

namespace convex_cone
section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E]

section has_scalar
variables [has_scalar 𝕜 E] (S T : convex_cone 𝕜 E)

instance : has_coe (convex_cone 𝕜 E) (set E) := ⟨convex_cone.carrier⟩

instance : has_mem E (convex_cone 𝕜 E) := ⟨λ m S, m ∈ S.carrier⟩

instance : has_le (convex_cone 𝕜 E) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

instance : has_lt (convex_cone 𝕜 E) := ⟨λ S T, S.carrier ⊂ T.carrier⟩

@[simp, norm_cast] lemma mem_coe {x : E} : x ∈ (S : set E) ↔ x ∈ S := iff.rfl

@[simp] lemma mem_mk {s : set E} {h₁ h₂ x} : x ∈ @mk 𝕜 _ _ _ _ s h₁ h₂ ↔ x ∈ s := iff.rfl

/-- Two `convex_cone`s are equal if the underlying sets are equal. -/
theorem ext' {S T : convex_cone 𝕜 E} (h : (S : set E) = T) : S = T :=
by cases S; cases T; congr'

/-- Two `convex_cone`s are equal if and only if the underlying sets are equal. -/
protected theorem ext'_iff {S T : convex_cone 𝕜 E}  : (S : set E) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext] theorem ext {S T : convex_cone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

lemma smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S := S.smul_mem' hc hx

lemma add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S := S.add_mem' hx hy

instance : has_inf (convex_cone 𝕜 E) :=
⟨λ S T, ⟨S ∩ T, λ c hc x hx, ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩,
  λ x hx y hy, ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

lemma coe_inf : ((S ⊓ T : convex_cone 𝕜 E) : set E) = ↑S ∩ ↑T := rfl

lemma mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

instance : has_Inf (convex_cone 𝕜 E) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s,
  λ c hc x hx, mem_bInter $ λ s hs, s.smul_mem hc $ by apply mem_bInter_iff.1 hx s hs,
  λ x hx y hy, mem_bInter $ λ s hs, s.add_mem (by apply mem_bInter_iff.1 hx s hs)
    (by apply mem_bInter_iff.1 hy s hs)⟩⟩

lemma mem_Inf {x : E} {S : set (convex_cone 𝕜 E)} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s := mem_bInter_iff

variables (𝕜)

instance : has_bot (convex_cone 𝕜 E) := ⟨⟨∅, λ c hc x, false.elim, λ x, false.elim⟩⟩

lemma mem_bot (x : E) : x ∈ (⊥ : convex_cone 𝕜 E) = false := rfl

instance : has_top (convex_cone 𝕜 E) := ⟨⟨univ, λ c hc x hx, mem_univ _, λ x hx y hy, mem_univ _⟩⟩

lemma mem_top (x : E) : x ∈ (⊤ : convex_cone 𝕜 E) := mem_univ x

instance : complete_lattice (convex_cone 𝕜 E) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x, false.elim,
  top          := (⊤),
  le_top       := λ S x hx, mem_top 𝕜 x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  sup          := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  Sup          := λ s, Inf {T | ∀ S ∈ s, S ≤ T},
  le_sup_left  := λ a b, λ x hx, mem_Inf.2 $ λ s hs, hs.1 hx,
  le_sup_right := λ a b, λ x hx, mem_Inf.2 $ λ s hs, hs.2 hx,
  sup_le       := λ a b c ha hb x hx, mem_Inf.1 hx c ⟨ha, hb⟩,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  le_Sup       := λ s p hs x hx, mem_Inf.2 $ λ t ht, ht p hs hx,
  Sup_le       := λ s p hs x hx, mem_Inf.1 hx p hs,
  le_Inf       := λ s a ha x hx, mem_Inf.2 $ λ t ht, ha t ht hx,
  Inf_le       := λ s a ha x hx, mem_Inf.1 hx _ ha,
  .. partial_order.lift (coe : convex_cone 𝕜 E → set E) (λ a b, ext') }

instance : inhabited (convex_cone 𝕜 E) := ⟨⊥⟩

end has_scalar

section module
variables [module 𝕜 E] (S : convex_cone 𝕜 E)

protected lemma convex : convex 𝕜 (S : set E) :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab,
  S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

end module
end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [add_comm_monoid F] [add_comm_monoid G]

section mul_action
variables [mul_action 𝕜 E] (S : convex_cone 𝕜 E)

lemma smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : E} :
  c • x ∈ S ↔ x ∈ S :=
⟨λ h, inv_smul_smul₀ hc.ne' x ▸ S.smul_mem (inv_pos.2 hc) h, S.smul_mem hc⟩

end mul_action

section module
variables [module 𝕜 E] [module 𝕜 F] [module 𝕜 G]

/-- The image of a convex cone under a `𝕜`-linear map is a convex cone. -/
def map (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 E) : convex_cone 𝕜 F :=
{ carrier := f '' S,
  smul_mem' := λ c hc y ⟨x, hx, hy⟩, hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx),
  add_mem' := λ y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩, hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸
    mem_image_of_mem f (S.add_mem hx₁ hx₂) }

lemma map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 E) :
  (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image g f S

@[simp] lemma map_id (S : convex_cone 𝕜 E) : S.map linear_map.id = S := ext' $ image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 F) : convex_cone 𝕜 E :=
{ carrier := f ⁻¹' S,
  smul_mem' := λ c hc x hx, by { rw [mem_preimage, f.map_smul c], exact S.smul_mem hc hx },
  add_mem' := λ x hx y hy, by { rw [mem_preimage, f.map_add], exact S.add_mem hx hy } }

@[simp] lemma comap_id (S : convex_cone 𝕜 E) : S.comap linear_map.id = S := ext' preimage_id

lemma comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
ext' $ preimage_comp.symm

@[simp] lemma mem_comap {f : E →ₗ[𝕜] F} {S : convex_cone 𝕜 F} {x : E} : x ∈ S.comap f ↔ f x ∈ S :=
iff.rfl

end module
end add_comm_monoid

section ordered_add_comm_group
variables [ordered_add_comm_group E] [module 𝕜 E]

/--
Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
lemma to_ordered_smul (S : convex_cone 𝕜 E) (h : ∀ x y : E, x ≤ y ↔ y - x ∈ S) :
  ordered_smul 𝕜 E :=
ordered_smul.mk'
begin
  intros x y z xy hz,
  rw [h (z • x) (z • y), ←smul_sub z y x],
  exact smul_mem S hz ((h x y).mp xy.le),
end

end ordered_add_comm_group
end linear_ordered_field

/-! ### Convex cones with extra properties -/

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [has_scalar 𝕜 E] (S : convex_cone 𝕜 E)

/-- A convex cone is pointed if it includes `0`. -/
def pointed (S : convex_cone 𝕜 E) : Prop := (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def blunt (S : convex_cone 𝕜 E) : Prop := (0 : E) ∉ S

lemma pointed_iff_not_blunt (S : convex_cone 𝕜 E) : S.pointed ↔ ¬S.blunt :=
⟨λ h₁ h₂, h₂ h₁, not_not.mp⟩

lemma blunt_iff_not_pointed (S : convex_cone 𝕜 E) : S.blunt ↔ ¬S.pointed :=
by rw [pointed_iff_not_blunt, not_not]

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [has_scalar 𝕜 E] (S : convex_cone 𝕜 E)

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def flat : Prop := ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def salient : Prop := ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S

lemma salient_iff_not_flat (S : convex_cone 𝕜 E) : S.salient ↔ ¬S.flat :=
begin
  split,
  { rintros h₁ ⟨x, xs, H₁, H₂⟩,
    exact h₁ x xs H₁ H₂ },
  { intro h,
    unfold flat at h,
    push_neg at h,
    exact h }
end

/-- A flat cone is always pointed (contains `0`). -/
lemma flat.pointed {S : convex_cone 𝕜 E} (hS : S.flat) : S.pointed :=
begin
  obtain ⟨x, hx, _, hxneg⟩ := hS,
  rw [pointed, ←add_neg_self x],
  exact add_mem S hx hxneg,
end

/-- A blunt cone (one not containing `0`) is always salient. -/
lemma blunt.salient {S : convex_cone 𝕜 E} : S.blunt → S.salient :=
begin
  rw [salient_iff_not_flat, blunt_iff_not_pointed],
  exact mt flat.pointed,
end

/-- A pointed convex cone defines a preorder. -/
def to_preorder (h₁ : S.pointed) : preorder E :=
{ le := λ x y, y - x ∈ S,
  le_refl := λ x, by change x - x ∈ S; rw [sub_self x]; exact h₁,
  le_trans := λ x y z xy zy, by simpa using add_mem S zy xy }

/-- A pointed and salient cone defines a partial order. -/
def to_partial_order (h₁ : S.pointed) (h₂ : S.salient) : partial_order E :=
{ le_antisymm :=
    begin
      intros a b ab ba,
      by_contradiction h,
      have h' : b - a ≠ 0 := λ h'', h (eq_of_sub_eq_zero h'').symm,
      have H := h₂ (b-a) ab h',
      rw neg_sub b a at H,
      exact H ba,
    end,
  ..to_preorder S h₁ }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def to_ordered_add_comm_group (h₁ : S.pointed) (h₂ : S.salient) :
  ordered_add_comm_group E :=
{ add_le_add_left :=
    begin
      intros a b hab c,
      change c + b - (c + a) ∈ S,
      rw add_sub_add_left_eq_sub,
      exact hab,
    end,
  ..to_partial_order S h₁ h₂,
  ..show add_comm_group E, by apply_instance }

end add_comm_group
end ordered_semiring

/-! ### Positive cone of an ordered module -/

section positive_cone
variables (𝕜 E) [ordered_semiring 𝕜] [ordered_add_comm_group E] [module 𝕜 E] [ordered_smul 𝕜 E]

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive_cone : convex_cone 𝕜 E :=
{ carrier := {x | 0 ≤ x},
  smul_mem' :=
    begin
      rintro c hc x (hx : _ ≤ _),
      rw ←smul_zero c,
      exact smul_le_smul_of_nonneg hx hc.le,
    end,
  add_mem' := λ x (hx : _ ≤ _) y (hy : _ ≤ _), add_nonneg hx hy }

/-- The positive cone of an ordered module is always salient. -/
lemma salient_positive_cone : salient (positive_cone 𝕜 E) :=
λ x xs hx hx', lt_irrefl (0 : E)
  (calc
    0   < x         : lt_of_le_of_ne xs hx.symm
    ... ≤ x + (-x)  : le_add_of_nonneg_right hx'
    ... = 0         : add_neg_self x)

/-- The positive cone of an ordered module is always pointed. -/
lemma pointed_positive_cone : pointed (positive_cone 𝕜 E) := le_refl 0

end positive_cone
end convex_cone

/-! ### Cone over a convex set -/

section cone_from_convex
variables [linear_ordered_field 𝕜] [ordered_add_comm_group E] [module 𝕜 E]

namespace convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def to_cone (s : set E) (hs : convex 𝕜 s) : convex_cone 𝕜 E :=
begin
  apply convex_cone.mk (⋃ (c : 𝕜) (H : 0 < c), c • s);
    simp only [mem_Union, mem_smul_set],
  { rintros c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩,
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩ },
  { rintros _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩,
    have : 0 < cx + cy, from add_pos cx_pos cy_pos,
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, _⟩,
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left _ this.ne'] }
end

variables {s : set E} (hs : convex 𝕜 s) {x : E}

lemma mem_to_cone : x ∈ hs.to_cone s ↔ ∃ (c : 𝕜), 0 < c ∧ ∃ y ∈ s, c • y = x :=
by simp only [to_cone, convex_cone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]

lemma mem_to_cone' : x ∈ hs.to_cone s ↔ ∃ (c : 𝕜), 0 < c ∧ c • x ∈ s :=
begin
  refine hs.mem_to_cone.trans ⟨_, _⟩,
  { rintros ⟨c, hc, y, hy, rfl⟩,
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩ },
  { rintros ⟨c, hc, hcx⟩,
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel hc.ne', one_smul]⟩ }
end

lemma subset_to_cone : s ⊆ hs.to_cone s :=
λ x hx, hs.mem_to_cone'.2 ⟨1, zero_lt_one, by rwa one_smul⟩

/-- `hs.to_cone s` is the least cone that includes `s`. -/
lemma to_cone_is_least : is_least { t : convex_cone 𝕜 E | s ⊆ t } (hs.to_cone s) :=
begin
  refine ⟨hs.subset_to_cone, λ t ht x hx, _⟩,
  rcases hs.mem_to_cone.1 hx with ⟨c, hc, y, hy, rfl⟩,
  exact t.smul_mem hc (ht hy)
end

lemma to_cone_eq_Inf : hs.to_cone s = Inf { t : convex_cone 𝕜 E | s ⊆ t } :=
hs.to_cone_is_least.is_glb.Inf_eq.symm

end convex

lemma convex_hull_to_cone_is_least (s : set E) :
  is_least {t : convex_cone 𝕜 E | s ⊆ t} ((convex_convex_hull 𝕜 s).to_cone _) :=
begin
  convert (convex_convex_hull 𝕜 s).to_cone_is_least,
  ext t,
  exact ⟨λ h, convex_hull_min h t.convex, (subset_convex_hull 𝕜 s).trans⟩,
end

lemma convex_hull_to_cone_eq_Inf (s : set E) :
  (convex_convex_hull 𝕜 s).to_cone _ = Inf {t : convex_cone 𝕜 E | s ⊆ t} :=
(convex_hull_to_cone_is_least s).is_glb.Inf_eq.symm

end cone_from_convex

/-!
### M. Riesz extension theorem

Given a convex cone `s` in a vector space `E`, a submodule `p`, and a linear `f : p → ℝ`, assume
that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then there exists a globally defined linear
function `g : E → ℝ` that agrees with `f` on `p`, and is nonnegative on `s`.

We prove this theorem using Zorn's lemma. `riesz_extension.step` is the main part of the proof.
It says that if the domain `p` of `f` is not the whole space, then `f` can be extended to a larger
subspace `p ⊔ span ℝ {y}` without breaking the non-negativity condition.

In `riesz_extension.exists_top` we use Zorn's lemma to prove that we can extend `f`
to a linear map `g` on `⊤ : submodule E`. Mathematically this is the same as a linear map on `E`
but in Lean `⊤ : submodule E` is isomorphic but is not equal to `E`. In `riesz_extension`
we use this isomorphism to prove the theorem.
-/

variables [add_comm_group E] [module ℝ E]

namespace riesz_extension
open submodule
variables (s : convex_cone ℝ E) (f : linear_pmap ℝ E ℝ)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
lemma step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
  (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
  ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x :=
begin
  rcases set_like.exists_of_lt (lt_top_iff_ne_top.2 hdom) with ⟨y, hy', hy⟩, clear hy',
  obtain ⟨c, le_c, c_le⟩ :
    ∃ c, (∀ x : f.domain, -(x:E) - y ∈ s → f x ≤ c) ∧ (∀ x : f.domain, (x:E) + y ∈ s → c ≤ f x),
  { set Sp := f '' {x : f.domain | (x:E) + y ∈ s},
    set Sn := f '' {x : f.domain | -(x:E) - y ∈ s},
    suffices : (upper_bounds Sn ∩ lower_bounds Sp).nonempty,
      by simpa only [set.nonempty, upper_bounds, lower_bounds, ball_image_iff] using this,
    refine exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (dense y)) _,
    { rcases (dense (-y)) with ⟨x, hx⟩,
      rw [← neg_neg x, coe_neg, ← sub_eq_add_neg] at hx,
      exact ⟨_, hx⟩ },
    rintros a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩,
    have := s.add_mem hxp hxn,
    rw [add_assoc, add_sub_cancel'_right, ← sub_eq_add_neg, ← coe_sub] at this,
    replace := nonneg _ this,
    rwa [f.map_sub, sub_nonneg] at this },
  have hy' : y ≠ 0, from λ hy₀, hy (hy₀.symm ▸ zero_mem _),
  refine ⟨f.sup_span_singleton y (-c) hy, _, _⟩,
  { refine lt_iff_le_not_le.2 ⟨f.left_le_sup _ _, λ H, _⟩,
    replace H := linear_pmap.domain_mono.monotone H,
    rw [linear_pmap.domain_sup_span_singleton, sup_le_iff, span_le, singleton_subset_iff] at H,
    exact hy H.2 },
  { rintros ⟨z, hz⟩ hzs,
    rcases mem_sup.1 hz with ⟨x, hx, y', hy', rfl⟩,
    rcases mem_span_singleton.1 hy' with ⟨r, rfl⟩,
    simp only [subtype.coe_mk] at hzs,
    erw [linear_pmap.sup_span_singleton_apply_mk _ _ _ _ _ hx, smul_neg,
      ← sub_eq_add_neg, sub_nonneg],
    rcases lt_trichotomy r 0 with hr|hr|hr,
    { have : -(r⁻¹ • x) - y ∈ s,
        by rwa [← s.smul_mem_iff (neg_pos.2 hr), smul_sub, smul_neg, neg_smul, neg_neg, smul_smul,
          mul_inv_cancel hr.ne, one_smul, sub_eq_add_neg, neg_smul, neg_neg],
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this,
      rwa [← mul_le_mul_left (neg_pos.2 hr), ← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul,
        neg_le_neg_iff, f.map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel hr.ne,
        one_mul] at this },
    { subst r,
      simp only [zero_smul, add_zero] at hzs ⊢,
      apply nonneg,
      exact hzs },
    { have : r⁻¹ • x + y ∈ s,
        by rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel hr.ne', one_smul],
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this,
      rwa [← mul_le_mul_left hr, f.map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel hr.ne', one_mul] at this } }
end

theorem exists_top (p : linear_pmap ℝ E ℝ)
  (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
  (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
  ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
begin
  replace hp_nonneg : p ∈ { p | _ }, by { rw mem_set_of_eq, exact hp_nonneg },
  obtain ⟨q, hqs, hpq, hq⟩ := zorn.zorn_nonempty_partial_order₀ _ _ _ hp_nonneg,
  { refine ⟨q, hpq, _, hqs⟩,
    contrapose! hq,
    rcases step s q hqs _ hq with ⟨r, hqr, hr⟩,
    { exact ⟨r, hr, hqr.le, hqr.ne'⟩ },
    { exact λ y, let ⟨x, hx⟩ := hp_dense y in ⟨of_le hpq.left x, hx⟩ } },
  { intros c hcs c_chain y hy,
    clear hp_nonneg hp_dense p,
    have cne : c.nonempty := ⟨y, hy⟩,
    refine ⟨linear_pmap.Sup c c_chain.directed_on, _, λ _, linear_pmap.le_Sup c_chain.directed_on⟩,
    rintros ⟨x, hx⟩ hxs,
    have hdir : directed_on (≤) (linear_pmap.domain '' c),
      from directed_on_image.2 (c_chain.directed_on.mono linear_pmap.domain_mono.monotone),
    rcases (mem_Sup_of_directed (cne.image _) hdir).1 hx with ⟨_, ⟨f, hfc, rfl⟩, hfx⟩,
    have : f ≤ linear_pmap.Sup c c_chain.directed_on, from linear_pmap.le_Sup _ hfc,
    convert ← hcs hfc ⟨x, hfx⟩ hxs,
    apply this.2, refl }
end

end riesz_extension

/-- M. **Riesz extension theorem**: given a convex cone `s` in a vector space `E`, a submodule `p`,
and a linear `f : p → ℝ`, assume that `f` is nonnegative on `p ∩ s` and `p + s = E`. Then
there exists a globally defined linear function `g : E → ℝ` that agrees with `f` on `p`,
and is nonnegative on `s`. -/
theorem riesz_extension (s : convex_cone ℝ E) (f : linear_pmap ℝ E ℝ)
  (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) :
  ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ (∀ x ∈ s, 0 ≤ g x) :=
begin
  rcases riesz_extension.exists_top s f nonneg dense with ⟨⟨g_dom, g⟩, ⟨hpg, hfg⟩, htop, hgs⟩,
  clear hpg,
  refine ⟨g ∘ₗ ↑(linear_equiv.of_top _ htop).symm, _, _⟩;
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.of_top_symm_apply],
  { exact λ x, (hfg (submodule.coe_mk _ _).symm).symm },
  { exact λ x hx, hgs ⟨x, _⟩ hx }
end

/-- **Hahn-Banach theorem**: if `N : E → ℝ` is a sublinear map, `f` is a linear map
defined on a subspace of `E`, and `f x ≤ N x` for all `x` in the domain of `f`,
then `f` can be extended to the whole space to a linear map `g` such that `g x ≤ N x`
for all `x`. -/
theorem exists_extension_of_le_sublinear (f : linear_pmap ℝ E ℝ) (N : E → ℝ)
  (N_hom : ∀ (c : ℝ), 0 < c → ∀ x, N (c • x) = c * N x)
  (N_add : ∀ x y, N (x + y) ≤ N x + N y)
  (hf : ∀ x : f.domain, f x ≤ N x) :
  ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ (∀ x, g x ≤ N x) :=
begin
  let s : convex_cone ℝ (E × ℝ) :=
  { carrier := {p : E × ℝ | N p.1 ≤ p.2 },
    smul_mem' := λ c hc p hp,
      calc N (c • p.1) = c * N p.1 : N_hom c hc p.1
      ... ≤ c * p.2 : mul_le_mul_of_nonneg_left hp hc.le,
    add_mem' := λ x hx y hy, (N_add _ _).trans (add_le_add hx hy) },
  obtain ⟨g, g_eq, g_nonneg⟩ :=
    riesz_extension s ((-f).coprod (linear_map.id.to_pmap ⊤)) _ _;
    try { simp only [linear_pmap.coprod_apply, to_pmap_apply, id_apply,
            linear_pmap.neg_apply, ← sub_eq_neg_add, sub_nonneg, subtype.coe_mk] at * },
  replace g_eq : ∀ (x : f.domain) (y : ℝ), g (x, y) = y - f x,
  { intros x y,
    simpa only [subtype.coe_mk, subtype.coe_eta] using g_eq ⟨(x, y), ⟨x.2, trivial⟩⟩ },
  { refine ⟨-g.comp (inl ℝ E ℝ), _, _⟩; simp only [neg_apply, inl_apply, comp_apply],
    { intro x, simp [g_eq x 0] },
    { intro x,
      have A : (x, N x) = (x, 0) + (0, N x), by simp,
      have B := g_nonneg ⟨x, N x⟩ (le_refl (N x)),
      rw [A, map_add, ← neg_le_iff_add_nonneg'] at B,
      have C := g_eq 0 (N x),
      simp only [submodule.coe_zero, f.map_zero, sub_zero] at C,
      rwa ← C } },
  { exact λ x hx, le_trans (hf _) hx },
  { rintros ⟨x, y⟩,
    refine ⟨⟨(0, N x - y), ⟨f.domain.zero_mem, trivial⟩⟩, _⟩,
    simp only [convex_cone.mem_mk, mem_set_of_eq, subtype.coe_mk, prod.fst_add, prod.snd_add,
      zero_add, sub_add_cancel] }
end

/-! ### The dual cone -/

section dual
variables {H : Type*} [inner_product_space ℝ H] (s t : set H)
open_locale real_inner_product_space

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
noncomputable def set.inner_dual_cone (s : set H) : convex_cone ℝ H :=
{ carrier := { y | ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ },
  smul_mem' := λ c hc y hy x hx,
  begin
    rw real_inner_smul_right,
    exact mul_nonneg hc.le (hy x hx)
  end,
  add_mem' := λ u hu v hv x hx,
  begin
    rw inner_add_right,
    exact add_nonneg (hu x hx) (hv x hx)
  end }

lemma mem_inner_dual_cone (y : H) (s : set H) :
  y ∈ s.inner_dual_cone ↔ ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ := by refl

@[simp] lemma inner_dual_cone_empty : (∅ : set H).inner_dual_cone = ⊤ :=
convex_cone.ext' (eq_univ_of_forall
  (λ x y hy, false.elim (set.not_mem_empty _ hy)))

lemma inner_dual_cone_le_inner_dual_cone (h : t ⊆ s) :
  s.inner_dual_cone ≤ t.inner_dual_cone :=
λ y hy x hx, hy x (h hx)

lemma pointed_inner_dual_cone : s.inner_dual_cone.pointed :=
λ x hx, by rw inner_zero_right

end dual
