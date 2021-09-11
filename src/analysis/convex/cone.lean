/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import analysis.convex.basic
import analysis.normed_space.inner_product

/-!
# Convex cones

In a vector space `E` over `ℝ`, we define a convex cone as a subset `s` such that
`a • x + b • y ∈ s` whenever `x, y ∈ s` and `a, b > 0`. We prove that convex cones form
a `complete_lattice`, and define their images (`convex_cone.map`) and preimages
(`convex_cone.comap`) under linear maps.

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

While `convex` is a predicate on sets, `convex_cone` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone

-/

universes u v

open set linear_map
open_locale classical pointwise

variables (E : Type*) [add_comm_group E] [module ℝ E]
  {F : Type*} [add_comm_group F] [module ℝ F]
  {G : Type*} [add_comm_group G] [module ℝ G]

/-!
### Definition of `convex_cone` and basic properties
-/

/-- A convex cone is a subset `s` of a vector space over `ℝ` such that `a • x + b • y ∈ s`
whenever `a, b > 0` and `x, y ∈ s`. -/
structure convex_cone :=
(carrier : set E)
(smul_mem' : ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier)
(add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier)

variable {E}

namespace convex_cone

variables (S T : convex_cone E)

instance : has_coe (convex_cone E) (set E) := ⟨convex_cone.carrier⟩

instance : has_mem E (convex_cone E) := ⟨λ m S, m ∈ S.carrier⟩

instance : has_le (convex_cone E) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

instance : has_lt (convex_cone E) := ⟨λ S T, S.carrier ⊂ T.carrier⟩

@[simp, norm_cast] lemma mem_coe {x : E} : x ∈ (S : set E) ↔ x ∈ S := iff.rfl

@[simp] lemma mem_mk {s : set E} {h₁ h₂ x} : x ∈ mk s h₁ h₂ ↔ x ∈ s := iff.rfl

/-- Two `convex_cone`s are equal if the underlying subsets are equal. -/
theorem ext' {S T : convex_cone E} (h : (S : set E) = T) : S = T :=
by cases S; cases T; congr'

/-- Two `convex_cone`s are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {S T : convex_cone E}  : (S : set E) = T ↔ S = T :=
⟨ext', λ h, h ▸ rfl⟩

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext] theorem ext {S T : convex_cone E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := ext' $ set.ext h

lemma smul_mem {c : ℝ} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S := S.smul_mem' hc hx

lemma add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S := S.add_mem' hx hy

lemma smul_mem_iff {c : ℝ} (hc : 0 < c) {x : E} :
  c • x ∈ S ↔ x ∈ S :=
⟨λ h, by simpa only [smul_smul, inv_mul_cancel (ne_of_gt hc), one_smul]
  using S.smul_mem (inv_pos.2 hc) h, λ h, S.smul_mem hc h⟩

lemma convex : convex ℝ (S : set E) :=
convex_iff_forall_pos.2 $ λ x y hx hy a b ha hb hab,
S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

instance : has_inf (convex_cone E) :=
⟨λ S T, ⟨S ∩ T, λ c hc x hx, ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩,
  λ x hx y hy, ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

lemma coe_inf : ((S ⊓ T : convex_cone E) : set E) = ↑S ∩ ↑T := rfl

lemma mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

instance : has_Inf (convex_cone E) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s,
  λ c hc x hx, mem_bInter $ λ s hs, s.smul_mem hc $ by apply mem_bInter_iff.1 hx s hs,
  λ x hx y hy, mem_bInter $ λ s hs, s.add_mem (by apply mem_bInter_iff.1 hx s hs)
    (by apply mem_bInter_iff.1 hy s hs)⟩⟩

lemma mem_Inf {x : E} {S : set (convex_cone E)} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s := mem_bInter_iff

instance : has_bot (convex_cone E) := ⟨⟨∅, λ c hc x, false.elim, λ x, false.elim⟩⟩

lemma mem_bot (x : E) : x ∈ (⊥ : convex_cone E) = false := rfl

instance : has_top (convex_cone E) := ⟨⟨univ, λ c hc x hx, mem_univ _, λ x hx y hy, mem_univ _⟩⟩

lemma mem_top (x : E) : x ∈ (⊤ : convex_cone E) := mem_univ x

instance : complete_lattice (convex_cone E) :=
{ le           := (≤),
  lt           := (<),
  bot          := (⊥),
  bot_le       := λ S x, false.elim,
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
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
  .. partial_order.lift (coe : convex_cone E → set E) (λ a b, ext') }

instance : inhabited (convex_cone E) := ⟨⊥⟩

/-- The image of a convex cone under an `ℝ`-linear map is a convex cone. -/
def map (f : E →ₗ[ℝ] F) (S : convex_cone E) : convex_cone F :=
{ carrier := f '' S,
  smul_mem' := λ c hc y ⟨x, hx, hy⟩, hy ▸ f.map_smul c x ▸ mem_image_of_mem f (S.smul_mem hc hx),
  add_mem' := λ y₁ ⟨x₁, hx₁, hy₁⟩ y₂ ⟨x₂, hx₂, hy₂⟩, hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸
    mem_image_of_mem f (S.add_mem hx₁ hx₂) }

lemma map_map (g : F →ₗ[ℝ] G) (f : E →ₗ[ℝ] F) (S : convex_cone E) :
  (S.map f).map g = S.map (g.comp f) :=
ext' $ image_image g f S

@[simp] lemma map_id : S.map linear_map.id = S := ext' $ image_id _

/-- The preimage of a convex cone under an `ℝ`-linear map is a convex cone. -/
def comap (f : E →ₗ[ℝ] F) (S : convex_cone F) : convex_cone E :=
{ carrier := f ⁻¹' S,
  smul_mem' := λ c hc x hx, by { rw [mem_preimage, f.map_smul c], exact S.smul_mem hc hx },
  add_mem' := λ x hx y hy, by { rw [mem_preimage, f.map_add], exact S.add_mem hx hy } }

@[simp] lemma comap_id : S.comap linear_map.id = S := ext' preimage_id

lemma comap_comap (g : F →ₗ[ℝ] G) (f : E →ₗ[ℝ] F) (S : convex_cone G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
ext' $ preimage_comp.symm

@[simp] lemma mem_comap {f : E →ₗ[ℝ] F} {S : convex_cone F} {x : E} :
  x ∈ S.comap f ↔ f x ∈ S := iff.rfl

/--
Constructs an ordered module given an `ordered_add_comm_group`, a cone, and a proof that
the order relation is the one defined by the cone.
-/
lemma to_ordered_smul {M : Type*} [ordered_add_comm_group M] [module ℝ M]
  (S : convex_cone M) (h : ∀ x y : M, x ≤ y ↔ y - x ∈ S) : ordered_smul ℝ M :=
ordered_smul.mk'
begin
  intros x y z xy hz,
  rw [h (z • x) (z • y), ←smul_sub z y x],
  exact smul_mem S hz ((h x y).mp (le_of_lt xy))
end

/-! ### Convex cones with extra properties -/

/-- A convex cone is pointed if it includes 0. -/
def pointed (S : convex_cone E) : Prop := (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include 0. -/
def blunt (S : convex_cone E) : Prop := (0 : E) ∉ S

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
def flat (S : convex_cone E) : Prop := ∃ x ∈ S, x ≠ (0 : E) ∧ -x ∈ S

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
def salient (S : convex_cone E) : Prop := ∀ x ∈ S, x ≠ (0 : E) → -x ∉ S

lemma pointed_iff_not_blunt (S : convex_cone E) : pointed S ↔ ¬blunt S :=
⟨λ h₁ h₂, h₂ h₁, λ h, not_not.mp h⟩

lemma salient_iff_not_flat (S : convex_cone E) : salient S ↔ ¬flat S :=
begin
  split,
  { rintros h₁ ⟨x, xs, H₁, H₂⟩,
    exact h₁ x xs H₁ H₂ },
  { intro h,
    unfold flat at h,
    push_neg at h,
    exact h }
end

/-- A blunt cone (one not containing 0) is always salient. -/
lemma salient_of_blunt (S : convex_cone E) : blunt S → salient S :=
begin
  intro h₁,
  rw [salient_iff_not_flat],
  intro h₂,
  obtain ⟨x, xs, H₁, H₂⟩ := h₂,
  have hkey : (0 : E) ∈ S := by rw [(show 0 = x + (-x), by simp)]; exact add_mem S xs H₂,
  exact h₁ hkey,
end

/-- A pointed convex cone defines a preorder. -/
def to_preorder (S : convex_cone E) (h₁ : pointed S) : preorder E :=
{ le := λ x y, y - x ∈ S,
  le_refl := λ x, by change x - x ∈ S; rw [sub_self x]; exact h₁,
  le_trans := λ x y z xy zy, by simpa using add_mem S zy xy }

/-- A pointed and salient cone defines a partial order. -/
def to_partial_order (S : convex_cone E) (h₁ : pointed S) (h₂ : salient S) : partial_order E :=
{ le_antisymm :=
    begin
      intros a b ab ba,
      by_contradiction h,
      have h' : b - a ≠ 0 := λ h'', h (eq_of_sub_eq_zero h'').symm,
      have H := h₂ (b-a) ab h',
      rw [neg_sub b a] at H,
      exact H ba,
    end,
  ..to_preorder S h₁ }

/-- A pointed and salient cone defines an `ordered_add_comm_group`. -/
def to_ordered_add_comm_group (S : convex_cone E) (h₁ : pointed S) (h₂ : salient S) :
  ordered_add_comm_group E :=
{ add_le_add_left :=
    begin
      intros a b hab c,
      change c + b - (c + a) ∈ S,
      rw [add_sub_add_left_eq_sub],
      exact hab,
    end,
  ..to_partial_order S h₁ h₂,
  ..show add_comm_group E, by apply_instance }

/-! ### Positive cone of an ordered module -/
section positive_cone

variables (M : Type*) [ordered_add_comm_group M] [module ℝ M] [ordered_smul ℝ M]

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive_cone : convex_cone M :=
{ carrier := {x | 0 ≤ x},
  smul_mem' :=
    begin
      intros c hc x hx,
      have := smul_le_smul_of_nonneg (show 0 ≤ x, by exact hx) (le_of_lt hc),
      have h' : c • (0 : M) = 0,
      { simp only [smul_zero] },
      rwa [h'] at this
    end,
  add_mem' := λ x hx y hy, add_nonneg (show 0 ≤ x, by exact hx) (show 0 ≤ y, by exact hy) }

/-- The positive cone of an ordered module is always salient. -/
lemma salient_of_positive_cone : salient (positive_cone M) :=
begin
  intros x xs hx hx',
  have := calc
    0   < x         : lt_of_le_of_ne xs hx.symm
    ... ≤ x + (-x)  : (le_add_iff_nonneg_right x).mpr hx'
    ... = 0         : by rw [tactic.ring.add_neg_eq_sub x x]; exact sub_self x,
  exact lt_irrefl 0 this,
end

/-- The positive cone of an ordered module is always pointed. -/
lemma pointed_of_positive_cone : pointed (positive_cone M) := le_refl 0

end positive_cone

end convex_cone

/-!
### Cone over a convex set
-/

namespace convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
def to_cone (s : set E) (hs : convex ℝ s) : convex_cone E :=
begin
  apply convex_cone.mk (⋃ c > 0, (c : ℝ) • s);
    simp only [mem_Union, mem_smul_set],
  { rintros c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩,
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩ },
  { rintros _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩,
    have : 0 < cx + cy, from add_pos cx_pos cy_pos,
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy (le_of_lt cx_pos) (le_of_lt cy_pos) this, _⟩,
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left _ (ne_of_gt this)] }
end

variables {s : set E} (hs : convex ℝ s) {x : E}

lemma mem_to_cone : x ∈ hs.to_cone s ↔ ∃ (c > 0) (y ∈ s), (c : ℝ) • y = x :=
by simp only [to_cone, convex_cone.mem_mk, mem_Union, mem_smul_set, eq_comm, exists_prop]

lemma mem_to_cone' : x ∈ hs.to_cone s ↔ ∃ c > 0, (c : ℝ) • x ∈ s :=
begin
  refine hs.mem_to_cone.trans ⟨_, _⟩,
  { rintros ⟨c, hc, y, hy, rfl⟩,
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel (ne_of_gt hc), one_smul]⟩ },
  { rintros ⟨c, hc, hcx⟩,
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel (ne_of_gt hc), one_smul]⟩ }
end

lemma subset_to_cone : s ⊆ hs.to_cone s :=
λ x hx, hs.mem_to_cone'.2 ⟨1, zero_lt_one, by rwa one_smul⟩

/-- `hs.to_cone s` is the least cone that includes `s`. -/
lemma to_cone_is_least : is_least { t : convex_cone E | s ⊆ t } (hs.to_cone s) :=
begin
  refine ⟨hs.subset_to_cone, λ t ht x hx, _⟩,
  rcases hs.mem_to_cone.1 hx with ⟨c, hc, y, hy, rfl⟩,
  exact t.smul_mem hc (ht hy)
end

lemma to_cone_eq_Inf : hs.to_cone s = Inf { t : convex_cone E | s ⊆ t } :=
hs.to_cone_is_least.is_glb.Inf_eq.symm

end convex

lemma convex_hull_to_cone_is_least (s : set E) :
  is_least {t : convex_cone E | s ⊆ t} ((convex_convex_hull 𝕜 s).to_cone _) :=
begin
  convert (convex_convex_hull 𝕜 s).to_cone_is_least,
  ext t,
  exact ⟨λ h, convex_hull_min h t.convex, λ h, subset.trans (subset_convex_hull s) h⟩
end

lemma convex_hull_to_cone_eq_Inf (s : set E) :
  (convex_convex_hull 𝕜 s).to_cone _ = Inf {t : convex_cone E | s ⊆ t} :=
(convex_hull_to_cone_is_least s).is_glb.Inf_eq.symm

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

namespace riesz_extension

open submodule

variables (s : convex_cone E) (f : linear_pmap ℝ E ℝ)

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
          mul_inv_cancel (ne_of_lt hr), one_smul, sub_eq_add_neg, neg_smul, neg_neg],
      replace := le_c (r⁻¹ • ⟨x, hx⟩) this,
      rwa [← mul_le_mul_left (neg_pos.2 hr), ← neg_mul_eq_neg_mul, ← neg_mul_eq_neg_mul,
        neg_le_neg_iff, f.map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel (ne_of_lt hr),
        one_mul] at this },
    { subst r,
      simp only [zero_smul, add_zero] at hzs ⊢,
      apply nonneg,
      exact hzs },
    { have : r⁻¹ • x + y ∈ s,
        by rwa [← s.smul_mem_iff hr, smul_add, smul_smul, mul_inv_cancel (ne_of_gt hr), one_smul],
      replace := c_le (r⁻¹ • ⟨x, hx⟩) this,
      rwa [← mul_le_mul_left hr, f.map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel (ne_of_gt hr), one_mul] at this } }
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
    { exact ⟨r, hr, le_of_lt hqr, ne_of_gt hqr⟩ },
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
theorem riesz_extension (s : convex_cone E) (f : linear_pmap ℝ E ℝ)
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
  let s : convex_cone (E × ℝ) :=
  { carrier := {p : E × ℝ | N p.1 ≤ p.2 },
    smul_mem' := λ c hc p hp,
      calc N (c • p.1) = c * N p.1 : N_hom c hc p.1
      ... ≤ c * p.2 : mul_le_mul_of_nonneg_left hp (le_of_lt hc),
    add_mem' := λ x hx y hy, le_trans (N_add _ _) (add_le_add hx hy) },
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

/-!
### The dual cone
-/
section dual

variables {H : Type*} [inner_product_space ℝ H] (s t : set H)
open_locale real_inner_product_space

/-- The dual cone is the cone consisting of all points `y` such that for
all points `x` in a given set `0 ≤ ⟪ x, y ⟫`. -/
noncomputable def set.inner_dual_cone (s : set H) : convex_cone H :=
{ carrier := { y | ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ },
  smul_mem' := λ c hc y hy x hx,
  begin
    rw real_inner_smul_right,
    exact mul_nonneg (le_of_lt hc) (hy x hx)
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
