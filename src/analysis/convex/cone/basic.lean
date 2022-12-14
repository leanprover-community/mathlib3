/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
import analysis.inner_product_space.projection

/-!
# Convex cones

In a `𝕜`-module `E`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `complete_lattice`, and define their
images (`convex_cone.map`) and preimages (`convex_cone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `convex.to_cone` to be the minimal cone that includes a given convex set.

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

We prove the following theorems:
* `convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem`:
  This variant of the
  [hyperplane separation theorem](https://en.wikipedia.org/wiki/Hyperplane_separation_theorem)
  states that given a nonempty, closed, convex cone `K` in a complete, real inner product space `H`
  and a point `b` disjoint from it, there is a vector `y` which separates `b` from `K` in the sense
  that for all points `x` in `K`, `0 ≤ ⟪x, y⟫_ℝ` and `⟪y, b⟫_ℝ < 0`. This is also a geometric
  interpretation of the
  [Farkas lemma](https://en.wikipedia.org/wiki/Farkas%27_lemma#Geometric_interpretation).
* `convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self`:
  The `inner_dual_cone` of the `inner_dual_cone` of a nonempty, closed, convex cone is itself.

## Implementation notes

While `convex 𝕜` is a predicate on sets, `convex_cone 𝕜 E` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/


open set linear_map
open_locale classical pointwise

variables {𝕜 E F G : Type*}

/-! ### Definition of `convex_cone` and basic properties -/

section definitions
variables (𝕜 E) [ordered_semiring 𝕜]

/-- A convex cone is a subset `s` of a `𝕜`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
structure convex_cone [add_comm_monoid E] [has_smul 𝕜 E] :=
(carrier : set E)
(smul_mem' : ∀ ⦃c : 𝕜⦄, 0 < c → ∀ ⦃x : E⦄, x ∈ carrier → c • x ∈ carrier)
(add_mem' : ∀ ⦃x⦄ (hx : x ∈ carrier) ⦃y⦄ (hy : y ∈ carrier), x + y ∈ carrier)

end definitions

variables {𝕜 E}

namespace convex_cone
section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E]

section has_smul
variables [has_smul 𝕜 E] (S T : convex_cone 𝕜 E)

instance : set_like (convex_cone 𝕜 E) E :=
{ coe := carrier,
  coe_injective' := λ S T h, by cases S; cases T; congr' }

@[simp] lemma coe_mk {s : set E} {h₁ h₂} : ↑(@mk 𝕜 _ _ _ _ s h₁ h₂) = s := rfl

@[simp] lemma mem_mk {s : set E} {h₁ h₂ x} : x ∈ @mk 𝕜 _ _ _ _ s h₁ h₂ ↔ x ∈ s := iff.rfl

/-- Two `convex_cone`s are equal if they have the same elements. -/
@[ext] theorem ext {S T : convex_cone 𝕜 E} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

lemma smul_mem {c : 𝕜} {x : E} (hc : 0 < c) (hx : x ∈ S) : c • x ∈ S := S.smul_mem' hc hx

lemma add_mem ⦃x⦄ (hx : x ∈ S) ⦃y⦄ (hy : y ∈ S) : x + y ∈ S := S.add_mem' hx hy

instance : add_mem_class (convex_cone 𝕜 E) E :=
{ add_mem := λ c a b ha hb, add_mem c ha hb }

instance : has_inf (convex_cone 𝕜 E) :=
⟨λ S T, ⟨S ∩ T, λ c hc x hx, ⟨S.smul_mem hc hx.1, T.smul_mem hc hx.2⟩,
  λ x hx y hy, ⟨S.add_mem hx.1 hy.1, T.add_mem hx.2 hy.2⟩⟩⟩

@[simp] lemma coe_inf : ((S ⊓ T : convex_cone 𝕜 E) : set E) = ↑S ∩ ↑T := rfl

lemma mem_inf {x} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

instance : has_Inf (convex_cone 𝕜 E) :=
⟨λ S, ⟨⋂ s ∈ S, ↑s,
  λ c hc x hx, mem_bInter $ λ s hs, s.smul_mem hc $ mem_Inter₂.1 hx s hs,
  λ x hx y hy, mem_bInter $ λ s hs, s.add_mem (mem_Inter₂.1 hx s hs) (mem_Inter₂.1 hy s hs)⟩⟩

@[simp] lemma coe_Inf (S : set (convex_cone 𝕜 E)) : ↑(Inf S) = ⋂ s ∈ S, (s : set E) := rfl

lemma mem_Inf {x : E} {S : set (convex_cone 𝕜 E)} : x ∈ Inf S ↔ ∀ s ∈ S, x ∈ s := mem_Inter₂

@[simp] lemma coe_infi {ι : Sort*} (f : ι → convex_cone 𝕜 E) : ↑(infi f) = ⋂ i, (f i : set E) :=
by simp [infi]

lemma mem_infi {ι : Sort*} {x : E} {f : ι → convex_cone 𝕜 E} : x ∈ infi f ↔ ∀ i, x ∈ f i :=
mem_Inter₂.trans $ by simp

variables (𝕜)

instance : has_bot (convex_cone 𝕜 E) := ⟨⟨∅, λ c hc x, false.elim, λ x, false.elim⟩⟩

lemma mem_bot (x : E) : x ∈ (⊥ : convex_cone 𝕜 E) = false := rfl

@[simp] lemma coe_bot : ↑(⊥ : convex_cone 𝕜 E) = (∅ : set E) := rfl

instance : has_top (convex_cone 𝕜 E) := ⟨⟨univ, λ c hc x hx, mem_univ _, λ x hx y hy, mem_univ _⟩⟩

lemma mem_top (x : E) : x ∈ (⊤ : convex_cone 𝕜 E) := mem_univ x

@[simp] lemma coe_top : ↑(⊤ : convex_cone 𝕜 E) = (univ : set E) := rfl

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
  .. set_like.partial_order }

instance : inhabited (convex_cone 𝕜 E) := ⟨⊥⟩

end has_smul

section module
variables [module 𝕜 E] (S : convex_cone 𝕜 E)

protected lemma convex : convex 𝕜 (S : set E) :=
convex_iff_forall_pos.2 $ λ x hx y hy a b ha hb _, S.add_mem (S.smul_mem ha hx) (S.smul_mem hb hy)

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

@[simp] lemma mem_map {f : E →ₗ[𝕜] F} {S : convex_cone 𝕜 E} {y : F} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

lemma map_map (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 E) :
  (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image g f S

@[simp] lemma map_id (S : convex_cone 𝕜 E) : S.map linear_map.id = S :=
set_like.coe_injective $ image_id _

/-- The preimage of a convex cone under a `𝕜`-linear map is a convex cone. -/
def comap (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 F) : convex_cone 𝕜 E :=
{ carrier := f ⁻¹' S,
  smul_mem' := λ c hc x hx, by { rw [mem_preimage, f.map_smul c], exact S.smul_mem hc hx },
  add_mem' := λ x hx y hy, by { rw [mem_preimage, f.map_add], exact S.add_mem hx hy } }

@[simp] lemma coe_comap (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 F) : (S.comap f : set E) = f ⁻¹' S := rfl

@[simp] lemma comap_id (S : convex_cone 𝕜 E) : S.comap linear_map.id = S :=
set_like.coe_injective preimage_id

lemma comap_comap (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) (S : convex_cone 𝕜 G) :
  (S.comap g).comap f = S.comap (g.comp f) :=
set_like.coe_injective $ preimage_comp.symm

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
variables [add_comm_monoid E] [has_smul 𝕜 E] (S : convex_cone 𝕜 E)

/-- A convex cone is pointed if it includes `0`. -/
def pointed (S : convex_cone 𝕜 E) : Prop := (0 : E) ∈ S

/-- A convex cone is blunt if it doesn't include `0`. -/
def blunt (S : convex_cone 𝕜 E) : Prop := (0 : E) ∉ S

lemma pointed_iff_not_blunt (S : convex_cone 𝕜 E) : S.pointed ↔ ¬S.blunt :=
⟨λ h₁ h₂, h₂ h₁, not_not.mp⟩

lemma blunt_iff_not_pointed (S : convex_cone 𝕜 E) : S.blunt ↔ ¬S.pointed :=
by rw [pointed_iff_not_blunt, not_not]

lemma pointed.mono {S T : convex_cone 𝕜 E} (h : S ≤ T) : S.pointed → T.pointed := @h _

lemma blunt.anti {S T : convex_cone 𝕜 E} (h : T ≤ S) : S.blunt → T.blunt := (∘ @@h)

end add_comm_monoid

section add_comm_group
variables [add_comm_group E] [has_smul 𝕜 E] (S : convex_cone 𝕜 E)

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

lemma flat.mono {S T : convex_cone 𝕜 E} (h : S ≤ T) : S.flat → T.flat
| ⟨x, hxS, hx, hnxS⟩ := ⟨x, h hxS, hx, h hnxS⟩

lemma salient.anti {S T : convex_cone 𝕜 E} (h : T ≤ S) : S.salient → T.salient :=
λ hS x hxT hx hnT, hS x (h hxT) hx (h hnT)

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

section module
variables [add_comm_monoid E] [module 𝕜 E]

instance : has_zero (convex_cone 𝕜 E) := ⟨⟨0, λ _ _, by simp, λ _, by simp⟩⟩

@[simp] lemma mem_zero (x : E) : x ∈ (0 : convex_cone 𝕜 E) ↔ x = 0 := iff.rfl
@[simp] lemma coe_zero : ((0 : convex_cone 𝕜 E) : set E) = 0 := rfl

lemma pointed_zero : (0 : convex_cone 𝕜 E).pointed := by rw [pointed, mem_zero]

instance : has_add (convex_cone 𝕜 E) := ⟨ λ K₁ K₂,
{ carrier := {z | ∃ (x y : E), x ∈ K₁ ∧ y ∈ K₂ ∧ x + y = z},
  smul_mem' :=
  begin
    rintro c hc _ ⟨x, y, hx, hy, rfl⟩,
    rw smul_add,
    use [c • x, c • y, K₁.smul_mem hc hx, K₂.smul_mem hc hy],
  end,
  add_mem' :=
  begin
    rintro _ ⟨x₁, x₂, hx₁, hx₂, rfl⟩ y ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
    use [x₁ + y₁, x₂ + y₂, K₁.add_mem hx₁ hy₁, K₂.add_mem hx₂ hy₂],
    abel,
  end } ⟩

@[simp] lemma mem_add {K₁ K₂ : convex_cone 𝕜 E} {a : E} :
  a ∈ K₁ + K₂ ↔ ∃ (x y : E), x ∈ K₁ ∧ y ∈ K₂ ∧ x + y = a := iff.rfl

instance : add_zero_class (convex_cone 𝕜 E) :=
⟨0, has_add.add, λ _, by {ext, simp}, λ _, by {ext, simp}⟩

instance : add_comm_semigroup (convex_cone 𝕜 E) :=
{ add := has_add.add,
  add_assoc := λ _ _ _, set_like.coe_injective $ set.add_comm_semigroup.add_assoc _ _ _,
  add_comm := λ _ _, set_like.coe_injective $ set.add_comm_semigroup.add_comm _ _ }

end module
end ordered_semiring

end convex_cone

namespace submodule

/-! ### Submodules are cones -/

section ordered_semiring
variables [ordered_semiring 𝕜]

section add_comm_monoid
variables [add_comm_monoid E] [module 𝕜 E]

/-- Every submodule is trivially a convex cone. -/
def to_convex_cone (S : submodule 𝕜 E) : convex_cone 𝕜 E :=
{ carrier := S,
  smul_mem' := λ c hc x hx, S.smul_mem c hx,
  add_mem' := λ x hx y hy, S.add_mem hx hy }

@[simp] lemma coe_to_convex_cone (S : submodule 𝕜 E) : ↑S.to_convex_cone = (S : set E) := rfl

@[simp] lemma mem_to_convex_cone {x : E} {S : submodule 𝕜 E} : x ∈ S.to_convex_cone ↔ x ∈ S :=
iff.rfl

@[simp] lemma to_convex_cone_le_iff {S T : submodule 𝕜 E} :
  S.to_convex_cone ≤ T.to_convex_cone ↔ S ≤ T :=
iff.rfl

@[simp] lemma to_convex_cone_bot : (⊥ : submodule 𝕜 E).to_convex_cone = 0 := rfl
@[simp] lemma to_convex_cone_top : (⊤ : submodule 𝕜 E).to_convex_cone = ⊤ := rfl

@[simp] lemma to_convex_cone_inf (S T : submodule 𝕜 E) :
  (S ⊓ T).to_convex_cone = S.to_convex_cone ⊓ T.to_convex_cone :=
rfl

@[simp] lemma pointed_to_convex_cone (S : submodule 𝕜 E) : S.to_convex_cone.pointed := S.zero_mem

end add_comm_monoid
end ordered_semiring

end submodule

namespace convex_cone

/-! ### Positive cone of an ordered module -/

section positive_cone
variables (𝕜 E) [ordered_semiring 𝕜] [ordered_add_comm_group E] [module 𝕜 E] [ordered_smul 𝕜 E]

/--
The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module.
-/
def positive : convex_cone 𝕜 E :=
{ carrier := set.Ici 0,
  smul_mem' := λ c hc x (hx : _ ≤ _), smul_nonneg hc.le hx,
  add_mem' := λ x (hx : _ ≤ _) y (hy : _ ≤ _), add_nonneg hx hy }

@[simp] lemma mem_positive {x : E} : x ∈ positive 𝕜 E ↔ 0 ≤ x := iff.rfl
@[simp] lemma coe_positive : ↑(positive 𝕜 E) = set.Ici (0 : E) := rfl

/-- The positive cone of an ordered module is always salient. -/
lemma salient_positive : salient (positive 𝕜 E) :=
λ x xs hx hx', lt_irrefl (0 : E)
  (calc
    0   < x         : lt_of_le_of_ne xs hx.symm
    ... ≤ x + (-x)  : le_add_of_nonneg_right hx'
    ... = 0         : add_neg_self x)

/-- The positive cone of an ordered module is always pointed. -/
lemma pointed_positive : pointed (positive 𝕜 E) := le_refl 0

/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`convex_cone.positive`) being established terminology for the non-negative elements. -/
def strictly_positive : convex_cone 𝕜 E :=
{ carrier := set.Ioi 0,
  smul_mem' := λ c hc x (hx : _ < _), smul_pos hc hx,
  add_mem' := λ x hx y hy, add_pos hx hy }

@[simp] lemma mem_strictly_positive {x : E} : x ∈ strictly_positive 𝕜 E ↔ 0 < x := iff.rfl
@[simp] lemma coe_strictly_positive : ↑(strictly_positive 𝕜 E) = set.Ioi (0 : E) := rfl

lemma positive_le_strictly_positive : strictly_positive 𝕜 E ≤ positive 𝕜 E := λ x, le_of_lt

/-- The strictly positive cone of an ordered module is always salient. -/
lemma salient_strictly_positive : salient (strictly_positive 𝕜 E) :=
(salient_positive 𝕜 E).anti $ positive_le_strictly_positive 𝕜 E

/-- The strictly positive cone of an ordered module is always blunt. -/
lemma blunt_strictly_positive : blunt (strictly_positive 𝕜 E) := lt_irrefl 0

end positive_cone
end convex_cone

/-! ### Cone over a convex set -/

section cone_from_convex
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E]

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
eq.symm $ is_glb.Inf_eq $ is_least.is_glb $ convex_hull_to_cone_is_least s

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
variables (s : convex_cone ℝ E) (f : E →ₗ.[ℝ] ℝ)

/-- Induction step in M. Riesz extension theorem. Given a convex cone `s` in a vector space `E`,
a partially defined linear map `f : f.domain → ℝ`, assume that `f` is nonnegative on `f.domain ∩ p`
and `p + s = E`. If `f` is not defined on the whole `E`, then we can extend it to a larger
submodule without breaking the non-negativity condition. -/
lemma step (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x)
  (dense : ∀ y, ∃ x : f.domain, (x : E) + y ∈ s) (hdom : f.domain ≠ ⊤) :
  ∃ g, f < g ∧ ∀ x : g.domain, (x : E) ∈ s → 0 ≤ g x :=
begin
  obtain ⟨y, -, hy⟩ : ∃ (y : E) (h : y ∈ ⊤), y ∉ f.domain,
    { exact @set_like.exists_of_lt (submodule ℝ E) _ _ _ _ (lt_top_iff_ne_top.2 hdom) },
  obtain ⟨c, le_c, c_le⟩ :
    ∃ c, (∀ x : f.domain, -(x:E) - y ∈ s → f x ≤ c) ∧ (∀ x : f.domain, (x:E) + y ∈ s → c ≤ f x),
  { set Sp := f '' {x : f.domain | (x:E) + y ∈ s},
    set Sn := f '' {x : f.domain | -(x:E) - y ∈ s},
    suffices : (upper_bounds Sn ∩ lower_bounds Sp).nonempty,
      by simpa only [set.nonempty, upper_bounds, lower_bounds, ball_image_iff] using this,
    refine exists_between_of_forall_le (nonempty.image f _) (nonempty.image f (dense y)) _,
    { rcases (dense (-y)) with ⟨x, hx⟩,
      rw [← neg_neg x, add_subgroup_class.coe_neg, ← sub_eq_add_neg] at hx,
      exact ⟨_, hx⟩ },
    rintros a ⟨xn, hxn, rfl⟩ b ⟨xp, hxp, rfl⟩,
    have := s.add_mem hxp hxn,
    rw [add_assoc, add_sub_cancel'_right, ← sub_eq_add_neg, ← add_subgroup_class.coe_sub] at this,
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
      rwa [← mul_le_mul_left (neg_pos.2 hr), neg_mul, neg_mul,
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

theorem exists_top (p : E →ₗ.[ℝ] ℝ)
  (hp_nonneg : ∀ x : p.domain, (x : E) ∈ s → 0 ≤ p x)
  (hp_dense : ∀ y, ∃ x : p.domain, (x : E) + y ∈ s) :
  ∃ q ≥ p, q.domain = ⊤ ∧ ∀ x : q.domain, (x : E) ∈ s → 0 ≤ q x :=
begin
  replace hp_nonneg : p ∈ { p | _ }, by { rw mem_set_of_eq, exact hp_nonneg },
  obtain ⟨q, hqs, hpq, hq⟩ := zorn_nonempty_partial_order₀ _ _ _ hp_nonneg,
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
theorem riesz_extension (s : convex_cone ℝ E) (f : E →ₗ.[ℝ] ℝ)
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
theorem exists_extension_of_le_sublinear (f : E →ₗ.[ℝ] ℝ) (N : E → ℝ)
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
def set.inner_dual_cone (s : set H) : convex_cone ℝ H :=
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

@[simp] lemma mem_inner_dual_cone (y : H) (s : set H) :
  y ∈ s.inner_dual_cone ↔ ∀ x ∈ s, 0 ≤ ⟪ x, y ⟫ := iff.rfl

@[simp] lemma inner_dual_cone_empty : (∅ : set H).inner_dual_cone = ⊤ :=
eq_top_iff.mpr $ λ x hy y, false.elim

/-- Dual cone of the convex cone {0} is the total space. -/
@[simp] lemma inner_dual_cone_zero : (0 : set H).inner_dual_cone = ⊤ :=
eq_top_iff.mpr $ λ x hy y (hy : y = 0), hy.symm ▸ inner_zero_left.ge

/-- Dual cone of the total space is the convex cone {0}. -/
@[simp] lemma inner_dual_cone_univ : (univ : set H).inner_dual_cone = 0 :=
begin
  suffices : ∀ x : H, x ∈ (univ : set H).inner_dual_cone → x = 0,
  { apply set_like.coe_injective,
    exact eq_singleton_iff_unique_mem.mpr ⟨λ x hx, inner_zero_right.ge, this⟩ },
  exact λ x hx, by simpa [←real_inner_self_nonpos] using hx (-x) (mem_univ _),
end

lemma inner_dual_cone_le_inner_dual_cone (h : t ⊆ s) :
  s.inner_dual_cone ≤ t.inner_dual_cone :=
λ y hy x hx, hy x (h hx)

lemma pointed_inner_dual_cone : s.inner_dual_cone.pointed :=
λ x hx, by rw inner_zero_right

/-- The inner dual cone of a singleton is given by the preimage of the positive cone under the
linear map `λ y, ⟪x, y⟫`. -/
lemma inner_dual_cone_singleton (x : H) :
  ({x} : set H).inner_dual_cone = (convex_cone.positive ℝ ℝ).comap (innerₛₗ x) :=
convex_cone.ext $ λ i, forall_eq

lemma inner_dual_cone_union (s t : set H) :
  (s ∪ t).inner_dual_cone = s.inner_dual_cone ⊓ t.inner_dual_cone :=
le_antisymm
  (le_inf (λ x hx y hy, hx _ $ or.inl hy) (λ x hx y hy, hx _ $ or.inr hy))
  (λ x hx y, or.rec (hx.1 _) (hx.2 _))

lemma inner_dual_cone_insert (x : H) (s : set H) :
  (insert x s).inner_dual_cone = set.inner_dual_cone {x} ⊓ s.inner_dual_cone :=
by rw [insert_eq, inner_dual_cone_union]

lemma inner_dual_cone_Union {ι : Sort*} (f : ι → set H) :
  (⋃ i, f i).inner_dual_cone = ⨅ i, (f i).inner_dual_cone :=
begin
  refine le_antisymm (le_infi $ λ i x hx y hy, hx _ $ mem_Union_of_mem _ hy) _,
  intros x hx y hy,
  rw [convex_cone.mem_infi] at hx,
  obtain ⟨j, hj⟩ := mem_Union.mp hy,
  exact hx _ _ hj,
end

lemma inner_dual_cone_sUnion (S : set (set H)) :
  (⋃₀ S).inner_dual_cone = Inf (set.inner_dual_cone '' S) :=
by simp_rw [Inf_image, sUnion_eq_bUnion, inner_dual_cone_Union]

/-- The dual cone of `s` equals the intersection of dual cones of the points in `s`. -/
lemma inner_dual_cone_eq_Inter_inner_dual_cone_singleton :
  (s.inner_dual_cone : set H) = ⋂ i : s, (({i} : set H).inner_dual_cone : set H) :=
by rw [←convex_cone.coe_infi, ←inner_dual_cone_Union, Union_of_singleton_coe]

lemma is_closed_inner_dual_cone : is_closed (s.inner_dual_cone : set H) :=
begin
  -- reduce the problem to showing that dual cone of a singleton `{x}` is closed
  rw inner_dual_cone_eq_Inter_inner_dual_cone_singleton,
  apply is_closed_Inter,
  intros x,

  -- the dual cone of a singleton `{x}` is the preimage of `[0, ∞)` under `inner x`
  have h : ↑({x} : set H).inner_dual_cone = (inner x : H → ℝ) ⁻¹' set.Ici 0,
  { rw [inner_dual_cone_singleton, convex_cone.coe_comap, convex_cone.coe_positive,
      innerₛₗ_apply_coe] },

  -- the preimage is closed as `inner x` is continuous and `[0, ∞)` is closed
  rw h,
  exact is_closed_Ici.preimage (by continuity),
end

lemma convex_cone.pointed_of_nonempty_of_is_closed (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) : K.pointed :=
begin
  obtain ⟨x, hx⟩ := ne,
  let f : ℝ → H := (• x),

  -- f (0, ∞) is a subset of K
  have fI : f '' set.Ioi 0 ⊆ (K : set H),
  { rintro _ ⟨_, h, rfl⟩,
    exact K.smul_mem (set.mem_Ioi.1 h) hx },

  -- closure of f (0, ∞) is a subset of K
  have clf : closure (f '' set.Ioi 0) ⊆ (K : set H) := hc.closure_subset_iff.2 fI,

  -- f is continuous at 0 from the right
  have fc : continuous_within_at f (set.Ioi (0 : ℝ)) 0 :=
    (continuous_id.smul continuous_const).continuous_within_at,

  -- 0 belongs to the closure of the f (0, ∞)
  have mem₀ := fc.mem_closure_image (by rw [closure_Ioi (0 : ℝ), mem_Ici]),

  -- as 0 ∈ closure f (0, ∞) and closure f (0, ∞) ⊆ K, 0 ∈ K.
  have f₀ : f 0 = 0 := zero_smul ℝ x,
  simpa only [f₀, convex_cone.pointed, ← set_like.mem_coe] using mem_of_subset_of_mem clf mem₀,
end

section complete_space
variables [complete_space H]

/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem convex_cone.hyperplane_separation_of_nonempty_of_is_closed_of_nmem (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) {b : H} (disj : b ∉ K) :
  ∃ (y : H), (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 :=
begin
  -- let `z` be the point in `K` closest to `b`
  obtain ⟨z, hzK, infi⟩ := exists_norm_eq_infi_of_complete_convex ne hc.is_complete K.convex b,

  -- for any `w` in `K`, we have `⟪b - z, w - z⟫_ℝ ≤ 0`
  have hinner := (norm_eq_infi_iff_real_inner_le_zero K.convex hzK).1 infi,

  -- set `y := z - b`
  use z - b,

  split,
  { -- the rest of the proof is a straightforward calculation
    rintros x hxK,
    specialize hinner _ (K.add_mem hxK hzK),
    rwa [add_sub_cancel, real_inner_comm, ← neg_nonneg, neg_eq_neg_one_mul,
         ← real_inner_smul_right, neg_smul, one_smul, neg_sub] at hinner },
  { -- as `K` is closed and non-empty, it is pointed
    have hinner₀ := hinner 0 (K.pointed_of_nonempty_of_is_closed ne hc),

    -- the rest of the proof is a straightforward calculation
    rw [zero_sub, inner_neg_right, right.neg_nonpos_iff] at hinner₀,
    have hbz : b - z ≠ 0 := by { rw sub_ne_zero, contrapose! hzK, rwa ← hzK },
    rw [← neg_zero, lt_neg, ← neg_one_mul, ← real_inner_smul_left, smul_sub, neg_smul, one_smul,
      neg_smul, neg_sub_neg, one_smul],
    calc 0 < ⟪b - z, b - z⟫_ℝ : lt_of_not_le ((iff.not real_inner_self_nonpos).2 hbz)
    ... = ⟪b - z, b - z⟫_ℝ + 0 : (add_zero _).symm
    ... ≤ ⟪b - z, b - z⟫_ℝ + ⟪b - z, z⟫_ℝ : add_le_add rfl.ge hinner₀
    ... = ⟪b - z, b - z + z⟫_ℝ : inner_add_right.symm
    ... = ⟪b - z, b⟫_ℝ : by rw sub_add_cancel },
end

/-- The inner dual of inner dual of a non-empty, closed convex cone is itself.  -/
theorem convex_cone.inner_dual_cone_of_inner_dual_cone_eq_self (K : convex_cone ℝ H)
  (ne : (K : set H).nonempty) (hc : is_closed (K : set H)) :
  ((K : set H).inner_dual_cone : set H).inner_dual_cone = K :=
begin
  ext x,
  split,
  { rw [mem_inner_dual_cone, ← set_like.mem_coe],
    contrapose!,
    exact K.hyperplane_separation_of_nonempty_of_is_closed_of_nmem ne hc },
  { rintro hxK y h,
    specialize h x hxK,
    rwa real_inner_comm },
end

end complete_space
end dual
