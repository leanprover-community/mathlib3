/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.isometry

/-!
# Group actions by isometries

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two typeclasses:

- `has_isometric_smul M X` says that `M` multiplicatively acts on a (pseudo extended) metric space
  `X` by isometries;
- `has_isometric_vadd` is an additive version of `has_isometric_smul`.

We also prove basic facts about isometric actions and define bundled isometries
`isometry_equiv.const_mul`, `isometry_equiv.mul_left`, `isometry_equiv.mul_right`,
`isometry_equiv.div_left`, `isometry_equiv.div_right`, and `isometry_equiv.inv`, as well as their
additive versions.

If `G` is a group, then `has_isometric_smul G G` means that `G` has a left-invariant metric while
`has_isometric_smul Gᵐᵒᵖ G` means that `G` has a right-invariant metric. For a commutative group,
these two notions are equivalent. A group with a right-invariant metric can be also represented as a
`normed_group`.
-/

open set
open_locale ennreal pointwise

universes u v w

variables (M : Type u) (G : Type v) (X : Type w)

/-- An additive action is isometric if each map `x ↦ c +ᵥ x` is an isometry. -/
class has_isometric_vadd [pseudo_emetric_space X] [has_vadd M X] : Prop :=
(isometry_vadd [] : ∀ c : M, isometry ((+ᵥ) c : X → X))

/-- A multiplicative action is isometric if each map `x ↦ c • x` is an isometry. -/
@[to_additive] class has_isometric_smul [pseudo_emetric_space X] [has_smul M X] : Prop :=
(isometry_smul [] : ∀ c : M, isometry ((•) c : X → X))

export has_isometric_vadd (isometry_vadd) has_isometric_smul (isometry_smul)

@[priority 100, to_additive]
instance has_isometric_smul.to_has_continuous_const_smul [pseudo_emetric_space X] [has_smul M X]
  [has_isometric_smul M X] : has_continuous_const_smul M X :=
⟨λ c, (isometry_smul X c).continuous⟩

@[priority 100, to_additive]
instance has_isometric_smul.opposite_of_comm [pseudo_emetric_space X] [has_smul M X]
  [has_smul Mᵐᵒᵖ X] [is_central_scalar M X] [has_isometric_smul M X] :
  has_isometric_smul Mᵐᵒᵖ X :=
⟨λ c x y, by simpa only [← op_smul_eq_smul] using (isometry_smul X c.unop x y)⟩

variables {M G X}

section emetric

variables [pseudo_emetric_space X] [group G] [mul_action G X] [has_isometric_smul G X]

@[simp, to_additive] lemma edist_smul_left [has_smul M X] [has_isometric_smul M X]
  (c : M) (x y : X) :
  edist (c • x) (c • y) = edist x y :=
isometry_smul X c x y

@[to_additive] lemma isometry_mul_left [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul M M] (a : M) : isometry ((*) a) :=
isometry_smul M a

@[simp, to_additive] lemma edist_mul_left [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul M M] (a b c : M) : edist (a * b) (a * c) = edist b c :=
isometry_mul_left a b c

@[to_additive] lemma isometry_mul_right [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a : M) : isometry (λ x, x * a) :=
isometry_smul M (mul_opposite.op a)

@[simp, to_additive] lemma edist_mul_right [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : edist (a * c) (b * c) = edist a b :=
isometry_mul_right c a b

@[simp, to_additive] lemma edist_div_right [div_inv_monoid M] [pseudo_emetric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : edist (a / c) (b / c) = edist a b :=
by simp only [div_eq_mul_inv, edist_mul_right]

@[simp, to_additive] lemma edist_inv_inv [pseudo_emetric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b : G) : edist a⁻¹ b⁻¹ = edist a b :=
by rw [← edist_mul_left a, ← edist_mul_right _ _ b, mul_right_inv, one_mul,
  inv_mul_cancel_right, edist_comm]

@[to_additive] lemma isometry_inv [pseudo_emetric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] : isometry (has_inv.inv : G → G) :=
edist_inv_inv

@[to_additive] lemma edist_inv [pseudo_emetric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (x y : G) : edist x⁻¹ y = edist x y⁻¹ :=
by rw [← edist_inv_inv, inv_inv]

@[simp, to_additive] lemma edist_div_left [pseudo_emetric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b c : G) : edist (a / b) (a / c) = edist b c :=
by rw [div_eq_mul_inv, div_eq_mul_inv, edist_mul_left, edist_inv_inv]

namespace isometry_equiv

/-- If a group `G` acts on `X` by isometries, then `isometry_equiv.const_smul` is the isometry of
`X` given by multiplication of a constant element of the group. -/
@[to_additive "If an additive group `G` acts on `X` by isometries, then `isometry_equiv.const_vadd`
is the isometry of `X` given by addition of a constant element of the group.", simps to_equiv apply]
def const_smul (c : G) : X ≃ᵢ X :=
{ to_equiv := mul_action.to_perm c,
  isometry_to_fun := isometry_smul X c }

@[simp, to_additive]
lemma const_smul_symm (c : G) : (const_smul c : X ≃ᵢ X).symm = const_smul c⁻¹ := ext $ λ _, rfl

variables [pseudo_emetric_space G]

/-- Multiplication `y ↦ x * y` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ x + y` as an `isometry_equiv`.", simps apply to_equiv]
def mul_left [has_isometric_smul G G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.mul_left c,
  isometry_to_fun := edist_mul_left c }

@[simp, to_additive] lemma mul_left_symm [has_isometric_smul G G] (x : G) :
  (mul_left x).symm = isometry_equiv.mul_left x⁻¹ :=
const_smul_symm x --ext $ λ y, rfl

/-- Multiplication `y ↦ y * x` as an `isometry_equiv`. -/
@[to_additive "Addition `y ↦ y + x` as an `isometry_equiv`.", simps apply to_equiv]
def mul_right [has_isometric_smul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.mul_right c,
  isometry_to_fun := λ a b, edist_mul_right a b c }

@[simp, to_additive] lemma mul_right_symm [has_isometric_smul Gᵐᵒᵖ G] (x : G) :
  (mul_right x).symm = mul_right x⁻¹ :=
ext $ λ y, rfl

/-- Division `y ↦ y / x` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ y - x` as an `isometry_equiv`.", simps apply to_equiv]
def div_right [has_isometric_smul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.div_right c,
  isometry_to_fun := λ a b, edist_div_right a b c }

@[simp, to_additive] lemma div_right_symm [has_isometric_smul Gᵐᵒᵖ G] (c : G) :
  (div_right c).symm = mul_right c :=
ext $ λ y, rfl

variables [has_isometric_smul G G] [has_isometric_smul Gᵐᵒᵖ G]

/-- Division `y ↦ x / y` as an `isometry_equiv`. -/
@[to_additive "Subtraction `y ↦ x - y` as an `isometry_equiv`.", simps apply symm_apply to_equiv]
def div_left (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.div_left c,
  isometry_to_fun := edist_div_left c }

variable (G)

/-- Inversion `x ↦ x⁻¹` as an `isometry_equiv`. -/
@[to_additive "Negation `x ↦ -x` as an `isometry_equiv`.", simps apply to_equiv]
def inv : G ≃ᵢ G :=
{ to_equiv := equiv.inv G,
  isometry_to_fun := edist_inv_inv }

@[simp, to_additive] lemma inv_symm : (inv G).symm = inv G := rfl

end isometry_equiv

namespace emetric

@[simp, to_additive] lemma smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
  c • ball x r = ball (c • x) r :=
(isometry_equiv.const_smul c).image_emetric_ball _ _

@[simp, to_additive] lemma preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
  ((•) c) ⁻¹' ball x r = ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_ball]

@[simp, to_additive] lemma smul_closed_ball (c : G) (x : X) (r : ℝ≥0∞) :
  c • closed_ball x r = closed_ball (c • x) r :=
(isometry_equiv.const_smul c).image_emetric_closed_ball _ _

@[simp, to_additive] lemma preimage_smul_closed_ball (c : G) (x : X) (r : ℝ≥0∞) :
  ((•) c) ⁻¹' closed_ball x r = closed_ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_closed_ball]

variables [pseudo_emetric_space G]

@[simp, to_additive]
lemma preimage_mul_left_ball [has_isometric_smul G G] (a b : G) (r : ℝ≥0∞) :
  ((*) a) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
preimage_smul_ball a b r

@[simp, to_additive]
lemma preimage_mul_right_ball [has_isometric_smul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
  (λ x, x * a) ⁻¹' ball b r = ball (b / a) r :=
by { rw div_eq_mul_inv, exact preimage_smul_ball (mul_opposite.op a) b r }

@[simp, to_additive]
lemma preimage_mul_left_closed_ball [has_isometric_smul G G] (a b : G) (r : ℝ≥0∞) :
  ((*) a) ⁻¹' closed_ball b r = closed_ball (a⁻¹ * b) r :=
preimage_smul_closed_ball a b r

@[simp, to_additive]
lemma preimage_mul_right_closed_ball [has_isometric_smul Gᵐᵒᵖ G] (a b : G) (r : ℝ≥0∞) :
  (λ x, x * a) ⁻¹' closed_ball b r = closed_ball (b / a) r :=
by { rw div_eq_mul_inv, exact preimage_smul_closed_ball (mul_opposite.op a) b r }

end emetric

end emetric

@[simp, to_additive]
lemma dist_smul [pseudo_metric_space X] [has_smul M X] [has_isometric_smul M X]
  (c : M) (x y : X) : dist (c • x) (c • y) = dist x y :=
(isometry_smul X c).dist_eq x y

@[simp, to_additive]
lemma nndist_smul [pseudo_metric_space X] [has_smul M X] [has_isometric_smul M X]
  (c : M) (x y : X) : nndist (c • x) (c • y) = nndist x y :=
(isometry_smul X c).nndist_eq x y

@[simp, to_additive]
lemma dist_mul_left [pseudo_metric_space M] [has_mul M] [has_isometric_smul M M]
  (a b c : M) : dist (a * b) (a * c) = dist b c :=
dist_smul a b c

@[simp, to_additive]
lemma nndist_mul_left [pseudo_metric_space M] [has_mul M] [has_isometric_smul M M]
  (a b c : M) : nndist (a * b) (a * c) = nndist b c :=
nndist_smul a b c

@[simp, to_additive] lemma dist_mul_right [has_mul M] [pseudo_metric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : dist (a * c) (b * c) = dist a b :=
dist_smul (mul_opposite.op c) a b

@[simp, to_additive]
lemma nndist_mul_right [pseudo_metric_space M] [has_mul M] [has_isometric_smul Mᵐᵒᵖ M]
  (a b c : M) : nndist (a * c) (b * c) = nndist a b :=
nndist_smul (mul_opposite.op c) a b

@[simp, to_additive] lemma dist_div_right [div_inv_monoid M] [pseudo_metric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : dist (a / c) (b / c) = dist a b :=
by simp only [div_eq_mul_inv, dist_mul_right]

@[simp, to_additive] lemma nndist_div_right [div_inv_monoid M] [pseudo_metric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : nndist (a / c) (b / c) = nndist a b :=
by simp only [div_eq_mul_inv, nndist_mul_right]

@[simp, to_additive]
lemma dist_inv_inv [group G] [pseudo_metric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b : G) : dist a⁻¹ b⁻¹ = dist a b :=
(isometry_equiv.inv G).dist_eq a b

@[simp, to_additive]
lemma nndist_inv_inv [group G] [pseudo_metric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
(isometry_equiv.inv G).nndist_eq a b

@[simp, to_additive]
lemma dist_div_left [group G] [pseudo_metric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b c : G) : dist (a / b) (a / c) = dist b c :=
by simp [div_eq_mul_inv]

@[simp, to_additive]
lemma nndist_div_left [group G] [pseudo_metric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b c : G) : nndist (a / b) (a / c) = nndist b c :=
by simp [div_eq_mul_inv]

namespace metric

variables [pseudo_metric_space X] [group G] [mul_action G X] [has_isometric_smul G X]

@[simp, to_additive] lemma smul_ball (c : G) (x : X) (r : ℝ) :
  c • ball x r = ball (c • x) r :=
(isometry_equiv.const_smul c).image_ball _ _

@[simp, to_additive] lemma preimage_smul_ball (c : G) (x : X) (r : ℝ) :
  ((•) c) ⁻¹' ball x r = ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_ball]

@[simp, to_additive] lemma smul_closed_ball (c : G) (x : X) (r : ℝ) :
  c • closed_ball x r = closed_ball (c • x) r :=
(isometry_equiv.const_smul c).image_closed_ball _ _

@[simp, to_additive] lemma preimage_smul_closed_ball (c : G) (x : X) (r : ℝ) :
  ((•) c) ⁻¹' closed_ball x r = closed_ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_closed_ball]

@[simp, to_additive] lemma smul_sphere (c : G) (x : X) (r : ℝ) :
  c • sphere x r = sphere (c • x) r :=
(isometry_equiv.const_smul c).image_sphere _ _

@[simp, to_additive] lemma preimage_smul_sphere (c : G) (x : X) (r : ℝ) :
  ((•) c) ⁻¹' sphere x r = sphere (c⁻¹ • x) r :=
by rw [preimage_smul, smul_sphere]

variables [pseudo_metric_space G]

@[simp, to_additive]
lemma preimage_mul_left_ball [has_isometric_smul G G] (a b : G) (r : ℝ) :
  ((*) a) ⁻¹' ball b r = ball (a⁻¹ * b) r :=
preimage_smul_ball a b r

@[simp, to_additive]
lemma preimage_mul_right_ball [has_isometric_smul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
  (λ x, x * a) ⁻¹' ball b r = ball (b / a) r :=
by { rw div_eq_mul_inv, exact preimage_smul_ball (mul_opposite.op a) b r }

@[simp, to_additive]
lemma preimage_mul_left_closed_ball [has_isometric_smul G G] (a b : G) (r : ℝ) :
  ((*) a) ⁻¹' closed_ball b r = closed_ball (a⁻¹ * b) r :=
preimage_smul_closed_ball a b r

@[simp, to_additive]
lemma preimage_mul_right_closed_ball [has_isometric_smul Gᵐᵒᵖ G] (a b : G) (r : ℝ) :
  (λ x, x * a) ⁻¹' closed_ball b r = closed_ball (b / a) r :=
by { rw div_eq_mul_inv, exact preimage_smul_closed_ball (mul_opposite.op a) b r }

end metric

section instances

variables {Y : Type*} [pseudo_emetric_space X] [pseudo_emetric_space Y] [has_smul M X]
  [has_isometric_smul M X]

@[to_additive] instance [has_smul M Y] [has_isometric_smul M Y] :
  has_isometric_smul M (X × Y) :=
⟨λ c, (isometry_smul X c).prod_map (isometry_smul Y c)⟩

@[to_additive] instance prod.has_isometric_smul' {N}
  [has_mul M] [pseudo_emetric_space M] [has_isometric_smul M M]
  [has_mul N] [pseudo_emetric_space N] [has_isometric_smul N N] :
  has_isometric_smul (M × N) (M × N) :=
⟨λ c, (isometry_smul M c.1).prod_map (isometry_smul N c.2)⟩

@[to_additive] instance prod.has_isometric_smul'' {N}
  [has_mul M] [pseudo_emetric_space M] [has_isometric_smul Mᵐᵒᵖ M]
  [has_mul N] [pseudo_emetric_space N] [has_isometric_smul Nᵐᵒᵖ N] :
  has_isometric_smul (M × N)ᵐᵒᵖ (M × N) :=
⟨λ c, (isometry_mul_right c.unop.1).prod_map (isometry_mul_right c.unop.2)⟩

@[to_additive] instance units.has_isometric_smul [monoid M] : has_isometric_smul Mˣ X :=
⟨λ c, by convert isometry_smul X (c : M)⟩

@[to_additive] instance : has_isometric_smul M Xᵐᵒᵖ :=
⟨λ c x y, by simpa only using edist_smul_left c x.unop y.unop⟩

@[to_additive] instance ulift.has_isometric_smul : has_isometric_smul (ulift M) X :=
⟨λ c, by simpa only using isometry_smul X c.down⟩

@[to_additive] instance ulift.has_isometric_smul' : has_isometric_smul M (ulift X) :=
⟨λ c x y, by simpa only using edist_smul_left c x.1 y.1⟩

@[to_additive] instance {ι} {X : ι → Type*} [fintype ι] [Π i, has_smul M (X i)]
  [Π i, pseudo_emetric_space (X i)] [∀ i, has_isometric_smul M (X i)] :
  has_isometric_smul M (Π i, X i) :=
⟨λ c, isometry_dcomp (λ i, (•) c) (λ i, isometry_smul (X i) c)⟩

@[to_additive] instance pi.has_isometric_smul' {ι} {M X : ι → Type*} [fintype ι]
  [Π i, has_smul (M i) (X i)] [Π i, pseudo_emetric_space (X i)]
  [∀ i, has_isometric_smul (M i) (X i)] :
  has_isometric_smul (Π i, M i) (Π i, X i) :=
⟨λ c, isometry_dcomp (λ i, (•) (c i)) (λ i, isometry_smul _ _)⟩

@[to_additive] instance pi.has_isometric_smul'' {ι} {M : ι → Type*} [fintype ι]
  [Π i, has_mul (M i)] [Π i, pseudo_emetric_space (M i)] [∀ i, has_isometric_smul (M i)ᵐᵒᵖ (M i)] :
  has_isometric_smul (Π i, M i)ᵐᵒᵖ (Π i, M i) :=
⟨λ c, isometry_dcomp (λ i (x : M i), x * c.unop i) $ λ i, isometry_mul_right _⟩

instance additive.has_isometric_vadd : has_isometric_vadd (additive M) X :=
⟨λ c, isometry_smul X c.to_mul⟩

instance additive.has_isometric_vadd' [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul M M] : has_isometric_vadd (additive M) (additive M) :=
⟨λ c x y, edist_smul_left c.to_mul x.to_mul y.to_mul⟩

instance additive.has_isometric_vadd'' [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] : has_isometric_vadd (additive M)ᵃᵒᵖ (additive M) :=
⟨λ c x y, edist_smul_left (mul_opposite.op c.unop.to_mul) x.to_mul y.to_mul⟩

instance multiplicative.has_isometric_smul {M X} [has_vadd M X] [pseudo_emetric_space X]
  [has_isometric_vadd M X]: has_isometric_smul (multiplicative M) X :=
⟨λ c, isometry_vadd X c.to_add⟩

instance multiplicative.has_isometric_smul' [has_add M] [pseudo_emetric_space M]
  [has_isometric_vadd M M] : has_isometric_smul (multiplicative M) (multiplicative M) :=
⟨λ c x y, edist_vadd_left c.to_add x.to_add y.to_add⟩

instance multiplicative.has_isometric_vadd'' [has_add M] [pseudo_emetric_space M]
  [has_isometric_vadd Mᵃᵒᵖ M] :
  has_isometric_smul (multiplicative M)ᵐᵒᵖ (multiplicative M) :=
⟨λ c x y, edist_vadd_left (add_opposite.op c.unop.to_add) x.to_add y.to_add⟩

end instances
