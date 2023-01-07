/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.isometry

/-!
-/

open set
open_locale ennreal pointwise

universes u v w

variables (M : Type u) (G : Type v) (X : Type w)

class has_isometric_vadd [pseudo_emetric_space X] [has_vadd M X] : Prop :=
(isometry_vadd : ∀ c : M, isometry ((+ᵥ) c : X → X))

@[to_additive] class has_isometric_smul [pseudo_emetric_space X] [has_smul M X] : Prop :=
(isometry_smul: ∀ c : M, isometry ((•) c : X → X))

export has_isometric_vadd (isometry_vadd) has_isometric_smul (isometry_smul)

@[priority 100, to_additive]
instance has_isometric_smul.to_has_continuous_const_smul [pseudo_emetric_space X] [has_smul M X]
  [has_isometric_smul M X] : has_continuous_const_smul M X :=
⟨λ c, (isometry_smul c).continuous⟩

variables {M G X}

section emetric

variables [pseudo_emetric_space X] [group G] [mul_action G X] [has_isometric_smul G X]

@[simp, to_additive] lemma edist_smul_left [has_smul M X] [has_isometric_smul M X]
  (c : M) (x y : X) :
  edist (c • x) (c • y) = edist x y :=
isometry_smul c x y

@[simp, to_additive] lemma edist_mul_left [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul M M] (a b c : M) : edist (a * b) (a * c) = edist b c :=
edist_smul_left a b c

@[simp, to_additive] lemma edist_mul_right [has_mul M] [pseudo_emetric_space M]
  [has_isometric_smul Mᵐᵒᵖ M] (a b c : M) : edist (a * c) (b * c) = edist a b :=
edist_smul_left (mul_opposite.op c) a b

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

namespace isometric

@[to_additive, simps to_equiv apply]
def const_smul (c : G) : X ≃ᵢ X :=
{ to_equiv := mul_action.to_perm c,
  isometry_to_fun := isometry_smul c }

@[simp] lemma const_smul_symm (c : G) :
  (isometric.const_smul c : X ≃ᵢ X).symm = isometric.const_smul c⁻¹ :=
by { ext, refl }

variables [pseudo_emetric_space G]

@[to_additive, simps apply to_equiv]
def mul_left [has_isometric_smul G G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.mul_left c,
  isometry_to_fun := edist_mul_left c }

@[to_additive, simps apply to_equiv]
def mul_right [has_isometric_smul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.mul_right c,
  isometry_to_fun := λ a b, edist_mul_right a b c }

@[to_additive, simps apply to_equiv]
def div_right [has_isometric_smul Gᵐᵒᵖ G] (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.div_right c,
  isometry_to_fun := λ a b, edist_div_right a b c }

variables [has_isometric_smul G G] [has_isometric_smul Gᵐᵒᵖ G]

@[to_additive, simps apply to_equiv]
def div_left (c : G) : G ≃ᵢ G :=
{ to_equiv := equiv.div_left c,
  isometry_to_fun := edist_div_left c }

variable (G)

@[to_additive, simps apply to_equiv]
def inv : G ≃ᵢ G :=
{ to_equiv := equiv.inv G,
  isometry_to_fun := edist_inv_inv }

end isometric

namespace emetric

@[simp, to_additive] lemma smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
  c • ball x r = ball (c • x) r :=
(isometric.const_smul c).image_emetric_ball _ _

@[simp, to_additive] lemma preimage_smul_ball (c : G) (x : X) (r : ℝ≥0∞) :
  ((•) c) ⁻¹' ball x r = ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_ball]

@[simp, to_additive] lemma smul_closed_ball (c : G) (x : X) (r : ℝ≥0∞) :
  c • closed_ball x r = closed_ball (c • x) r :=
(isometric.const_smul c).image_emetric_closed_ball _ _

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
(isometry_smul c).dist_eq x y

@[simp, to_additive]
lemma nndist_smul [pseudo_metric_space X] [has_smul M X] [has_isometric_smul M X]
  (c : M) (x y : X) : nndist (c • x) (c • y) = nndist x y :=
(isometry_smul c).nndist_eq x y

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
(isometric.inv G).dist_eq a b

@[simp, to_additive]
lemma nndist_inv_inv [group G] [pseudo_metric_space G] [has_isometric_smul G G]
  [has_isometric_smul Gᵐᵒᵖ G] (a b : G) : nndist a⁻¹ b⁻¹ = nndist a b :=
(isometric.inv G).nndist_eq a b

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
(isometric.const_smul c).image_ball _ _

@[simp, to_additive] lemma preimage_smul_ball (c : G) (x : X) (r : ℝ) :
  ((•) c) ⁻¹' ball x r = ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_ball]

@[simp, to_additive] lemma smul_closed_ball (c : G) (x : X) (r : ℝ) :
  c • closed_ball x r = closed_ball (c • x) r :=
(isometric.const_smul c).image_closed_ball _ _

@[simp, to_additive] lemma preimage_smul_closed_ball (c : G) (x : X) (r : ℝ) :
  ((•) c) ⁻¹' closed_ball x r = closed_ball (c⁻¹ • x) r :=
by rw [preimage_smul, smul_closed_ball]

@[simp, to_additive] lemma smul_sphere (c : G) (x : X) (r : ℝ) :
  c • sphere x r = sphere (c • x) r :=
(isometric.const_smul c).image_sphere _ _

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
