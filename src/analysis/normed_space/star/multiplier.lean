import analysis.normed_space.star.basic
import analysis.normed_space.operator_norm

/-!
Define the multiplier algebra of a C∗-algebra as the algebra of double centralizers.
A double centralizer is a pair of continuous linear maps `L R : A →L[𝕜] A` satisfying the
intertwining condition `R x * y = x * L y`. These maps
-/

universes u v

variables (𝕜 : Type u) (A : Type v)
  [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A]
  [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A]

-- should we just implement this as a subtype of `(A →L[𝕜] A) × (A →L[𝕜] A)`?
-- I think not because it just makes the linear maps harder to access.
@[ext]
structure double_centralizer : Type v :=
(left : A →L[𝕜] A)
(right : A →L[𝕜] A)
(central : ∀ x y : A, right x * y = x * left y)

namespace continuous_linear_map

-- `lmul` exists, but doesn't work for us because we have *non-unital* ring, so we need this
-- very similar version.
noncomputable def lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] :
  A →L[𝕜] A →L[𝕜] A :=
linear_map.mk_continuous₂
  ({ to_fun := λ a,
     { to_fun := λ b, a * b,
       map_add' := λ x y, mul_add _ _ _,
       map_smul' := λ k x, mul_smul_comm _ _ _ },
     map_add' := λ x y, by { ext, exact add_mul _ _ _ },
     map_smul' := λ k x, by { ext, exact smul_mul_assoc _ _ _ } })
  (1 : ℝ)
  (by simpa only [linear_map.coe_mk, one_mul] using norm_mul_le)

@[simp]
lemma lmul'_apply (x y : A) : lmul' 𝕜 A x y = x * y := rfl

@[simp] lemma op_norm_lmul'_apply_le (x : A) : ∥lmul' 𝕜 A x∥ ≤ ∥x∥ :=
op_norm_le_bound _ (norm_nonneg x) (norm_mul_le x)

lemma lmul_eq_lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] : lmul 𝕜 A = lmul' 𝕜 A := by {ext, refl}

noncomputable def lmul_right' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜]
  [non_unital_normed_ring A] [normed_space 𝕜 A] [smul_comm_class 𝕜 A A] [is_scalar_tower 𝕜 A A] :
  A →L[𝕜] A →L[𝕜] A :=
(lmul' 𝕜 A).flip

@[simp]
lemma lmul_right'_apply (x y : A) : lmul_right' 𝕜 A x y = y * x := rfl

@[simp] lemma op_norm_lmul_right'_apply_le (x : A) : ∥lmul_right' 𝕜 A x∥ ≤ ∥x∥ :=
op_norm_le_bound _ (norm_nonneg x) (λ y, (norm_mul_le y x).trans_eq (mul_comm _ _))

lemma lmul_right_eq_lmul' (𝕜 : Type u) (A : Type v) [nondiscrete_normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] : lmul_right 𝕜 A = lmul_right' 𝕜 A := by {ext, refl}

end continuous_linear_map

localized "notation `𝓜(` 𝕜 `, ` A `)` := double_centralizer 𝕜 A" in multiplier_algebra

namespace double_centralizer

-- this requires approximate units, which we don't yet have, and it's a bit of a mess.
def of_central_funs (L : A → A) (R : A → A) (h : ∀ x y : A, R x * y = x * L y) : 𝓜(𝕜, A) :=
{ left :=
  { to_fun := L,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  right :=
  { to_fun := R,
    map_add' := sorry,
    map_smul' := sorry,
    cont := sorry },
  central := h }

-- probably we don't even need the `cast` map and can just declare the `coe` directly.
noncomputable def cast (a : A) : 𝓜(𝕜, A) :=
{ left := continuous_linear_map.lmul' 𝕜 A a,
  right := continuous_linear_map.lmul_right' 𝕜 A a,
  central := λ x y, mul_assoc _ _ _ }

noncomputable instance : has_coe A 𝓜(𝕜, A) :=
{ coe := double_centralizer.cast 𝕜 A }

@[simp]
lemma coe_left (a : A) : (a : 𝓜(𝕜, A)).left = continuous_linear_map.lmul' 𝕜 A a := rfl

@[simp]
lemma coe_right (a : A) : (a : 𝓜(𝕜, A)).right = continuous_linear_map.lmul_right' 𝕜 A a := rfl

instance : has_add 𝓜(𝕜, A) :=
{ add := λ a b,
  { left := a.left + b.left,
    right := a.right + b.right,
    central := sorry } }

@[simp]
lemma left_add (a b : 𝓜(𝕜, A)) : (a + b).left = a.left + b.left := rfl

@[simp]
lemma right_add (a b : 𝓜(𝕜, A)) : (a + b).right = a.right + b.right := rfl

instance : has_mul 𝓜(𝕜, A) :=
{ mul := λ a b,
  { left := a.left.comp b.left,
    right := b.right.comp a.right,
    central := sorry } }

@[simp]
lemma left_mul (a b : 𝓜(𝕜, A)) : (a * b).left = a.left.comp b.left := rfl

@[simp]
lemma right_mul (a b : 𝓜(𝕜, A)) : (a * b).right = b.right.comp a.right := rfl

instance : has_smul 𝕜 𝓜(𝕜, A) :=
{ smul := λ k a,
  { left := k • a.left,
    right := k • a.right,
    central := sorry } }

instance : has_zero 𝓜(𝕜, A) :=
{ zero :=
  { left := 0,
    right := 0,
    central := λ x y, by simp only [continuous_linear_map.zero_apply, zero_mul, mul_zero] } }

@[simp]
lemma zero_left : (0 : 𝓜(𝕜, A)).left = 0 := rfl
@[simp]
lemma zero_right : (0 : 𝓜(𝕜, A)).right = 0 := rfl

instance : has_one 𝓜(𝕜, A) :=
{ one :=
  { left := 1,
    right := 1,
    central := λ x y, rfl } }

@[simp]
lemma one_left : (1 : 𝓜(𝕜, A)).left = 1 := rfl
@[simp]
lemma one_right : (1 : 𝓜(𝕜, A)).right = 1 := rfl

variables [star_ring 𝕜] [star_ring A] [star_module 𝕜 A] [normed_star_group A]

-- gross: for some reason `starₗᵢ` expects a `[normed_ring A]`
#check @starₗᵢ 𝕜 A _ _


instance : has_star 𝓜(𝕜, A) :=
{ star := λ a,
  { left := ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp
      (a.right.comp ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)),
    right := ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp
      (a.left.comp ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)),
    central := sorry } }

@[simp]
lemma star_left (a : 𝓜(𝕜, A)) : (star a).left = ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp
  (a.right.comp ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)) := rfl

@[simp]
lemma star_right (a : 𝓜(𝕜, A)) : (star a).right = ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A).comp
  (a.left.comp ((starₗᵢ 𝕜 : A ≃ₗᵢ⋆[𝕜] A) : A →L⋆[𝕜] A)) := rfl

instance : has_neg 𝓜(𝕜, A) :=
{ neg := λ a,
  { left := -(a.left),
    right := -(a.right),
    central := sorry } }

@[simp]
lemma neg_left (a : 𝓜(𝕜, A)) : -a.left = -(a.left) := rfl
@[simp]
lemma neg_right (a : 𝓜(𝕜, A)) : -a.right = -(a.right) := rfl

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
  central := sorry } }

@[simp]
lemma sub_left (a b : 𝓜(𝕜, A)) : (a - b).left = a.left - b.left := rfl
@[simp]
lemma sub_right (a b : 𝓜(𝕜, A)) : (a - b).right = a.right - b.right := rfl

-- this might already require `A` to be a `cstar_ring`, for otherwise I don't think we'll be able
-- to prove `norm_right` below.
noncomputable instance : has_norm 𝓜(𝕜, A) :=
{ norm := λ a, ∥a.left∥ }

lemma norm_left (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.left∥ := rfl
lemma norm_right (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.right∥ := sorry -- this uses the cstar property

end double_centralizer
