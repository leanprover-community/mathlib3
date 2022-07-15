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
-- although then we would need only one set of `simp` lemmas.
-- What the hell is going on with `continuous_linear_map` and `prod` in structures?
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

variables {𝕜 A}

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
    central :=
            begin
            intros x y,
            simp,
            rw add_mul,
            rw mul_add,
            repeat {rw central _ _},
            end } }

@[simp]
lemma left_add (a b : 𝓜(𝕜, A)) : (a + b).left = a.left + b.left := rfl

@[simp]
lemma right_add (a b : 𝓜(𝕜, A)) : (a + b).right = a.right + b.right := rfl

instance : has_mul 𝓜(𝕜, A) :=
{ mul := λ a b,
  { left := a.left.comp b.left,
    right := b.right.comp a.right,
    central :=
              begin
              intros x y,
              simp,
              repeat
              {rw central _ _},
              end } }

@[simp]
lemma left_mul (a b : 𝓜(𝕜, A)) : (a * b).left = a.left.comp b.left := rfl

@[simp]
lemma right_mul (a b : 𝓜(𝕜, A)) : (a * b).right = b.right.comp a.right := rfl

instance : has_smul 𝕜 𝓜(𝕜, A) :=
{ smul := λ k a,
  { left := k • a.left,
    right := k • a.right,
    central :=
              begin
              intros x y,
              simp,
              repeat {rw central _ _},
              rw mul_smul_comm _ _ _,
              rw smul_mul_assoc,
              rw central _ _,
              exact _inst_4,
              end } }

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
    central :=
              begin
              intros x y,
              simp,
              have ha := a.central,
              specialize ha (star y) (star x),
              have P := congr_arg star ha,
              simp only [star_mul , star_star] at P,
              symmetry,
              exact P,
              end } }

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
    central :=
              begin
              intros x y,
              simp,
              apply central,
              end } }

@[simp]
lemma neg_left (a : 𝓜(𝕜, A)) : (-a).left = -a.left := rfl
@[simp]
lemma neg_right (a : 𝓜(𝕜, A)) : (-a).right = -a.right := rfl

instance : has_sub 𝓜(𝕜, A) :=
{ sub := λ a b,
  { left := a.left - b.left,
    right := a.right - b.right,
  central :=
            begin
            intros x y,
            simp,
            rw sub_mul,
            rw mul_sub,
            repeat { rw central _ _ },
            end } }

@[simp]
lemma sub_left (a b : 𝓜(𝕜, A)) : (a - b).left = a.left - b.left := rfl
@[simp]
lemma sub_right (a b : 𝓜(𝕜, A)) : (a - b).right = a.right - b.right := rfl

instance : add_comm_group 𝓜(𝕜, A) :=
{ add := (+),
  add_assoc := λ a b c, by {ext; exact add_assoc _ _ _},
  zero := 0,
  zero_add := λ a, by {ext; exact zero_add _},
  add_zero := λ a, by {ext; exact add_zero _},
  neg := λ x, -x,
  sub := λ x y,  x - y,
  sub_eq_add_neg := λ a b, by {ext; exact sub_eq_add_neg _ _},
  add_left_neg := λ a, by {ext; exact add_left_neg _},
  add_comm := λ a b, by {ext; exact add_comm _ _} }

instance : ring 𝓜(𝕜, A) :=
{ one := 1,
  mul := λ x y, x * y,
  mul_assoc := λ a b c, by {ext; simp only [left_mul, right_mul, continuous_linear_map.coe_comp']},
  one_mul := λ a, by {ext; simp only [left_mul, one_left, right_mul, one_right, continuous_linear_map.coe_comp', function.comp_app, continuous_linear_map.one_apply]},
  mul_one := λ a, by {ext; simp only [left_mul, one_left, right_mul, one_right, continuous_linear_map.coe_comp', function.comp_app, continuous_linear_map.one_apply]},
  left_distrib :=
                  begin
                  intros a b c,
                  ext,
                  simp,
                  apply map_add,
                  simp,
                  tauto,
                  end,
  right_distrib :=
                  begin
                  intros a b c,
                  ext,
                  simp,
                  tauto,
                  simp,
                  apply map_add,
                  end,
  .. double_centralizer.add_comm_group }

-- this might already require `A` to be a `cstar_ring`, for otherwise I don't think we'll be able
-- to prove `norm_right` below.
noncomputable instance : has_norm 𝓜(𝕜, A) :=
{ norm := λ a, ∥a.left∥ }

open_locale nnreal
variables [cstar_ring A]

lemma norm_left (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.left∥ := rfl
lemma norm_right (a : 𝓜(𝕜, A)) : ∥a∥ = ∥a.right∥ :=
      begin
      have h1 : ∀ b, ∥ a.left b ∥₊ ^ 2 ≤  ∥ a.right ∥₊ * ∥ a.left ∥₊ * ∥ b ∥₊ ^ 2,
      { intros b,

            calc ∥ a.left b ∥₊ ^ 2 = ∥ a.left b ∥₊ * ∥ a.left b ∥₊ : by ring
            ...                   = ∥ star (a.left b) * (a.left b) ∥₊  : (cstar_ring.nnnorm_star_mul_self).symm
            ...                 = ∥ a.right (star (a.left b)) * b ∥₊ : by rw a.central _ b
            ...                 ≤ ∥ a.right (star (a.left b))∥₊ * ∥ b ∥₊ : nnnorm_mul_le _ _
            ...                 ≤ ∥ a.right ∥₊ * ∥ star (a.left b) ∥₊ * ∥ b ∥₊ : mul_le_mul_right' (a.right.le_op_nnnorm _) _
            ...                 = ∥ a.right ∥₊ * ∥ a.left b ∥₊ * ∥ b ∥₊ : by rw nnnorm_star
            ...                 ≤ ∥ a.right ∥₊ * ∥ a.left ∥₊ * ∥ b ∥₊  * ∥ b ∥₊ :
                                                                          begin
                                                                          apply mul_le_mul_right',
                                                                          rw mul_assoc,
                                                                          apply mul_le_mul_left',
                                                                          apply a.left.le_op_nnnorm,
                                                                          end
            ...                 = ∥ a.right ∥₊ * ∥ a.left ∥₊ * ∥ b ∥₊ ^ 2 : by ring, } ,
            have h2 : ∀ b, ∥ a.left b ∥ ^ 2 ≤  ∥ a.right ∥ * ∥ a.left ∥ * ∥ b ∥ ^ 2 :=
                                        begin
                                        intro b,
                                        have h2 := h1 b,
                                        exact_mod_cast nnreal.coe_mono h2,
                                        end,
      sorry
      end
end double_centralizer
