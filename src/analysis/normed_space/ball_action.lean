/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.normed.field.unit_ball
import analysis.normed_space.basic

/-!
# Multiplicative actions of/on balls and spheres

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/
open metric set
variables {𝕜 𝕜' E : Type*} [normed_field 𝕜] [normed_field 𝕜']
  [seminormed_add_comm_group E] [normed_space 𝕜 E] [normed_space 𝕜' E] {r : ℝ}

section closed_ball

instance mul_action_closed_ball_ball : mul_action (closed_ball (0 : 𝕜) 1) (ball (0 : E) r) :=
{ smul := λ c x, ⟨(c : 𝕜) • x, mem_ball_zero_iff.2 $
    by simpa only [norm_smul, one_mul]
      using mul_lt_mul' (mem_closed_ball_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2)
        (norm_nonneg _) one_pos⟩,
  one_smul := λ x, subtype.ext $ one_smul 𝕜 _,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul _ _ _ }

instance has_continuous_smul_closed_ball_ball :
  has_continuous_smul (closed_ball (0 : 𝕜) 1) (ball (0 : E) r) :=
⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mul_action_closed_ball_closed_ball :
  mul_action (closed_ball (0 : 𝕜) 1) (closed_ball (0 : E) r) :=
{ smul := λ c x, ⟨(c : 𝕜) • x, mem_closed_ball_zero_iff.2 $
    by simpa only [norm_smul, one_mul]
      using mul_le_mul (mem_closed_ball_zero_iff.1 c.2) (mem_closed_ball_zero_iff.1 x.2)
        (norm_nonneg _) zero_le_one⟩,
  one_smul := λ x, subtype.ext $ one_smul 𝕜 _,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul _ _ _ }

instance has_continuous_smul_closed_ball_closed_ball :
  has_continuous_smul (closed_ball (0 : 𝕜) 1) (closed_ball (0 : E) r) :=
⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

end closed_ball

section sphere

instance mul_action_sphere_ball : mul_action (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
{ smul := λ c x, inclusion sphere_subset_closed_ball c • x,
  one_smul := λ x, subtype.ext $ one_smul _ _,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul _ _ _ }

instance has_continuous_smul_sphere_ball :
  has_continuous_smul (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mul_action_sphere_closed_ball : mul_action (sphere (0 : 𝕜) 1) (closed_ball (0 : E) r) :=
{ smul := λ c x, inclusion sphere_subset_closed_ball c • x,
  one_smul := λ x, subtype.ext $ one_smul _ _,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul _ _ _ }

instance has_continuous_smul_sphere_closed_ball :
  has_continuous_smul (sphere (0 : 𝕜) 1) (closed_ball (0 : E) r) :=
⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

instance mul_action_sphere_sphere : mul_action (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
{ smul := λ c x, ⟨(c : 𝕜) • x, mem_sphere_zero_iff_norm.2 $
    by rw [norm_smul, mem_sphere_zero_iff_norm.1 c.coe_prop, mem_sphere_zero_iff_norm.1 x.coe_prop,
      one_mul]⟩,
  one_smul := λ x, subtype.ext $ one_smul _ _,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul _ _ _ }

instance has_continuous_smul_sphere_sphere :
  has_continuous_smul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
⟨(continuous_subtype_val.fst'.smul continuous_subtype_val.snd').subtype_mk _⟩

end sphere

section is_scalar_tower

variables [normed_algebra 𝕜 𝕜'] [is_scalar_tower 𝕜 𝕜' E]

instance is_scalar_tower_closed_ball_closed_ball_closed_ball :
  is_scalar_tower (closed_ball (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_closed_ball_closed_ball_ball :
  is_scalar_tower (closed_ball (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_closed_ball_closed_ball :
  is_scalar_tower (sphere (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_closed_ball_ball :
  is_scalar_tower (sphere (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_closed_ball :
  is_scalar_tower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_ball :
  is_scalar_tower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_sphere_sphere :
  is_scalar_tower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

instance is_scalar_tower_sphere_ball_ball :
  is_scalar_tower (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance is_scalar_tower_closed_ball_ball_ball :
  is_scalar_tower (closed_ball (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨λ a b c, subtype.ext $ smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

end is_scalar_tower

section smul_comm_class

variables [smul_comm_class 𝕜 𝕜' E]

instance smul_comm_class_closed_ball_closed_ball_closed_ball :
  smul_comm_class (closed_ball (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_closed_ball_closed_ball_ball :
  smul_comm_class (closed_ball (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_closed_ball_closed_ball :
  smul_comm_class (sphere (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_closed_ball_ball :
  smul_comm_class (sphere (0 : 𝕜) 1) (closed_ball (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_ball_ball [normed_algebra 𝕜 𝕜'] :
  smul_comm_class (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

instance smul_comm_class_sphere_sphere_closed_ball :
  smul_comm_class (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closed_ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_sphere_ball :
  smul_comm_class (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

instance smul_comm_class_sphere_sphere_sphere :
  smul_comm_class (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
⟨λ a b c, subtype.ext $ smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

end smul_comm_class

variables (𝕜) [char_zero 𝕜]

lemma ne_neg_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : sphere (0:E) r) : x ≠ - x :=
λ h, ne_zero_of_mem_sphere hr x ((self_eq_neg 𝕜 _).mp (by { conv_lhs {rw h}, simp }))

lemma ne_neg_of_mem_unit_sphere (x : sphere (0:E) 1) : x ≠ - x :=
ne_neg_of_mem_sphere 𝕜 one_ne_zero x
