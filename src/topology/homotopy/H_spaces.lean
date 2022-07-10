/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

-- import analysis.complex.circle
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universe u

noncomputable theory

open path continuous_map

open_locale unit_interval

namespace H_space

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨(λ x : X, Hmul (e, x)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  {e})
(right_Hmul_e : ∀ x : X,
  @continuous_map.homotopy_rel (X) (X) _ _
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  {e})

notation ` ∨ `:65 := H_space.Hmul

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G]: H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ ,
  right_Hmul_e := λ _, continuous_map.homotopy_rel.refl _ _ }

@[simp]
lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

-- open circle

-- instance S0_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := infer_instance
-- instance S1_H_space : H_space circle := infer_instance
-- instance S3_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S7_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry

variables {X : Type u} [topological_space X]

def loop_space (x : X) : Type u := {f : C(I, X) // f 0 = x ∧ f 1 = x}

instance (x : X) : topological_space (loop_space x) := by {exact subtype.topological_space}

instance (x : X) : has_coe (loop_space x) C(I, X) := {coe := λ g, ⟨g.1⟩}

notation ` Ω ` := loop_space

variable (x : X)


-- lemma loop.continuous_eval : (γ : Ω x) (t : I) : continuous (λ x, γ t) :=
-- example : locally_compact_space I := infer_instance





lemma continuous_to_loop_space_iff (Y : Type u) [topological_space Y] (g : Y → Ω x) :
  continuous g ↔ continuous (λ y : Y, λ t : I, g y t) :=
begin
sorry;{
  split,
  -- {
    intro h,
    -- suffices hh : continuous (λ p : I × Y, g y t),
    have := continuous_uncurry,
    let f := λ t, λ y, g y t,
    have hf : continuous f, sorry,
    let G₀ : (Y → C(I, X)) := (λ y, (g y).1),
    have hG₀ : continuous G₀, sorry,
    let G : C(Y, C(I, X)) := ⟨G₀, hG₀⟩,
    have h_unc := @continuous_of_continuous_uncurry Y I X _ _ _ G _,
    have h1 := @continuous_map.continuous_curry,
    refine continuous_pi (λ (t : I), _),
    have hprod:= @continuous.prod.mk I C(I, X) _ _ t,
    -- have hprodu := @continuous_uncurry_of_continious

    -- continuity,
    -- continuit
    -- simp [continuous.comp],
    -- suggest,
    -- ext x,
    -- have h_cur := @continuous_uncurry_of_continuous Y I X _ _ _ _ G,-- (λ t : I, λ y : Y, g y t),

  -- },
}
end


-- instance loop_space_is_H_space (x : X) : H_space (loop_space x) :=
-- { Hmul := sorry,
--   e := sorry,
--   cont' := sorry,
--   Hmul_e_e := sorry,
--   left_Hmul_e := sorry,
--   right_Hmul_e := sorry}


end H_space
