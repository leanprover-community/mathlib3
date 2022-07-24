/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

-- import analysis.complex.circle
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universes u v w

noncomputable theory

open_locale unit_interval

namespace continuous_map

lemma continuous_to_C_iff_uncurry (X Y Z : Type*) [topological_space X]
  [topological_space Y] [locally_compact_space Y] [topological_space Z] (g : X → C(Y, Z)) :
  continuous g ↔ continuous (λ p : X × Y, g p.1 p.2) :=  iff.intro
(λ h, continuous_uncurry_of_continuous ⟨_, h⟩) (λ h, continuous_of_continuous_uncurry _ h)

end continuous_map

namespace path

open continuous_map

variables (X : Type u) [topological_space X]

instance (x y : X) : has_coe (path x y) C(I, X) := ⟨λ γ, γ.1⟩

instance (x y : X) : topological_space (path x y) := topological_space.induced (coe : _ → C(↥I, X))
  continuous_map.compact_open

end path

namespace H_space

open path continuous_map

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : ∀ x : X,
  continuous_map.homotopy_rel
  ⟨(λ a : X, Hmul (e, a)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨id, continuous_id'⟩
  {e})
(right_Hmul_e : ∀ x : X,
  continuous_map.homotopy_rel
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨id, continuous_id'⟩
  {e})


notation ` ∨ `:65 := H_space.Hmul

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G] : H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := λ _, by {simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl _ _ },
  right_Hmul_e := λ _, by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _ },
}

@[simp]
lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

-- open circle

-- instance S0_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := infer_instance
-- instance S1_H_space : H_space circle := infer_instance
-- instance S3_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry
-- instance S7_H_space : H_space (metric.sphere (0 : ℝ × ℝ) 1) := sorry

variables {X : Type u} [topological_space X]

notation ` Ω(` x `)` := path x x

@[simp]
lemma continuous_coe (x : X) : continuous (coe : Ω(x) → C(↥I, X)) := continuous_induced_dom

@[ext]
lemma ext_loop (x : X) (γ γ' : Ω(x) ) : γ = γ' ↔ (∀ t, γ t = γ' t) :=
begin
  split;
  intro h,
  { simp only [h, eq_self_iff_true, forall_const] },
  { rw [← function.funext_iff] at h, exact path.ext h }
end

variable {x : X}

@[simp]
lemma continuous_to_Ω_if_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x)} :
 continuous (↑g : Y → C(I,X)) → continuous g := λ h, continuous_induced_rng h

lemma continuous_to_Ω_iff_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x) } :
 continuous g ↔ continuous (↑g : Y → C(I,X)) :=
 ⟨λ h, continuous.comp (continuous_coe x) h, λ h, continuous_to_Ω_if_to_C h⟩

lemma continuous_to_Ω_iff_uncurry {Y : Type u} [topological_space Y]
[locally_compact_space Y] {g : Y → Ω(x)} : continuous g ↔ continuous (λ p : Y × I, g p.1 p.2) :=
  iff.intro ((λ h, (continuous_to_C_iff_uncurry Y I X ↑g).mp (continuous_to_Ω_iff_to_C.mp h)))
  (λ h, continuous_to_Ω_iff_to_C.mpr ((continuous_to_C_iff_uncurry Y I X ↑g).mpr h))


lemma continuous_map.continuous_prod (X Y Z : Type*) [topological_space X] [topological_space Y] [locally_compact_space Y] [topological_space Z] : continuous (λ x : C(X, Y) × C(Y, Z), x.2.comp x.1) :=
begin
  sorry,
end


lemma continuous_prod_first_half (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.1.extend (2 * x.2)) :=
begin
  let η := (λ p : Ω(x) × I, p.1.extend (2 * p.2)),
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc _ _ zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod _ _ _).comp (continuous.prod.mk Cproj)).comp continuous_induced_dom,
    have h_right := (continuous_const.mul continuous_id').comp
    (@continuous_induced_dom _ _ (coe : I → ℝ) _),
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)) },
  replace H := (homeomorph.comp_continuous_iff' $ homeomorph.prod_assoc Ω(x) _ _).mpr (H.comp $ continuous_snd),
  exact (H.comp $ continuous.prod_map continuous_swap continuous_id),
end

lemma continuous_prod_second_half (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.2.extend (2 * x.2 - 1)) :=
begin
  let η := (λ p : Ω(x) × I, p.1.extend (2 * p.2 - 1)),
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc 0 1 zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod _ _ _).comp (continuous.prod.mk Cproj)).comp continuous_induced_dom,
    have aux : continuous (λ x : ℝ, 2 * x -1 ),
      from (continuous_const.mul continuous_id').sub continuous_const,
    have h_right := aux.comp continuous_induced_dom,
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)) },
  exact (homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm).mp (H.comp continuous_snd),
end

lemma Hmul_cont (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.1.trans x.1.2 x.2) :=
begin
  apply continuous.piecewise,
  { rintros ⟨_, t⟩ ⟨h_left, h_right⟩,
    have h_eq : (λ (i : (path x x × path x x) × I), (i.snd : ℝ) ≤ (1 / 2)) =  (set.univ) ×ˢ {s : I | (s : ℝ) ≤ (1 / 2)},
    { ext p,
      change (p.2 : ℝ) ≤ 1 / 2 ↔ p ∈ ((@set.univ (Ω(x) × Ω(x))) ×ˢ {s : I | (s : ℝ) ≤ 1 / 2}),
      simp only [set.mem_prod, set.mem_univ, set.mem_set_of_eq, true_and] },
    erw h_eq at h_left h_right,
    simp only [closure_prod_eq, closure_univ, set.prod_mk_mem_set_prod_eq, set.mem_univ,
      true_and] at h_left,
    simp only [interior_prod_eq, interior_univ, set.prod_mk_mem_set_prod_eq, set.mem_univ, true_and] at h_right,

    have H : (t : ℝ) = 1 / 2,
    rw closure_induced at h_left,
    -- haveI : order_closed_topology I, sorry,
    have := @is_closed_le' ℝ _ _ _ (1 / 2),
    unfold coe at h_left,
    -- simp * at *,
    sorry,

    simp only [H, extend, mul_inv_cancel_of_invertible, set.Icc_extend_right, unit_interval.mk_one,
      path.target, sub_self, set.Icc_extend_left, unit_interval.mk_zero, path.source, one_div] },
  exacts [continuous_prod_first_half x, continuous_prod_second_half x],
end

instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' := continuous_to_Ω_if_to_C $ continuous_of_continuous_uncurry _ $ Hmul_cont x,
  Hmul_e_e := refl_trans_refl,
  left_Hmul_e := sorry,
  right_Hmul_e := sorry}


end H_space
