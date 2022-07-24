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
lemma continuous_to_Ω_iff_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x) } :
 continuous g ↔ continuous (↑g : Y → C(I,X)) :=
 ⟨λ h, continuous.comp (continuous_coe x) h, λ h, continuous_induced_rng h⟩

lemma continuous_to_Ω_iff_uncurry {Y : Type u} [topological_space Y]
[locally_compact_space Y] {g : Y → Ω(x)} : continuous g ↔ continuous (λ p : Y × I, g p.1 p.2) :=
  iff.intro ((λ h, (continuous_to_C_iff_uncurry Y I X ↑g).mp (continuous_to_Ω_iff_to_C.mp h)))
  (λ h, continuous_to_Ω_iff_to_C.mpr ((continuous_to_C_iff_uncurry Y I X ↑g).mpr h))


lemma Hmul_Ω_cont (x : X) (γ γ' : Ω(x)) : continuous (λ t, γ.trans γ' t) :=
begin
  exact (trans γ γ').continuous,
end

lemma Hmul_Ω_cont' (x : X) : continuous (λ t, λ φ : Ω(x) × Ω(x), φ.1.trans φ.2 t) :=
begin
  exact continuous_pi (λ (i : path x x × path x x), (i.fst.trans i.snd).continuous),
end

lemma continuous_map.continuous_prod (X Y Z : Type*) [topological_space X] [topological_space Y] [locally_compact_space Y] [topological_space Z] : continuous (λ x : C(X, Y) × C(Y, Z), x.2.comp x.1) :=
begin
  sorry,
end


lemma continuous_prod_first_half (x : X) : continuous (λ x : I × Ω(x) × Ω(x), x.2.1.extend (2 * x.1.1)) :=
begin
  set η := (λ p : Ω(x) × I, p.1.extend (2 * p.2)) with hη,
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc 0 1 zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod ℝ I X).comp (continuous.prod.mk Cproj)).comp continuous_induced_dom,
    have h_right := (continuous_const.mul continuous_id').comp (@continuous_induced_dom _ _ (coe : I → ℝ) _),
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)) },
  replace H := (H.comp continuous_swap).comp (@continuous_fst _ Ω(x) _ _),
  exact (homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm).mpr H,
end

lemma continuous_prod_second_half (x : X) : continuous (λ x : I × Ω(x) × Ω(x), x.2.2.extend (2 * x.1.1 - 1)) :=
begin
  set η := (λ p : Ω(x) × I, p.1.extend (2 * p.2 -1 )) with hη,
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc 0 1 zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod ℝ I X).comp (continuous.prod.mk Cproj)).comp continuous_induced_dom,
    have aux : continuous (λ x : ℝ, 2 * x -1 ),
      from (continuous_const.mul continuous_id').sub continuous_const,
    have h_right := aux.comp (@continuous_induced_dom _ _ (coe : I → ℝ) _),
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)),
    },
  replace H := (H.comp continuous_swap).comp (@continuous_fst _ Ω(x) _ _),
  replace H := (homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm).mpr H,
  exact H.comp (continuous.prod_map (continuous_id) continuous_swap),
end

lemma Hmul_Ω_cont₁ (x : X) : continuous (λ x : I × Ω(x) × Ω(x), x.2.1.trans x.2.2 x.1) :=
begin
  apply continuous.piecewise,
  { sorry },
  exacts [continuous_prod_first_half x, continuous_prod_second_half x],
end

instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' :=
  begin
    sorry,
    -- apply continuous_to_Ω_iff_uncurry.mpr,
    -- apply (Hmul_Ω_cont₁ x),
  end,
  Hmul_e_e := sorry,
  left_Hmul_e := sorry,
  right_Hmul_e := sorry}


end H_space
