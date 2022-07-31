/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import tactic.field_simp
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universes u v w

noncomputable theory

open_locale unit_interval

namespace continuous_map

/--This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*-/
lemma continuous_map.continuous_prod (α β γ : Type*) [topological_space α] [topological_space β]
  [locally_compact_space β] [topological_space γ] :
  continuous (λ x : C(α, β) × C(β, γ), x.2.comp x.1) :=
begin
  apply continuous_generated_from,
  rintros M ⟨K, hK, U, hU, hM⟩,
  apply is_open_iff_forall_mem_open.mpr,
  rintros ⟨φ₀, ψ₀⟩ H,
  simp only [set.mem_preimage, hM, compact_open.gen, set.image_subset_iff, coe_comp,
    set.mem_set_of_eq, @set.preimage_comp _ _ _ φ₀ ψ₀ _, to_fun_eq_coe] at H,
  obtain ⟨L, ⟨hL, hL_left, hL_right⟩⟩ := exists_compact_superset' (hK.image φ₀.2)
    (hU.preimage ψ₀.2) (set.image_subset_iff.mpr H),
  set V : (set C(α, β)) := { φ | φ '' K ⊆ interior L } with def_V,
  have hV := continuous_map.is_open_gen hK is_open_interior,
  set W : (set C(β, γ)) := {ψ | ψ '' L ⊆ U } with def_W,
  have hW := continuous_map.is_open_gen hL hU,
  use V ×ˢ W,
  split,
  { rintros ⟨φ, ψ⟩ ⟨hφ, hψ⟩,
    simp only [set.mem_preimage, hM, compact_open.gen, set.image_subset_iff, coe_comp,
    set.mem_set_of_eq],
    rw [← set.image_subset_iff, set.image_comp],
    exact (set.image_subset ψ $ set.subset.trans hφ interior_subset).trans hψ },
  exact ⟨is_open.prod hV hW, set.mem_prod.mpr
    ⟨by {simp only [set.mem_set_of_eq], exact hL_left},
    by {simp only [set.mem_set_of_eq, set.image_subset_iff], exact hL_right}⟩⟩,
end

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
(left_Hmul_e : continuous_map.homotopy_rel
  ⟨(λ a : X, Hmul (e, a)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
  ⟨id, continuous_id'⟩
  {e})
(right_Hmul_e : continuous_map.homotopy_rel
  ⟨(λ x : X, Hmul (x, e)), (continuous.comp cont'(continuous_id'.prod_mk continuous_const))⟩
  ⟨id, continuous_id'⟩
  {e})


notation ` ∨ `:65 := H_space.Hmul

section topological_group_H_space

instance topological_group_H_space (G : Type u) [topological_space G] [group G]
  [topological_group G] : H_space G :=
{ Hmul := function.uncurry has_mul.mul,
  e := 1,
  cont' := continuous_mul,
  Hmul_e_e := by {simp only [function.uncurry_apply_pair, mul_one]},
  left_Hmul_e := by {simp only [function.uncurry_apply_pair, one_mul],
    exact continuous_map.homotopy_rel.refl _ _ },
  right_Hmul_e := by {simp only [function.uncurry_apply_pair, mul_one],
    exact continuous_map.homotopy_rel.refl _ _ },
}

lemma Hmul_e {G : Type u} [topological_space G] [group G] [topological_group G] :
  (1 : G) = H_space.e := rfl

end topological_group_H_space

section path_space_H_space

variables {X : Type u} [topological_space X]

notation ` Ω(` x `)` := path x x

lemma continuous_coe (x : X) : continuous (coe : Ω(x) → C(↥I, X)) := continuous_induced_dom

variable {x : X}

@[simp, continuity]
lemma continuous_to_Ω_if_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x)} :
  continuous (↑g : Y → C(I,X)) → continuous g := λ h, continuous_induced_rng h


@[simp, continuity]
lemma continuous_to_Ω_if_continuous_uncurry {Y : Type u} [topological_space Y]
  {g : Y → Ω(x)} : continuous (λ p : Y × I, g p.1 p.2) → continuous g :=
  λ h, continuous_induced_rng $ continuous_of_continuous_uncurry ↑g h


lemma continuous_prod_first_half (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I,
  x.1.1.extend (2 * x.2)) :=
begin
  let η := (λ p : Ω(x) × I, p.1.extend (2 * p.2)),
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc _ _ zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod _ _ _).comp (continuous.prod.mk Cproj)).comp
      continuous_induced_dom,
    have h_right := (continuous_const.mul continuous_id').comp
    (@continuous_induced_dom _ _ (coe : I → ℝ) _),
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)) },
  replace H := (homeomorph.comp_continuous_iff' $ homeomorph.prod_assoc Ω(x) _ _).mpr
    (H.comp $ continuous_snd),
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

lemma closure_I_mem (θ t : I) : t ∈ closure {s : ↥I | (s : ℝ) ≤ θ / 2} ↔ (t : ℝ) ≤ θ /2 :=
  by {rw [(is_closed_le continuous_induced_dom continuous_const).closure_eq, set.mem_set_of_eq],
    apply_instance}

lemma interior_I_not_mem (θ t : I) : t ∉ interior {s : ↥I | (s : ℝ) ≤ θ / 2} ↔ (θ / 2 : ℝ) ≤ t :=
begin
  let half_θ : I := ⟨θ / 2, ⟨div_nonneg θ.2.1 zero_le_two, (half_le_self θ.2.1).trans θ.2.2⟩ ⟩,
  have : {s : ↥I | (s : ℝ) ≤ θ / 2} = set.Iic half_θ := rfl,
  have H_ne : (set.Ioi half_θ).nonempty := ⟨1, by {simpa only [set.mem_Ioi, ← subtype.coe_lt_coe,
    subtype.coe_mk, unit_interval.coe_one, @div_lt_one ℝ _ θ _ zero_lt_two]
      using lt_of_le_of_lt θ.2.2 one_lt_two,}⟩,
  simp only [this, interior_Iic' H_ne, not_lt, subtype.coe_mk, set.mem_set_of_eq,
    ← subtype.coe_lt_coe, ← set.Iio_def],
end

lemma Hmul_cont (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.1.trans x.1.2 x.2) :=
begin
  apply continuous.piecewise,
  { rintros ⟨_, t⟩ ⟨h_left, h_right⟩,
    have h_eq : (λ (i : (path x x × path x x) × I), (i.snd : ℝ) ≤ (1 / 2)) =
      (set.univ) ×ˢ {s : I | (s : ℝ) ≤ (1 / 2)},
    { ext p,
      change (p.2 : ℝ) ≤ 1 / 2 ↔ p ∈ (@set.univ (Ω(x) × Ω(x)) ×ˢ {s : I | (s : ℝ) ≤ 1 / 2}),
      simp only [set.mem_prod, set.mem_univ, set.mem_set_of_eq, true_and] },
    erw h_eq at h_left h_right,
    simp only [closure_prod_eq, closure_univ, set.prod_mk_mem_set_prod_eq, set.mem_univ,
      true_and] at h_left,
    simp only [interior_prod_eq, interior_univ, set.prod_mk_mem_set_prod_eq, set.mem_univ, true_and]
       at h_right,
    have H := eq_of_ge_of_not_gt ((interior_I_not_mem 1 t).mp h_right)
      (not_lt_of_le $ (closure_I_mem 1 t).mp h_left),
    simp only [H, unit_interval.coe_one, extend, mul_inv_cancel_of_invertible, set.Icc_extend_right, unit_interval.mk_one,
      path.target, sub_self, set.Icc_extend_left, unit_interval.mk_zero, path.source, one_div] },
  exacts [continuous_prod_first_half x, continuous_prod_second_half x],
end

def delayed_id {x : X} (θ : I) (γ : Ω(x)) : Ω(x) :=
{ to_fun := λ t, if  (t : ℝ) ≤ θ / 2 then x
                 else γ.extend ((2*t - θ)/(2 - θ)),
  continuous_to_fun :=
  begin
    apply continuous.piecewise,
    { rintros t ⟨h_left, h_right⟩,
      simp only [eq_of_ge_of_not_gt ((interior_I_not_mem θ t).mp h_right)
      (not_lt_of_le $ (closure_I_mem θ t).mp h_left)],
      field_simp },
    exacts [continuous_const, (continuous_extend γ).comp ((continuous_const.mul continuous_induced_dom).sub
      continuous_const).div_const ],
  end,
  source' :=
  begin
    simp only [unit_interval.coe_zero, path.source, mul_zero, zero_sub, ite_eq_left_iff, not_le],
    intro h,
    contrapose! h,
    exact div_nonneg θ.2.1 zero_le_two,
  end,
  target' :=
  begin
    simp only [unit_interval.coe_one, path.target, mul_one, ite_eq_left_iff, not_le],
    intro,
    rw div_self,
    { simpa only [div_self, set.right_mem_Icc, zero_le_one, extend_extends, unit_interval.mk_one, to_fun_eq_coe,
      coe_to_continuous_map] using γ.3 },
    { linarith },
  end }

lemma aux_mem_I {t θ : I} : 0 ≤ ((2 : ℝ) * t - θ)/(2 - θ) ∧ ((2 : ℝ) * t - θ)/(2 - θ) ≤ 1 := sorry

lemma continuous_delayed_id {x : X} : continuous (λ p : I × Ω(x), delayed_id p.1 p.2) :=
begin
  apply continuous_to_Ω_if_continuous_uncurry,
  let Q : I × I → I := λ ⟨θ, t⟩, if (t : ℝ) ≤ θ / 2 then 0
                                else ⟨(2 * t - θ)/(2 - θ), aux_mem_I⟩,
  have hQ : continuous Q, sorry,
  let Q₀ : C(I × I, I) := ⟨Q, hQ⟩,
  let Q₁ : C((I × I) × Ω(x), I × Ω(x)) := ⟨λ p, ⟨Q₀ p.1, p.2⟩, (continuous.comp hQ
    continuous_fst).prod_mk continuous_snd⟩,
  let F₀ : I × Ω(x) → X := λ p, p.2 p.1,
  have hF₀ : continuous F₀, sorry,
  -- let F : C(Ω(x) × I, X) := ⟨F₀, hF₀⟩,
  -- have := continuous_swap.comp Q₁.2,
  have hQ₂ := (homeomorph.comp_continuous_iff' $ (homeomorph.prod_assoc I I Ω(x)).symm).mpr Q₁.2,
  have hQ₃ := hQ₂.comp continuous_swap,
  convert hF₀.comp hQ₃,
  -- refl,
  ext,
  dsimp [delayed_id, prod.swap, Q],
  split_ifs,
  -- refl,
  simp_rw [if_pos h],
  -- simp only,
end

instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' := continuous_to_Ω_if_to_C $ continuous_of_continuous_uncurry _ $ Hmul_cont x,
  Hmul_e_e := refl_trans_refl,
  left_Hmul_e :=
  begin
    -- existsi
    let φ : C(I × Ω(x), Ω(x)) := ⟨λ p, delayed_id p.1 p.2, continuous_delayed_id⟩,
    use φ,
    intro γ,
    -- simp only [continuous_map.coe_mk],
    funext,
    -- dsimp [path.refl],
    ext t,
    dsimp [path.refl, delayed_id],
    have temp : (ite ((t : ℝ) ≤ 0 / 2) x (γ.extend ((2 * ↑t - 0) / (2 - 0)))) = x, sorry,
    rw temp,
    sorry,
    -- simp,
    -- simp [path.has_coe_to_fun],
    -- convert,
    -- simp only,
    -- have := (delayed_id 0 γ).source',
    -- erw this,

    -- let φ : I × Ω(x) → (I → X) := λ p t, if  ≤ (p.1)/2 then p.2 t,
    --                       else p.2 ((2t - p.1)/(2 - p.2)),
  end,
  right_Hmul_e := sorry}

end path_space_H_space

end H_space
