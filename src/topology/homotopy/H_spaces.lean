/-
Copyright (c) 2022 Filippo A. E. Nuccio Mortarino Majno di Capriglio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/
import data.real.basic
import tactic.field_simp
import topology.algebra.order.basic
import topology.compact_open
import topology.homotopy.basic
import topology.homotopy.path

universes u v w

classical theory

noncomputable theory

open_locale unit_interval

namespace continuous_map

/--This is Prop. 9 of Chap. X, §3, №. 4 of Bourbaki's *Topologie Générale*-/
lemma continuous_map.continuous_prod (α β γ : Type*) [topological_space α] [topological_space β]
  [locally_compact_space β] [topological_space γ] :
  continuous (λ x : C(α, β) × C(β, γ), x.2.comp x.1) :=
begin
sorry,--the proof is in `PR #15721`
  -- apply continuous_generated_from,
  -- rintros M ⟨K, hK, U, hU, hM⟩,
  -- apply is_open_iff_forall_mem_open.mpr,
  -- rintros ⟨φ₀, ψ₀⟩ H,
  -- simp only [set.mem_preimage, hM, compact_open.gen, set.image_subset_iff, coe_comp,
  --   set.mem_set_of_eq, @set.preimage_comp _ _ _ φ₀ ψ₀ _, to_fun_eq_coe] at H,
  -- obtain ⟨L, ⟨hL, hL_left, hL_right⟩⟩ := exists_compact_between (hK.image φ₀.2)
  --   (hU.preimage ψ₀.2) (set.image_subset_iff.mpr H),
  -- set V : (set C(α, β)) := { φ | φ '' K ⊆ interior L } with def_V,
  -- have hV := continuous_map.is_open_gen hK is_open_interior,
  -- set W : (set C(β, γ)) := {ψ | ψ '' L ⊆ U } with def_W,
  -- have hW := continuous_map.is_open_gen hL hU,
  -- use V ×ˢ W,
  -- split,
  -- { rintros ⟨φ, ψ⟩ ⟨hφ, hψ⟩,
  --   simp only [set.mem_preimage, hM, compact_open.gen, set.image_subset_iff, coe_comp,
  --   set.mem_set_of_eq],
  --   rw [← set.image_subset_iff, set.image_comp],
  --   exact (set.image_subset ψ $ set.subset.trans hφ interior_subset).trans hψ },
  -- exact ⟨is_open.prod hV hW, set.mem_prod.mpr
  --   ⟨by {simp only [set.mem_set_of_eq], exact hL_left},
  --   by {simp only [set.mem_set_of_eq, set.image_subset_iff], exact hL_right}⟩⟩,
end

end continuous_map

namespace unit_interval

@[simp]
lemma univ_eq_ge_zero : {s : I | 0 ≤ (s : ℝ)} = set.univ :=
begin
  rw set.eq_univ_iff_forall,
  intro,
  simpa only [set.mem_set_of_eq] using nonneg _,
end

@[simp]
lemma univ_eq_le_one : {s : I | (s : ℝ) ≤ 1} = set.univ :=
begin
  rw set.eq_univ_iff_forall,
  intro,
  simpa only [set.mem_set_of_eq] using le_one _,
end

lemma mem_closure_iff {θ : ℝ} {t : I} : t ∈ closure {s : ↥I | (s : ℝ) ≤ θ} ↔ (t : ℝ) ≤ θ :=
  by {rw [(is_closed_le continuous_induced_dom continuous_const).closure_eq, set.mem_set_of_eq],
    apply_instance}

lemma not_mem_interior {θ : ℝ} {t : I} : t ∉ interior {s : ↥I | (s : ℝ) ≤ θ } → θ  ≤ t :=
begin
  -- For `θ = 1` the set `{s : ↥I | (s : ℝ) ≤ θ}` is the whole `I`, whose interior (in the induced
  -- topology) is `I` again, and `t ∉ I` is always false whereas `1 ≤ t` is true for `t = 1`.
  -- So we split the proof in the cases `θ = 1` and `θ ≠ 1`, that is purely interval-theoretical.
  by_cases θ_eq_one : θ = 1,
  { rw [θ_eq_one, univ_eq_le_one, interior_univ],
    tauto, },
  intro h,
  by_cases H : θ ∈ I, -- this must be changed to `θ < 1` (the proof is basically the same) and
  -- then 1 ≤ θ, which becomes `1 < θ` by virtue of `θ_eq_one`, in which case everything is OK
  -- **Actually**, I suspect that the proof for `θ = 1` generalizes to `1 ≤ θ` and therefore we
  -- can reduce the number of splittings.
  { let θI : I := ⟨θ, H⟩,
    have : {s : ↥I | (s : ℝ) ≤ θ} = set.Iic θI := rfl,
    have H_ne : (set.Ioi θI).nonempty := ⟨1, _⟩,
    simpa only [this, interior_Iic' H_ne, ← set.Iio_def, set.mem_set_of_eq, not_lt,
      ← subtype.coe_le_coe] using h,
    simp only [set.mem_Ioi, ← subtype.coe_lt_coe],
    apply lt_of_le_of_ne H.2 θ_eq_one},
  by_cases H1 : θ < 0,
  { exact (le_of_lt $ lt_of_lt_of_le H1 t.2.1) },
  { replace H1 : 1 < θ,
    simpa only [set.mem_Icc, not_le, not_lt.mp H1, true_and] using H,
    contrapose! h,
    suffices : {s : ↥I | (s : ℝ) ≤ θ} = set.univ,
    simp only [this, interior_univ],
    rw set.eq_univ_iff_forall,
    intro s,
    simpa only [set.mem_set_of_eq] using (le_of_lt $ lt_of_le_of_lt s.2.2 H1) },
end

lemma mem_frontier {θ : ℝ} {t : I} : t ∈ frontier (λ i : I, (i : ℝ) ≤ θ) → (t : ℝ)
  = θ := λ ⟨h_left, h_right⟩, by {simp only [eq_of_ge_of_not_gt (not_mem_interior
    h_right) (not_lt_of_le $ mem_closure_iff.mp h_left)]}

end unit_interval

namespace path

open continuous_map path

variables {X : Type u} [topological_space X]

instance {x y : X} : has_coe (path x y) C(I, X) := ⟨λ γ, γ.1⟩

instance {x y : X} : topological_space (path x y) := topological_space.induced (coe : _ → C(↥I, X))
  continuous_map.compact_open

lemma continuous_eval {x y : X} : continuous (λ p : I × (path x y), p.2 p.1) :=
  (continuous_eval'.comp (continuous.prod_map (continuous_induced_dom) (@continuous_id I _))).comp
    continuous_swap

end path

namespace H_space

open path continuous_map

class H_space (X : Type u) [topological_space X]  :=
(Hmul : X × X → X)
(e : X)
(cont' : continuous Hmul)
(Hmul_e_e : Hmul (e, e) = e)
(left_Hmul_e : continuous_map.homotopy_rel
  ⟨id, continuous_id'⟩
  ⟨(λ a : X, Hmul (e, a)), (continuous.comp cont' (continuous_const.prod_mk continuous_id'))⟩
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

open unit_interval path

variables {X : Type u} [topological_space X]

notation ` Ω(` x `)` := path x x

variable {x : X}

@[simp, continuity]
lemma continuous_to_Ω_if_to_C {Y : Type u} [topological_space Y] {g : Y → Ω(x)} :
  continuous (↑g : Y → C(I,X)) → continuous g := λ h, continuous_induced_rng.mpr h

@[simp, continuity]
lemma continuous_to_Ω_if_continuous_uncurry {Y : Type u} [topological_space Y]
  {g : Y → Ω(x)} : continuous (λ p : Y × I, g p.1 p.2) → continuous g :=
  λ h, continuous_induced_rng.mpr $ continuous_of_continuous_uncurry ↑g h

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

lemma continuous_prod_second_half (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.2.extend
  (2 * x.2 - 1)) :=
begin
  let η := (λ p : Ω(x) × I, p.1.extend (2 * p.2 - 1)),
  have H : continuous η,
  { let Cproj : C(ℝ, I) := ⟨set.proj_Icc 0 1 zero_le_one, continuous_proj_Icc⟩,
    have h_left := ((continuous_map.continuous_prod _ _ _).comp (continuous.prod.mk Cproj)).comp
      continuous_induced_dom,
    have aux : continuous (λ x : ℝ, 2 * x -1 ),
      from (continuous_const.mul continuous_id').sub continuous_const,
    have h_right := aux.comp continuous_induced_dom,
    exact (continuous_eval'.comp (continuous.prod_map h_left h_right)) },
  exact (homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm).mp
    (H.comp continuous_snd),
end

theorem Hmul_cont (x : X) : continuous (λ x : (Ω(x) × Ω(x)) × I, x.1.1.trans x.1.2 x.2) :=
begin
  apply continuous.piecewise,
  { rintros ⟨_, t⟩ h,
    have h_eq : (λ (i : (path x x × path x x) × I), (i.snd : ℝ) ≤ (1 / 2)) =
      (set.univ) ×ˢ {s : I | (s : ℝ) ≤ (1 / 2)},
    { ext p,
      change (p.2 : ℝ) ≤ 1 / 2 ↔ p ∈ (@set.univ (Ω(x) × Ω(x)) ×ˢ {s : I | (s : ℝ) ≤ 1 / 2}),
      simp only [set.mem_prod, set.mem_univ, set.mem_set_of_eq, true_and] },
    erw h_eq at h,
    simp only [frontier_prod_eq, frontier_univ, closure_univ, set.empty_prod,
      set.union_empty, set.prod_mk_mem_set_prod_eq, set.mem_univ, true_and] at h,
    simp only [mem_frontier h, set.right_mem_Icc, zero_le_one, coe_one, one_div,
      mul_inv_cancel_of_invertible, path.extend_extends, mk_one, path.target, set.left_mem_Icc,
      sub_self, mk_zero, path.source] },
  exacts [continuous_prod_first_half x, continuous_prod_second_half x],
end

/- This is the function defined on p. 475 of Serre's `Homologie singulière des espaces fibrés`
defining a homotopy from a path `γ` to the product `γ ∧ e`.-/
def delayed_refl_left {x : X} (θ : I) (γ : Ω(x)) : Ω(x) :=
{ to_fun := λ t, if  (t : ℝ) ≤ θ / 2 then x
                 else γ.extend ((2*t - θ)/(2 - θ)),
  continuous_to_fun :=
  begin
    apply continuous.piecewise,
    { intros t ht,
      rw mem_frontier ht,
      field_simp, },
    exacts [continuous_const, (continuous_extend γ).comp ((continuous_const.mul
      continuous_induced_dom).sub continuous_const).div_const ],
  end,
  source' :=
  begin
    simp only [coe_zero, path.source, mul_zero, zero_sub, ite_eq_left_iff, not_le],
    intro h,
    contrapose! h,
    exact div_nonneg θ.2.1 zero_le_two,
  end,
  target' :=
  begin
    simp only [coe_one, path.target, mul_one, ite_eq_left_iff, not_le],
    intro,
    rw div_self,
    { simpa only [div_self, set.right_mem_Icc, zero_le_one, extend_extends, mk_one,
      to_fun_eq_coe, coe_to_continuous_map] using γ.3 },
    { linarith },
  end }


lemma delayed_refl_left_at_0 (γ : Ω(x)) : (delayed_refl_left 0 γ) = γ :=
begin
  ext t,
  dsimp [delayed_refl_left],
  rw [sub_zero, sub_zero, mul_div_assoc, mul_div_cancel' (t : ℝ) two_ne_zero, zero_div],
  split_ifs with h,
  { have := coe_eq_zero.mp (((nonneg t).antisymm) h).symm,
    rwa [this, path.source] },
  { exact extend_extends' _ _ },
end

lemma delayed_refl_left_at_1 (γ : Ω(x)) : (delayed_refl_left 1 γ) = (path.refl x).trans γ :=
begin
  ext t,
  dsimp [delayed_refl_left],
  norm_num,
  refl,
end

lemma delayed_refl_left_e (θ : I) : delayed_refl_left θ (refl x) = refl x :=
begin
  ext t,
  dsimp [path.refl, delayed_refl_left],
  split_ifs;
  refl,
end

/- This is the function analogous to the one on p. 475 of Serre's `Homologie singulière des espaces`
  `fibrés`, defining a homotopy from the product path `e ∧ γ` to `γ`.-/
def delayed_refl_right {x : X} (θ : I) (γ : Ω(x)) : Ω(x) :=
{ to_fun := λ t, if  (t : ℝ) ≤ (1 + θ) / 2 then γ.extend (2 * t/(1 + θ))
                 else x,
  continuous_to_fun :=
  begin
    apply continuous.piecewise,
    { intros t ht,
      rw [mem_frontier ht, mul_div_cancel', div_self],
      simp only [γ.target, set.right_mem_Icc, zero_le_one, extend_extends, mk_one],
      exacts [ne_of_gt $ add_pos_of_pos_of_nonneg (@one_pos ℝ _ _) θ.2.1, two_ne_zero] },
    exacts [(continuous_extend γ).comp (continuous_const.mul continuous_induced_dom).div_const,
      continuous_const],
  end,
  source' :=
  begin
    simp only [zero_le_one, extend_extends, coe_zero, set.left_mem_Icc, mul_zero, zero_div, mk_zero,
       path.source, if_t_t],
  end,
  target' :=
  begin
    simp only [coe_one, mul_one, ite_eq_right_iff, one_le_div (@two_pos ℝ _ _),
      ← sub_le_iff_le_add],
    intro h,
    replace h : (1 : ℝ) ≤ θ := by linarith,
    rw (h.antisymm θ.2.2).symm,
    norm_num,
  end }

lemma delayed_refl_right_at_0 (γ : Ω(x)) : (delayed_refl_right 0 γ) = γ.trans (path.refl x) :=
begin
  ext t,
  dsimp [delayed_refl_right],
  simp only [add_zero, div_one],
  refl,
end

lemma delayed_refl_right_at_1 (γ : Ω(x)) : (delayed_refl_right 1 γ) = γ :=
begin
  ext t,
  dsimp [delayed_refl_right],
  split_ifs with h,
  { norm_num,
    rw [mul_div_assoc, mul_div_cancel' _ $ @two_ne_zero ℝ _ _, extend_extends'] },
  { norm_num at h,
    contrapose! h,
    exact t.2.2 }
end

lemma delayed_refl_right_e (θ : I) : delayed_refl_right θ (refl x) = refl x :=
begin
  ext t,
  dsimp [path.refl, delayed_refl_right],
  split_ifs;
  refl,
end


-- `[FAE]` The two lemmas below might be unified, probably
lemma aux_mem_I {t θ : I} (h : (θ : ℝ) / 2 < t) : 0 ≤ ((2 : ℝ) * t - θ)/(2 - θ) ∧
  ((2 : ℝ) * t - θ)/(2 - θ) ≤ 1 := ⟨div_nonneg (le_of_lt $ sub_pos.mpr $ (div_lt_iff' two_pos).mp h)
    (sub_nonneg.mpr $ (θ.2.2).trans one_le_two),
    (div_le_one (sub_pos.mpr $ lt_of_le_of_lt θ.2.2 one_lt_two)).mpr ((sub_le_sub_iff_right ↑θ).mpr
    $ mul_nonneg_le_one_le (@zero_le_two ℝ _ _ _ _ _) (le_of_eq rfl) t.2.1 t.2.2)⟩

lemma aux_mem_I' {t θ : I} (h : (t : ℝ) ≤ (1 + θ) / 2) : 0 ≤ ((2 : ℝ) * t)/(1 + θ) ∧
  ((2 : ℝ) * t)/(1 + θ) ≤ 1 := ⟨ div_nonneg (by {simpa only [zero_le_mul_left, zero_lt_bit0,
    zero_lt_one] using t.2.1 }) (add_nonneg zero_le_one θ.2.1), ((div_le_one $
    add_pos_of_pos_of_nonneg (@one_pos ℝ _ _) θ.2.1).mpr $ (le_div_iff' two_pos).mp h)⟩

/- This is the function `Q` defined on p. 475 of Serre's `Homologie singulière des espaces fibrés`
that helps proving continuity of `delayed_refl_left`.-/
def Q_left : I × I → I := λ p, dite ((p.1 : ℝ) ≤ p.2 / 2) (λ h, 0)
  (λ h, ⟨(2 * p.1 - p.2)/(2 - p.2), aux_mem_I $ not_le.mp h⟩)

def Q'_left : I × I → ℝ := λ p,
ite ((p.1 : ℝ) ≤ p.2 / 2) 0 ((2 * p.1 - p.2)/(2 - p.2))

lemma Q'_left_extends_Q_left : Q_left = (set.proj_Icc (0 : ℝ) _ zero_le_one) ∘ Q'_left :=
begin
  ext,
  dsimp only [Q_left, Q'_left, zero_le_one],
  split_ifs,
  { simp only [coe_zero, function.comp_app, if_pos h, zero_div, set.proj_Icc_left,
    mk_zero, coe_zero]},
  { simp only [(set.proj_Icc_of_mem (@zero_le_one ℝ _ _ _ _) (aux_mem_I $ not_le.mp h)).symm,
    if_neg h, function.comp_app] },
end

lemma continuous_Q'_left : continuous Q'_left :=
begin
  refine @continuous_if (I × I) ℝ _ _ (λ p, (p.1 : ℝ) ≤ p.2/2) 0 (λ p, (2 * p.1 - p.2)/(2 - p.2))
    _ _ _ _,
  { intros _ hp,
    have h := @continuous.div_const (I × I) ℝ _ _ _ (coe ∘ prod.snd) _ (continuous_subtype_coe.comp
    continuous_snd) 2,
    replace hp := frontier_le_subset_eq (continuous_subtype_coe.comp continuous_fst) h hp,
    simp only [pi.zero_apply, function.comp_app, set.mem_set_of_eq] at ⊢ hp,
    field_simp [hp] },
  { exact continuous_zero.continuous_on },
  { refine (((continuous_const.mul (continuous_induced_dom.comp continuous_fst)).sub
    (continuous_induced_dom.comp continuous_snd)).div (continuous_const.sub
      (continuous_induced_dom.comp continuous_snd)) (λ p, _)).continuous_on,
    exact sub_ne_zero_of_ne (ne_of_lt (lt_of_le_of_lt p.2.2.2 one_lt_two)).symm },
end

lemma continuous_Q_left : continuous Q_left :=
  by simp only [Q'_left_extends_Q_left, continuous_proj_Icc.comp continuous_Q'_left]

lemma continuous_delayed_refl_left {x : X} :
  continuous (λ p : I × Ω(x), delayed_refl_left p.1 p.2) :=
begin
  apply continuous_to_Ω_if_continuous_uncurry,
  have hQ := ((homeomorph.comp_continuous_iff' $ (homeomorph.prod_assoc I I Ω(x)).symm).mpr
    ((continuous.comp continuous_Q_left continuous_fst).prod_mk continuous_snd)).comp
      continuous_swap,
  convert continuous_eval.comp hQ,--this is slow
  ext,
  dsimp [delayed_refl_left, prod.swap, homeomorph.prod_assoc, Q_left],
  split_ifs,
  exacts [(path.source _).symm, extend_extends _ _],
end

/- This `Q_left` is analogous to the function `Q` defined on p. 475 of Serre's `Homologie`
  `singulière des espaces fibrés` that helps proving continuity of `delayed_refl_right`.-/
def Q_right : I × I → I := λ p, dite ((p.1 : ℝ) ≤ (1 + p.2) / 2)
  (λ h, ⟨(2 * p.1)/(1 + p.2), aux_mem_I' h⟩) (λ h, 1)

def Q'_right : I × I → ℝ := λ p,
ite ((p.1 : ℝ) ≤ (1 + p.2) / 2) ((2 * p.1)/(1 + p.2)) 1

lemma Q'_right_extends_Q_right : Q_right = (set.proj_Icc (0 : ℝ) _ zero_le_one) ∘ Q'_right :=
begin
  ext,
  dsimp only [Q_right, Q'_right, zero_le_one],
  split_ifs,
  { simp only [if_pos h, (set.proj_Icc_of_mem (@zero_le_one ℝ _ _ _ _) (aux_mem_I' h)).symm,
    function.comp_app] },
  { simp only [if_neg h, function.comp_app, set.proj_Icc_right, mk_one] },
end

lemma continuous_Q'_right : continuous Q'_right :=
begin
  have : ∀ a : I, (1 : ℝ) + a ≠ 0 := λ a, ne_of_gt $ add_pos_of_pos_of_nonneg one_pos a.2.1,
  refine @continuous_if (I × I) ℝ _ _ (λ p, (p.1 : ℝ) ≤ (1 + p.2)/2) (λ p, (2 * p.1)/(1 + p.2)) 1
    _ _ _ _,
  { intros _ hp,
    have h : continuous (λ (x : I × I), ((1 : ℝ) + (x.snd)) / 2),
    exact (continuous_const.add (continuous_induced_dom.comp continuous_snd)).div_const,
    replace hp := frontier_le_subset_eq (continuous_subtype_coe.comp continuous_fst) h hp,
    simp only [pi.one_apply, function.comp_app, set.mem_set_of_eq] at ⊢ hp,
    rw [hp, mul_div_cancel' _ (@two_ne_zero ℝ _ _), div_self],
    exact this a.2 },
  { refine ((continuous_const.mul $ continuous_induced_dom.comp continuous_fst).div
      (continuous_const.add (continuous_induced_dom.comp continuous_snd)) (λ a, _)).continuous_on,
    exact this a.2 },
  { exact continuous_one.continuous_on },
end

lemma continuous_Q_right : continuous Q_right :=
  by simp only [Q'_right_extends_Q_right, continuous_proj_Icc.comp continuous_Q'_right]

lemma continuous_delayed_refl_right {x : X} :
  continuous (λ p : I × Ω(x), delayed_refl_right p.1 p.2) :=
begin
  apply continuous_to_Ω_if_continuous_uncurry,
  have hQ := ((homeomorph.comp_continuous_iff' $ (homeomorph.prod_assoc I I Ω(x)).symm).mpr
    ((continuous.comp continuous_Q_right continuous_fst).prod_mk continuous_snd)).comp
      continuous_swap,
  convert continuous_eval.comp hQ,----this is slow
  ext,
  dsimp [delayed_refl_right, prod.swap, homeomorph.prod_assoc, Q_right],
  split_ifs,
  exacts [extend_extends _ _, (path.target _).symm],
end


instance loop_space_is_H_space (x : X) : H_space Ω(x) :=
{ Hmul := λ ρ, ρ.1.trans ρ.2,
  e := refl _,
  cont' := continuous_to_Ω_if_to_C $ continuous_of_continuous_uncurry _ $ Hmul_cont x,
  Hmul_e_e := refl_trans_refl,
  left_Hmul_e :=
  begin
    use ⟨λ p, delayed_refl_left p.1 p.2, continuous_delayed_refl_left⟩;
    intro x,
    { exact delayed_refl_left_at_0 x },
    { exact delayed_refl_left_at_1 x },
    { intros _ h,
      simp only [set.mem_singleton_iff.mp h, continuous_map.coe_mk, refl_trans_refl, id.def,
        and_self],
      exact delayed_refl_left_e x },
  end,
  right_Hmul_e :=
  begin
    use ⟨λ p, delayed_refl_right p.1 p.2, continuous_delayed_refl_right⟩;
    intro x,
    { exact delayed_refl_right_at_0 x },
    { exact delayed_refl_right_at_1 x },
    { intros _ h,
      simp only [set.mem_singleton_iff.mp h, continuous_map.coe_mk, refl_trans_refl, id.def,
        and_self],
      exact delayed_refl_right_e x },
  end  }

end path_space_H_space

end H_space
