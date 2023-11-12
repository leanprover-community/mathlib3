/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import category_theory.category.Groupoid
import category_theory.groupoid
import topology.category.Top.basic
import topology.homotopy.path

/-!
# Fundamental groupoid of a space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
variables {x₀ x₁ : X}

noncomputable theory

open_locale unit_interval

namespace path

namespace homotopy

section

/-- Auxilliary function for `refl_trans_symm` -/
def refl_trans_symm_aux (x : I × I) : ℝ :=
if (x.2 : ℝ) ≤ 1/2 then
  x.1 * 2 * x.2
else
  x.1 * (2 - 2 * x.2)

@[continuity]
lemma continuous_refl_trans_symm_aux : continuous refl_trans_symm_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _,
  { continuity },
  { continuity },
  { continuity },
  { continuity },
  intros x hx,
  norm_num [hx, mul_assoc],
end

lemma refl_trans_symm_aux_mem_I (x : I × I) : refl_trans_symm_aux x ∈ I :=
begin
  dsimp only [refl_trans_symm_aux],
  split_ifs,
  { split,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { unit_interval },
        { norm_num } },
      { unit_interval } },
    { rw [mul_assoc],
      apply mul_le_one,
      { unit_interval },
      { apply mul_nonneg,
        { norm_num },
        { unit_interval } },
      { linarith } } },
  { split,
    { apply mul_nonneg,
      { unit_interval },
      linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] },
    { apply mul_le_one,
      { unit_interval },
      { linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] },
      { linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] } } }
end

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
def refl_trans_symm (p : path x₀ x₁) : homotopy (path.refl x₀) (p.trans p.symm) :=
{ to_fun := λ x, p ⟨refl_trans_symm_aux x, refl_trans_symm_aux_mem_I x⟩,
  continuous_to_fun := by continuity,
  map_zero_left' := by norm_num [refl_trans_symm_aux],
  map_one_left' := λ x, begin
    dsimp only [refl_trans_symm_aux, path.coe_to_continuous_map, path.trans],
    change _ = ite _ _ _,
    split_ifs,
    { rw [path.extend, set.Icc_extend_of_mem],
      { norm_num },
      { rw unit_interval.mul_pos_mem_iff zero_lt_two,
        exact ⟨unit_interval.nonneg x, h⟩ } },
    { rw [path.symm, path.extend, set.Icc_extend_of_mem],
      { congr' 1,
        ext,
        norm_num [sub_sub_eq_add_sub] },
      { rw unit_interval.two_mul_sub_one_mem_iff,
        exact ⟨(not_le.1 h).le, unit_interval.le_one x⟩ } }
  end,
  prop' := λ t x hx, begin
    cases hx,
    { rw hx, simp [refl_trans_symm_aux] },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      norm_num [refl_trans_symm_aux] }
  end }

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
def refl_symm_trans (p : path x₀ x₁) : homotopy (path.refl x₁) (p.symm.trans p) :=
(refl_trans_symm p.symm).cast rfl $ congr_arg _ path.symm_symm

end

section trans_refl

/-- Auxilliary function for `trans_refl_reparam` -/
def trans_refl_reparam_aux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  2 * t
else
  1

@[continuity]
lemma continuous_trans_refl_reparam_aux : continuous trans_refl_reparam_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _;
  [continuity, continuity, continuity, continuity, skip],
  intros x hx,
  norm_num [hx]
end

lemma trans_refl_reparam_aux_mem_I (t : I) : trans_refl_reparam_aux t ∈ I :=
begin
  unfold trans_refl_reparam_aux,
  split_ifs; split; linarith [unit_interval.le_one t, unit_interval.nonneg t]
end

lemma trans_refl_reparam_aux_zero : trans_refl_reparam_aux 0 = 0 :=
by norm_num [trans_refl_reparam_aux]

lemma trans_refl_reparam_aux_one : trans_refl_reparam_aux 1 = 1 :=
by norm_num [trans_refl_reparam_aux]

lemma trans_refl_reparam (p : path x₀ x₁) : p.trans (path.refl x₁) =
  p.reparam (λ t, ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩) (by continuity)
  (subtype.ext trans_refl_reparam_aux_zero) (subtype.ext trans_refl_reparam_aux_one) :=
begin
  ext,
  unfold trans_refl_reparam_aux,
  simp only [path.trans_apply, not_le, coe_to_fun, function.comp_app],
  split_ifs,
  { refl },
  { simp }
end

/--
For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (path.refl x₁)` to `p`.
-/
def trans_refl (p : path x₀ x₁) : homotopy (p.trans (path.refl x₁)) p :=
((homotopy.reparam p (λ t, ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩)
  (by continuity) (subtype.ext trans_refl_reparam_aux_zero)
  (subtype.ext trans_refl_reparam_aux_one)).cast rfl (trans_refl_reparam p).symm).symm

/--
For any path `p` from `x₀` to `x₁`, we have a homotopy from `(path.refl x₀).trans p` to `p`.
-/
def refl_trans (p : path x₀ x₁) : homotopy ((path.refl x₀).trans p) p :=
(trans_refl p.symm).symm₂.cast (by simp) (by simp)

end trans_refl

section assoc

/-- Auxilliary function for `trans_assoc_reparam`. -/
def trans_assoc_reparam_aux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/4 then
  2 * t
else if (t : ℝ) ≤ 1/2 then
  t + 1/4
else
  1/2 * (t + 1)

@[continuity]
lemma continuous_trans_assoc_reparam_aux : continuous trans_assoc_reparam_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _)
    (continuous_if_le _ _ (continuous.continuous_on _)
    (continuous.continuous_on _) _).continuous_on _;
    [continuity, continuity, continuity, continuity, continuity, continuity, continuity,
     skip, skip];
    { intros x hx,
      norm_num [hx], }
end

lemma trans_assoc_reparam_aux_mem_I (t : I) : trans_assoc_reparam_aux t ∈ I :=
begin
  unfold trans_assoc_reparam_aux,
  split_ifs; split; linarith [unit_interval.le_one t, unit_interval.nonneg t]
end

lemma trans_assoc_reparam_aux_zero : trans_assoc_reparam_aux 0 = 0 :=
by norm_num [trans_assoc_reparam_aux]

lemma trans_assoc_reparam_aux_one : trans_assoc_reparam_aux 1 = 1 :=
by norm_num [trans_assoc_reparam_aux]

lemma trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : path x₀ x₁) (q : path x₁ x₂) (r : path x₂ x₃) :
  (p.trans q).trans r = (p.trans (q.trans r)).reparam
    (λ t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩)
    (by continuity) (subtype.ext trans_assoc_reparam_aux_zero)
    (subtype.ext trans_assoc_reparam_aux_one) :=
begin
  ext,
  simp only [trans_assoc_reparam_aux, path.trans_apply, mul_inv_cancel_left₀, not_le,
             function.comp_app, ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_ite,
             subtype.coe_mk, path.coe_to_fun],
  -- TODO: why does split_ifs not reduce the ifs??????
  split_ifs with h₁ h₂ h₃ h₄ h₅,
  { simp [h₂, h₃, -one_div] },
  { exfalso, linarith },
  { exfalso, linarith },
  { have h : ¬ (x : ℝ) + 1/4 ≤ 1/2, by linarith,
    have h' : 2 * ((x : ℝ) + 1/4) - 1 ≤ 1/2, by linarith,
    have h'' : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1/4) - 1), by linarith,
    simp only [h₄, h₁, h, h', h'',
      dif_neg (show ¬ false, from id), dif_pos true.intro, if_false, if_true] },
  { exfalso,
    linarith },
  { have h : ¬ (1 / 2 : ℝ) * (x + 1) ≤ 1/2, by linarith,
    have h' : ¬ 2 * ((1 / 2 : ℝ) * (x + 1)) - 1 ≤ 1/2, by linarith,
    simp only [h₁, h₅, h, h', if_false, dif_neg (show ¬ false, from id)],
    congr, ring }
end

/--
For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`.
-/
def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : path x₀ x₁) (q : path x₁ x₂) (r : path x₂ x₃) :
  homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
((homotopy.reparam (p.trans (q.trans r))
  (λ t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩)
  (by continuity) (subtype.ext trans_assoc_reparam_aux_zero)
  (subtype.ext trans_assoc_reparam_aux_one)).cast rfl (trans_assoc_reparam p q r).symm).symm

end assoc

end homotopy

end path

/--
The fundamental groupoid of a space `X` is defined to be a type synonym for `X`, and we subsequently
put a `category_theory.groupoid` structure on it.
-/
def fundamental_groupoid (X : Type u) := X

namespace fundamental_groupoid

instance {X : Type u} [h : inhabited X] : inhabited (fundamental_groupoid X) := h

local attribute [reducible] fundamental_groupoid
local attribute [instance] path.homotopic.setoid

instance : category_theory.groupoid (fundamental_groupoid X) :=
{ hom := λ x y, path.homotopic.quotient x y,
  id := λ x, ⟦path.refl x⟧,
  comp := λ x y z, path.homotopic.quotient.comp,
  id_comp' := λ x y f, quotient.induction_on f
    (λ a, show ⟦(path.refl x).trans a⟧ = ⟦a⟧,
          from quotient.sound ⟨path.homotopy.refl_trans a⟩ ),
  comp_id' := λ x y f, quotient.induction_on f
    (λ a, show ⟦a.trans (path.refl y)⟧ = ⟦a⟧,
          from quotient.sound ⟨path.homotopy.trans_refl a⟩),
  assoc' := λ w x y z f g h, quotient.induction_on₃ f g h
    (λ p q r, show ⟦(p.trans q).trans r⟧ = ⟦p.trans (q.trans r)⟧,
              from quotient.sound ⟨path.homotopy.trans_assoc p q r⟩),
  inv := λ x y p, quotient.lift (λ l : path x y, ⟦l.symm⟧) begin
    rintros a b ⟨h⟩,
    rw quotient.eq,
    exact ⟨h.symm₂⟩,
  end p,
  inv_comp' := λ x y f, quotient.induction_on f
    (λ a, show ⟦a.symm.trans a⟧ = ⟦path.refl y⟧,
          from quotient.sound ⟨(path.homotopy.refl_symm_trans a).symm⟩),
  comp_inv' := λ x y f, quotient.induction_on f
    (λ a, show ⟦a.trans a.symm⟧ = ⟦path.refl x⟧,
          from quotient.sound ⟨(path.homotopy.refl_trans_symm a).symm⟩) }

lemma comp_eq (x y z : fundamental_groupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.comp q := rfl

lemma id_eq_path_refl (x : fundamental_groupoid X) : 𝟙 x = ⟦path.refl x⟧ := rfl

/--
The functor sending a topological space `X` to its fundamental groupoid.
-/
def fundamental_groupoid_functor : Top ⥤ category_theory.Groupoid :=
{ obj := λ X, { α := fundamental_groupoid X },
  map := λ X Y f,
  { obj := f,
    map := λ x y p, p.map_fn f,
    map_id' := λ X, rfl,
    map_comp' := λ x y z p q, quotient.induction_on₂ p q $ λ a b,
      by simp [comp_eq, ← path.homotopic.map_lift, ← path.homotopic.comp_lift] },
  map_id' := begin
    intro X,
    change _ = (⟨_, _, _, _⟩ : fundamental_groupoid X ⥤ fundamental_groupoid X),
    congr',
    ext x y p,
    refine quotient.induction_on p (λ q, _),
    rw [← path.homotopic.map_lift],
    conv_rhs { rw [←q.map_id] },
    refl,
  end,
  map_comp' := begin
    intros X Y Z f g,
    congr',
    ext x y p,
    refine quotient.induction_on p (λ q, _),
    simp only [quotient.map_mk, path.map_map, quotient.eq],
    refl,
  end }

localized "notation (name := fundamental_groupoid_functor)
  `π` := fundamental_groupoid.fundamental_groupoid_functor" in fundamental_groupoid
localized "notation (name := fundamental_groupoid_functor.obj)
  `πₓ` := fundamental_groupoid.fundamental_groupoid_functor.obj" in fundamental_groupoid
localized "notation (name := fundamental_groupoid_functor.map)
  `πₘ` := fundamental_groupoid.fundamental_groupoid_functor.map" in fundamental_groupoid

lemma map_eq {X Y : Top} {x₀ x₁ : X} (f : C(X, Y)) (p : path.homotopic.quotient x₀ x₁) :
  (πₘ f).map p = p.map_fn f := rfl

/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
@[reducible]
def to_top {X : Top} (x : πₓ X) : X := x

/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space -/
@[reducible]
def from_top {X : Top} (x : X) : πₓ X := x

/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `path.homotopic.quotient`). -/
@[reducible]
def to_path {X : Top} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) :
  path.homotopic.quotient x₀ x₁ := p

/-- Help the typechecker by convering a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
@[reducible]
def from_path {X : Top} {x₀ x₁ : X} (p : path.homotopic.quotient x₀ x₁) : (x₀ ⟶ x₁) := p

end fundamental_groupoid
