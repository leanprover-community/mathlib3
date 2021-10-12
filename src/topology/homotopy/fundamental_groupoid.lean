/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import topology.homotopy.path
import category_theory.groupoid
import analysis.convex.basic

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, fundamental group of `X` based at `x` is just the automorphism
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

private def refl_trans_symm_aux (x : I × I) : ℝ :=
if (x.2 : ℝ) ≤ 1/2 then
  x.1 * 2 * x.2
else
  x.1 * (2 - 2 * x.2)

private lemma continuous_refl_trans_symm_aux : continuous refl_trans_symm_aux :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _,
  { continuity },
  { continuity },
  { continuity },
  { continuity },
  intros x hx,
  norm_num [hx, mul_assoc],
end

local attribute [continuity] continuous_refl_trans_symm_aux

private lemma refl_trans_symm_aux_mem_I (x : I × I) : refl_trans_symm_aux x ∈ I :=
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

def refl_trans_symm (p : path x₀ x₁) : homotopy (path.refl x₀) (p.trans p.symm) :=
{ to_fun := λ x, p ⟨refl_trans_symm_aux x, refl_trans_symm_aux_mem_I x⟩,
  continuous_to_fun := by continuity,
  to_fun_zero := by norm_num [refl_trans_symm_aux],
  to_fun_one := λ x, begin
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
        norm_num [sub_sub_assoc_swap] },
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

def refl_symm_trans (p : path x₀ x₁) : homotopy (path.refl x₁) (p.symm.trans p) :=
(refl_trans_symm p.symm).cast rfl $ congr_arg _ path.symm_symm

end

private def reparam_aux (x y t : I) : I :=
⟨σ t * x + t * y, show (σ t : ℝ) • (x : ℝ) + (t : ℝ) • (y : ℝ) ∈ I, from convex_Icc _ _ x.2 y.2
  (by unit_interval) (by unit_interval) (by simp)⟩

def reparam (p  : path x₀ x₁) (f : I → I) (hf : continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  homotopy p (p.reparam f hf hf₀ hf₁) :=
{ to_fun := λ x, p (reparam_aux x.2 (f x.2) x.1),
  continuous_to_fun := by continuity!,
  to_fun_zero := λ x, by norm_num [reparam_aux],
  to_fun_one := λ x, by norm_num [reparam_aux],
  prop' := λ t x hx,
  begin
    cases hx,
    { rw hx, norm_num [reparam_aux, hf₀] },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      norm_num [reparam_aux, hf₁] }
  end }

def symm₂ {p q : path x₀ x₁} (h : p.homotopy q) : p.symm.homotopy q.symm :=
{ to_fun := λ x, h ⟨x.1, σ x.2⟩,
  continuous_to_fun := by continuity,
  to_fun_zero := by simp [path.symm],
  to_fun_one := by simp [path.symm],
  prop' := λ t x hx, begin
    cases hx,
    { rw hx, simp },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      simp }
  end }

section trans_refl

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

def trans_refl (p : path x₀ x₁) : homotopy (p.trans (path.refl x₁)) p :=
((homotopy.reparam p (λ t, ⟨trans_refl_reparam_aux t, trans_refl_reparam_aux_mem_I t⟩)
  (by continuity) (subtype.ext trans_refl_reparam_aux_zero)
  (subtype.ext trans_refl_reparam_aux_one)).cast rfl (trans_refl_reparam p).symm).symm

def refl_trans (p : path x₀ x₁) : homotopy ((path.refl x₀).trans p) p :=
(trans_refl p.symm).symm₂.cast (by simp) (by simp)

end trans_refl

section assoc

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
  simp only [trans_assoc_reparam_aux, path.trans_apply, mul_inv_cancel_left₀, not_le, function.comp_app,
             ne.def, not_false_iff, bit0_eq_zero, one_ne_zero, mul_ite, subtype.coe_mk,
             path.coe_to_fun],
  split_ifs with h₁ h₂ h₃ h₄ h₅,
  { simp only [one_div, subtype.coe_mk] at h₂,
    simp [h₂, h₃] },
  { exfalso,
    simp only [subtype.coe_mk] at h₂,
    linarith },
  { exfalso,
    simp only [subtype.coe_mk] at h₂,
    linarith },
  { have h : ¬ (x : ℝ) + 1/4 ≤ 1/2, by linarith,
    have h' : 2 * ((x : ℝ) + 1/4) - 1 ≤ 1/2, by linarith,
    have h'' : 2 * (2 * (x : ℝ)) - 1 = 2 * (2 * (↑x + 1/4) - 1), by linarith,
    simp only [one_div, subtype.coe_mk] at h h' h'' h₂,
    simp [h₁, h₂, h₄, h, h', h''] },
  { exfalso,
    linarith },
  { have h : ¬ (1 / 2 : ℝ) * (x + 1) ≤ 1/2, by linarith,
    simp only [one_div] at h h₁,
    simp [h₁, h₅, h] }
end

def trans_assoc {x₀ x₁ x₂ x₃ : X} (p : path x₀ x₁) (q : path x₁ x₂) (r : path x₂ x₃) :
  homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
((homotopy.reparam (p.trans (q.trans r))
  (λ t, ⟨trans_assoc_reparam_aux t, trans_assoc_reparam_aux_mem_I t⟩)
  (by continuity) (subtype.ext trans_assoc_reparam_aux_zero)
  (subtype.ext trans_assoc_reparam_aux_one)).cast rfl (trans_assoc_reparam p q r).symm).symm

end assoc

end homotopy

end path

def fundamental_groupoid (X : Type u) [topological_space X] := X

local attribute [reducible] fundamental_groupoid
local attribute [instance] path.homotopic.setoid

instance : category_theory.groupoid (fundamental_groupoid X) :=
{ hom := λ x y, path.homotopic.quotient x y,
  id := λ x, ⟦path.refl x⟧,
  comp := λ x y z p q, quotient.lift₂ (λ (l₁ : path x y) (l₂ : path y z), ⟦l₁.trans l₂⟧) begin
    rintros a₁ a₂ b₁ b₂ ⟨h₁⟩ ⟨h₂⟩,
    rw quotient.eq,
    exact ⟨h₁.hcomp h₂⟩,
  end p q,
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
