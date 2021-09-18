/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.normed_space.basic
import algebra.lattice_ordered_group
import topology.order.lattice

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

open filter set
open_locale topological_space

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_group (α : Type*)
extends linear_ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

@[priority 100] instance normed_linear_ordered_group.to_normed_group (α : Type*)
  [normed_linear_ordered_group α] : normed_group α :=
⟨normed_linear_ordered_group.dist_eq⟩

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type*)
extends linear_ordered_field α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

@[priority 100] instance normed_linear_ordered_field.to_normed_field (α : Type*)
  [normed_linear_ordered_field α] : normed_field α :=
{ dist_eq := normed_linear_ordered_field.dist_eq,
  norm_mul' := normed_linear_ordered_field.norm_mul' }

@[priority 100] instance normed_linear_ordered_field.to_normed_linear_ordered_group (α : Type*)
[normed_linear_ordered_field α] : normed_linear_ordered_group α :=
⟨normed_linear_ordered_field.dist_eq⟩

noncomputable
instance : normed_linear_ordered_field ℚ :=
⟨dist_eq_norm, normed_field.norm_mul⟩

noncomputable
instance : normed_linear_ordered_field ℝ :=
⟨dist_eq_norm, normed_field.norm_mul⟩

-- See e.g. Peter Meyer-Nieberg

local notation `|`a`|` := abs a

-- I guess we would call this a normed lattice ordered group
class normed_lattice_add_comm_group (α : Type*)
  extends normed_group α, lattice α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(solid : ∀ a b : α, |a| ≤ |b| → ∥a∥ ≤ ∥b∥)

-- Suggested https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/norm.20of.20abs
instance normed_lattice_add_comm_group_to_covariant_class {α : Type*}
  [h : normed_lattice_add_comm_group α] : covariant_class α α (+) (≤) :=
{elim := λ a b c bc,  normed_lattice_add_comm_group.add_le_add_left _ _ bc a}

instance {α : Type*} : Π [normed_group α], normed_group (order_dual α) := id

lemma opsolid {α : Type*} [h: normed_lattice_add_comm_group α] : ∀ a b : α, a⊓-a ≥ b⊓-b →
  ∥a∥ ≤ ∥b∥ :=
begin
  intros a b h₁,
  apply h.solid,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg a,
  rw ← neg_inf_eq_sup_neg,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg b,
  rw ← neg_inf_eq_sup_neg,
  finish,
end


-- If α is a normed lattice ordered group, so is order_dual α
instance {α : Type*} [h: normed_lattice_add_comm_group α] : normed_lattice_add_comm_group
  (order_dual α) := {
  add_le_add_left := begin
    intros a b h₁ c,
    rw ← order_dual.dual_le,
    rw ← order_dual.dual_le at h₁,
    apply h.add_le_add_left,
    exact h₁,
  end,
  solid := begin
    intros a b h₂,
    apply opsolid,
    rw ← order_dual.dual_le at h₂,
    finish,
  end,
}

lemma norm_abs_eq_norm {α : Type*} [normed_lattice_add_comm_group α] (a : α) : ∥|a|∥ = ∥a∥ :=
begin
  rw le_antisymm_iff,
  split,
  {
    apply normed_lattice_add_comm_group.solid,
    rw ← lattice_ordered_comm_group.abs_idempotent a,
  },
  {
    apply normed_lattice_add_comm_group.solid,
    rw ← lattice_ordered_comm_group.abs_idempotent a,
  }
end

-- e.g. https://github.com/leanprover-community/mathlib/blob/1fdce2f8774ca129326ae6ec737005dbfa94bf3c/src/analysis/normed_space/basic.lean#L877
-- Banasiak, Banach Lattices in Applications,
-- Proposition 2.19
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_has_continuous_inf {α : Type*}
  [normed_lattice_add_comm_group α] : has_continuous_inf α :=
⟨ continuous_iff_continuous_at.2 $ λ q, tendsto_iff_norm_tendsto_zero.2 $
begin
  have : ∀ p : α × α, ∥p.1 ⊓ p.2 - q.1 ⊓ q.2∥ ≤ ∥p.1 - q.1∥ + ∥p.2 - q.2∥,
  {
    intros,
    nth_rewrite_rhs 0  ← norm_abs_eq_norm,
    nth_rewrite_rhs 1  ← norm_abs_eq_norm,
    apply le_trans _ (norm_add_le (|p.fst - q.fst|) (|p.snd - q.snd|)),
    apply normed_lattice_add_comm_group.solid,
    rw lattice_ordered_comm_group.abs_pos_eq (|p.fst - q.fst| + |p.snd - q.snd|),
    {
      calc |p.fst ⊓ p.snd - q.fst ⊓ q.snd| =
        |p.fst ⊓ p.snd - q.fst ⊓ p.snd + (q.fst ⊓ p.snd - q.fst ⊓ q.snd)| :
          by { rw sub_add_sub_cancel, }
        ... ≤ |p.fst ⊓ p.snd - q.fst ⊓ p.snd| + |q.fst ⊓ p.snd - q.fst ⊓ q.snd| :
          by {apply lattice_ordered_comm_group.abs_triangle,}
        ... ≤ |p.fst - q.fst | + |p.snd - q.snd| : by {
          apply add_le_add,
          apply
            (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right,
          -- Should I be surprised that this isn't infered automatically?
          apply normed_lattice_add_comm_group_to_covariant_class,
          rw inf_comm,
          nth_rewrite 1 inf_comm,
          apply
            (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right,
          -- Should I be surprised that this isn't infered automatically?
          apply normed_lattice_add_comm_group_to_covariant_class,
        },
    },
    {
      apply add_nonneg,
      apply lattice_ordered_comm_group.abs_pos,
      apply lattice_ordered_comm_group.abs_pos,
    }
  },
  refine squeeze_zero (λ e, norm_nonneg _) this _,
  convert (((continuous_fst.tendsto q).sub tendsto_const_nhds).norm).add
        (((continuous_snd.tendsto q).sub tendsto_const_nhds).norm),
  simp,
end
⟩

lemma normed_lattice_add_comm_group_has_continuous_sup {α : Type*}
  [h: normed_lattice_add_comm_group α] : has_continuous_sup α :=
infer_instance
