/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import analysis.normed_space.basic
import algebra.lattice_ordered_group
import topology.order.lattice

/-!
# Normed lattice ordered groups

Motivated by the theory of Banach Lattices, we then define `normed_lattice_add_comm_group` as a
lattice with a covariant normed group addition satisfying the solid axiom.

## Main statements

We show that a normed lattice ordered group is a topological lattice with respect to the norm
topology.

## References

* [Meyer-Nieberg, Banach lattices][MeyerNieberg1991]

## Tags

normed, lattice, ordered, group
-/

/-!
### Normed lattice orderd groups

Motivated by the theory of Banach Lattices, this section introduces normed lattice ordered groups.
-/

local notation `|`a`|` := abs a

/--
Let `α` be a normed commutative group equipped with a partial order covariant with addition, with
respect which `α` forms a lattice. Suppose that `α` is *solid*, that is to say, for `a` and `b` in
`α`, with absolute values `|a|` and `|b|` respectively, `|a| ≤ |b|` implies `∥a∥ ≤ ∥b∥`. Then `α` is
said to be a normed lattice ordered group.
-/
class normed_lattice_add_comm_group (α : Type*)
  extends normed_group α, lattice α :=
(add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(solid : ∀ a b : α, |a| ≤ |b| → ∥a∥ ≤ ∥b∥)

lemma solid {α : Type*} [normed_lattice_add_comm_group α] {a b : α} (h : |a| ≤ |b|) : ∥a∥ ≤ ∥b∥ :=
normed_lattice_add_comm_group.solid a b h

/--
A normed lattice ordered group is an ordered additive commutative group
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_to_ordered_add_comm_group {α : Type*}
  [h : normed_lattice_add_comm_group α] : ordered_add_comm_group α := { ..h }

/--
Let `α` be a normed group with a partial order. Then the order dual is also a normed group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} : Π [normed_group α], normed_group (order_dual α) := id

/--
Let `α` be a normed lattice ordered group and let `a` and `b` be elements of `α`. Then `a⊓-a ≥ b⊓-b`
implies `∥a∥ ≤ ∥b∥`.
-/
lemma dual_solid {α : Type*} [normed_lattice_add_comm_group α] (a b : α) (h: b⊓-b ≤ a⊓-a) :
  ∥a∥ ≤ ∥b∥ :=
begin
  apply solid,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg a,
  rw ← neg_inf_eq_sup_neg,
  rw abs_eq_sup_neg,
  nth_rewrite 0 ← neg_neg b,
  rw ← neg_inf_eq_sup_neg,
  finish,
end

/--
Let `α` be a normed lattice ordered group, then the order dual is also a
normed lattice ordered group.
-/
@[priority 100] -- see Note [lower instance priority]
instance {α : Type*} [h: normed_lattice_add_comm_group α] :
  normed_lattice_add_comm_group (order_dual α) :=
{ add_le_add_left := begin
  intros a b h₁ c,
  rw ← order_dual.dual_le,
  rw ← order_dual.dual_le at h₁,
  apply h.add_le_add_left,
  exact h₁,
end,
solid := begin
  intros a b h₂,
  apply dual_solid,
  rw ← order_dual.dual_le at h₂,
  finish,
end, }

/--
Let `α` be a normed lattice ordered group, let `a` be an element of `α` and let `|a|` be the
absolute value of `a`. Then `∥|a|∥ = ∥a∥`.
-/
lemma norm_abs_eq_norm {α : Type*} [normed_lattice_add_comm_group α] (a : α) : ∥|a|∥ = ∥a∥ :=
begin
  rw le_antisymm_iff,
  split,
  { apply normed_lattice_add_comm_group.solid,
    rw ← lattice_ordered_comm_group.abs_idempotent a, },
  { apply normed_lattice_add_comm_group.solid,
    rw ← lattice_ordered_comm_group.abs_idempotent a, }
end

/--
Let `α` be a normed lattice ordered group. Then the infimum is jointly continuous.
-/
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
    { calc |p.fst ⊓ p.snd - q.fst ⊓ q.snd| =
        |p.fst ⊓ p.snd - q.fst ⊓ p.snd + (q.fst ⊓ p.snd - q.fst ⊓ q.snd)| :
          by { rw sub_add_sub_cancel, }
        ... ≤ |p.fst ⊓ p.snd - q.fst ⊓ p.snd| + |q.fst ⊓ p.snd - q.fst ⊓ q.snd| :
          by {apply lattice_ordered_comm_group.abs_triangle,}
        ... ≤ |p.fst - q.fst | + |p.snd - q.snd| : by {
          apply add_le_add,
          { exact
            (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right },
          { rw inf_comm,
          nth_rewrite 1 inf_comm,
          exact
            (sup_le_iff.elim_left (lattice_ordered_comm_group.Birkhoff_inequalities _ _ _)).right }
        }, },
    { exact add_nonneg (lattice_ordered_comm_group.abs_pos (p.fst - q.fst))
        (lattice_ordered_comm_group.abs_pos (p.snd - q.snd)), }
  },
  refine squeeze_zero (λ e, norm_nonneg _) this _,
  convert (((continuous_fst.tendsto q).sub tendsto_const_nhds).norm).add
        (((continuous_snd.tendsto q).sub tendsto_const_nhds).norm),
  simp,
end
⟩

/--
Let `α` be a normed lattice ordered group. Then `α` is a topological lattice in the norm topology.
-/
@[priority 100] -- see Note [lower instance priority]
instance normed_lattice_add_comm_group_topological_lattice {α : Type*}
  [normed_lattice_add_comm_group α] : topological_lattice α :=
topological_lattice.mk
