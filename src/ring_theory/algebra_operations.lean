/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Multiplication of submodules of an algebra.
-/

import ring_theory.algebra algebra.pointwise ring_theory.ideals
import tactic.chain

universes u v

open lattice algebra

local attribute [instance] set.pointwise_mul_semiring

namespace submodule

variables {R : Type u} [comm_ring R]

section ring

variables {A : Type v} [ring A] [algebra R A]
variables (S T : set A) {M N P Q : submodule R A} {m n : A}

instance : has_one (submodule R A) :=
⟨submodule.map (of_id R A).to_linear_map (⊤ : ideal R)⟩

theorem one_eq_map_top :
  (1 : submodule R A) = submodule.map (of_id R A).to_linear_map (⊤ : ideal R) := rfl

theorem one_eq_span : (1 : submodule R A) = span R {1} :=
begin
  apply submodule.ext,
  intro a,
  erw [mem_map, mem_span_singleton],
  apply exists_congr,
  intro r,
  simpa [smul_def],
end

theorem one_le : (1 : submodule R A) ≤ P ↔ (1 : A) ∈ P :=
by simpa only [one_eq_span, span_le, set.singleton_subset_iff]

set_option class.instance_max_depth 50
instance : has_mul (submodule R A) :=
⟨λ M N, ⨆ s : M, N.map $ algebra.lmul R A s.1⟩
set_option class.instance_max_depth 32

theorem mul_mem_mul (hm : m ∈ M) (hn : n ∈ N) : m * n ∈ M * N :=
(le_supr _ ⟨m, hm⟩ : _ ≤ M * N) ⟨n, hn, rfl⟩

theorem mul_le : M * N ≤ P ↔ ∀ (m ∈ M) (n ∈ N), m * n ∈ P :=
⟨λ H m hm n hn, H $ mul_mem_mul hm hn,
λ H, supr_le $ λ ⟨m, hm⟩, map_le_iff_le_comap.2 $ λ n hn, H m hm n hn⟩

@[elab_as_eliminator] protected theorem mul_induction_on
  {C : A → Prop} {r : A} (hr : r ∈ M * N)
  (hm : ∀ (m ∈ M) (n ∈ N), C (m * n))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x + y))
  (hs : ∀ (r : R) x, C x → C (r • x)) : C r :=
(@mul_le _ _ _ _ _ _ _ ⟨C, h0, ha, hs⟩).2 hm hr

variables R
theorem span_mul_span : span R S * span R T = span R (S * T) :=
begin
  apply le_antisymm,
  { rw mul_le, intros a ha b hb,
    apply span_induction ha,
    work_on_goal 0 { intros, apply span_induction hb,
      work_on_goal 0 { intros, exact subset_span ⟨_, ‹_›, _, ‹_›, rfl⟩ } },
    all_goals { intros, simp only [mul_zero, zero_mul, zero_mem,
        left_distrib, right_distrib, mul_smul_comm, smul_mul_assoc],
      try {apply add_mem _ _ _}, try {apply smul_mem _ _ _} }, assumption' },
  { rw span_le, rintros _ ⟨a, ha, b, hb, rfl⟩,
    exact mul_mem_mul (subset_span ha) (subset_span hb) }
end
variables {R}

variables (M N P Q)
set_option class.instance_max_depth 50
protected theorem mul_assoc : (M * N) * P = M * (N * P) :=
le_antisymm (mul_le.2 $ λ mn hmn p hp, suffices M * N ≤ (M * (N * P)).comap ((algebra.lmul R A).flip p), from this hmn,
  mul_le.2 $ λ m hm n hn, show m * n * p ∈ M * (N * P), from
  (mul_assoc m n p).symm ▸ mul_mem_mul hm (mul_mem_mul hn hp))
(mul_le.2 $ λ m hm np hnp, suffices N * P ≤ (M * N * P).comap (algebra.lmul R A m), from this hnp,
  mul_le.2 $ λ n hn p hp, show m * (n * p) ∈ M * N * P, from
  mul_assoc m n p ▸ mul_mem_mul (mul_mem_mul hm hn) hp)
set_option class.instance_max_depth 32

@[simp] theorem mul_bot : M * ⊥ = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [submodule.mem_bot] at hn ⊢; rw [hn, mul_zero]

@[simp] theorem bot_mul : ⊥ * M = ⊥ :=
eq_bot_iff.2 $ mul_le.2 $ λ m hm n hn, by rw [submodule.mem_bot] at hm ⊢; rw [hm, zero_mul]

@[simp] protected theorem one_mul : (1 : submodule R A) * M = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, one_mul, span_eq] }

@[simp] protected theorem mul_one : M * 1 = M :=
by { conv_lhs { rw [one_eq_span, ← span_eq M] }, erw [span_mul_span, mul_one, span_eq] }

variables {M N P Q}

@[mono] theorem mul_le_mul (hmp : M ≤ P) (hnq : N ≤ Q) : M * N ≤ P * Q :=
mul_le.2 $ λ m hm n hn, mul_mem_mul (hmp hm) (hnq hn)

theorem mul_le_mul_left (h : M ≤ N) : M * P ≤ N * P :=
mul_le_mul h (le_refl P)

theorem mul_le_mul_right (h : N ≤ P) : M * N ≤ M * P :=
mul_le_mul (le_refl M) h

variables (M N P)
theorem mul_sup : M * (N ⊔ P) = M * N ⊔ M * P :=
le_antisymm (mul_le.2 $ λ m hm np hnp, let ⟨n, hn, p, hp, hnp⟩ := mem_sup.1 hnp in
  mem_sup.2 ⟨_, mul_mem_mul hm hn, _, mul_mem_mul hm hp, hnp ▸ (mul_add m n p).symm⟩)
(sup_le (mul_le_mul_right le_sup_left) (mul_le_mul_right le_sup_right))

theorem sup_mul : (M ⊔ N) * P = M * P ⊔ N * P :=
le_antisymm (mul_le.2 $ λ mn hmn p hp, let ⟨m, hm, n, hn, hmn⟩ := mem_sup.1 hmn in
  mem_sup.2 ⟨_, mul_mem_mul hm hp, _, mul_mem_mul hn hp, hmn ▸ (add_mul m n p).symm⟩)
(sup_le (mul_le_mul_left le_sup_left) (mul_le_mul_left le_sup_right))
variables {M N P}

instance : semiring (submodule R A) :=
{ one_mul       := submodule.one_mul,
  mul_one       := submodule.mul_one,
  mul_assoc     := submodule.mul_assoc,
  zero_mul      := bot_mul,
  mul_zero      := mul_bot,
  left_distrib  := mul_sup,
  right_distrib := sup_mul,
  ..submodule.add_comm_monoid,
  ..submodule.has_one,
  ..submodule.has_mul }

end ring

section comm_ring

variables {A : Type v} [comm_ring A] [algebra R A]
variables {M N : submodule R A} {m n : A}

theorem mul_mem_mul_rev (hm : m ∈ M) (hn : n ∈ N) : n * m ∈ M * N :=
mul_comm m n ▸ mul_mem_mul hm hn

variables (M N)
protected theorem mul_comm : M * N = N * M :=
le_antisymm (mul_le.2 $ λ r hrm s hsn, mul_mem_mul_rev hsn hrm)
(mul_le.2 $ λ r hrn s hsm, mul_mem_mul_rev hsm hrn)

instance : comm_semiring (submodule R A) :=
{ mul_comm := submodule.mul_comm,
  .. submodule.semiring }

end comm_ring

end submodule
