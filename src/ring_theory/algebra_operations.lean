/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Multiplication of submodules of an algebra.
-/

import ring_theory.algebra ring_theory.noetherian

universes u v

open lattice submodule

namespace algebra

variables {R : Type u} [comm_ring R]

section ring

variables {A : Type v} [ring A] [algebra R A]

set_option class.instance_max_depth 50
instance : has_mul (submodule R A) :=
⟨λ M N, ⨆ s : M, N.map $ algebra.lmul R A s.1⟩
set_option class.instance_max_depth 32

variables (S T : set A) {M N P Q : submodule R A} {m n : A}

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
theorem span_mul_span : span R S * span R T = span R ((S.prod T).image (λ p, p.1 * p.2)) :=
le_antisymm
  (mul_le.2 $ λ x1 hx1 x2 hx2, span_induction hx1
    (λ y1 hy1, span_induction hx2
      (λ y2 hy2, subset_span ⟨(y1, y2), ⟨hy1, hy2⟩, rfl⟩)
      ((mul_zero y1).symm ▸ zero_mem _)
      (λ r1 r2, (mul_add y1 r1 r2).symm ▸ add_mem _)
      (λ s r, (algebra.mul_smul_comm s y1 r).symm ▸ smul_mem _ _))
    ((zero_mul x2).symm ▸ zero_mem _)
    (λ r1 r2, (add_mul r1 r2 x2).symm ▸ add_mem _)
    (λ s r, (algebra.smul_mul_assoc s r x2).symm ▸ smul_mem _ _))
  (span_le.2 (set.image_subset_iff.2 $ λ ⟨x1, x2⟩ ⟨hx1, hx2⟩,
    mul_mem_mul (subset_span hx1) (subset_span hx2)))
variables {R}

theorem fg_mul (hm : M.fg) (hn : N.fg) : (M * N).fg :=
let ⟨m, hf1, hm⟩ := fg_def.1 hm, ⟨n, hf2, hn⟩ := fg_def.1 hn in
fg_def.2 ⟨(m.prod n).image (λ p, p.1 * p.2),
set.finite_image _ (set.finite_prod hf1 hf2),
span_mul_span R m n ▸ hm ▸ hn ▸ rfl⟩

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

instance : semigroup (submodule R A) :=
{ mul := (*),
  mul_assoc := algebra.mul_assoc }

instance : mul_zero_class (submodule R A) :=
{ zero_mul := bot_mul,
  mul_zero := mul_bot,
  .. submodule.add_comm_monoid, .. algebra.semigroup  }

instance : distrib (submodule R A) :=
{ left_distrib := mul_sup,
  right_distrib := sup_mul,
  .. submodule.add_comm_monoid, .. algebra.semigroup }

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

instance : comm_semigroup (submodule R A) :=
{ mul_comm := algebra.mul_comm,
  .. algebra.semigroup }

end comm_ring

end algebra
