import tactic.rw_hint

structure cat :=
  (O : Type)
  (H : O → O → Type)
  (i : Π o : O, H o o)
  (c : Π {X Y Z : O} (f : H X Y) (g : H Y Z), H X Z)
  (li : Π {X Y : O} (f : H X Y), c (i X) f = f)
  (ri : Π {X Y : O} (f : H X Y), c f (i Y) = f)
  (a : Π {W X Y Z : O} (f : H W X) (g : H X Y) (h : H Y Z), c (c f g) h = c f (c g h))

open tactic

example (C : cat) (W X Y Z : C.O) (f : C.H X Y) (g : C.H W X) (h k : C.H Y Z) : C.c (C.c g f) h = C.c g (C.c f h) :=
begin
  -- rw_hint,
  (do s ← tactic.rw_hint_target,
      guard $ ("rw cat.a", "C.c g (C.c f h) = C.c g (C.c f h)") ∈ s,
      guard $ "rw cat.ri" ∉ (s.map prod.fst)),
  rw cat.a,
end

example (C : cat) (X Y : C.O) (f : C.H X Y) : C.c f (C.i Y) = f :=
begin
  (do s ← tactic.rw_hint_target,
      guard $ ("rw cat.ri", "f = f") ∈ s),
  rw cat.ri,
end

/-
Try this: rw ←int.of_nat.inj_eq
Try this: rw ordered_semiring.add_zero
Try this: rw norm_num.mul_bit0
Try this: rw two_mul
Try this: rw add_monoid.add_zero
Try this: rw ←nat.succ_eq_add_one
Try this: rw nat_add_zero
Try this: rw nat.succ_mul_succ_eq
Try this: rw add_zero
Try this: rw nat.bit0_val
Try this: rw ←nat.bit0_val
Try this: rw comm_monoid.mul_comm
Try this: rw ←comm_monoid.mul_comm
Try this: rw ←nat.succ.inj_eq
Try this: rw ←option.some_inj
Try this: rw decidable_linear_ordered_semiring.left_distrib
Try this: rw ←decidable_linear_ordered_semiring.left_distrib
Try this: rw semiring.add_zero
Try this: rw linear_ordered_semiring.left_distrib
Try this: rw ←linear_ordered_semiring.left_distrib
Try this: rw add_comm_monoid.add_comm
Try this: rw ←add_comm_monoid.add_comm
Try this: rw decidable_linear_ordered_semiring.add_zero
Try this: rw nat.succ_add_eq_succ_add
Try this: rw ←nat.succ_add_eq_succ_add
Try this: rw nat.add_comm
Try this: rw ←nat.add_comm
Try this: rw ←int.neg_succ_of_nat_inj_iff
Try this: rw nat.add_succ
Try this: rw comm_semiring.mul_comm
Try this: rw ←comm_semiring.mul_comm
Try this: rw semiring.left_distrib
Try this: rw ←semiring.left_distrib
Try this: rw decidable_linear_ordered_cancel_comm_monoid.add_comm
Try this: rw ←decidable_linear_ordered_cancel_comm_monoid.add_comm
Try this: rw ordered_cancel_comm_monoid.add_comm
Try this: rw ←ordered_cancel_comm_monoid.add_comm
Try this: rw comm_semiring.add_comm
Try this: rw ←comm_semiring.add_comm
Try this: rw eq_comm
Try this: rw ←eq_comm
Try this: rw ←eq_iff_eq_cancel_right
Try this: rw left_distrib
Try this: rw ←left_distrib
Try this: rw linear_ordered_semiring.add_comm
Try this: rw ←linear_ordered_semiring.add_comm
Try this: rw add_comm
Try this: rw ←add_comm
Try this: rw ←eq_iff_eq_cancel_left
Try this: rw ←option.some.inj_eq
Try this: rw comm_semiring.add_zero
Try this: rw nat.succ_add
Try this: rw nat.add_zero
Try this: rw nat.mul_succ
Try this: rw nat.bit1_val
Try this: rw norm_num.bit1_add_bit0
Try this: rw ←int.coe_nat_eq_coe_nat_iff
Try this: rw nat.bit0_succ_eq
Try this: rw decidable_linear_ordered_semiring.add_comm
Try this: rw ←decidable_linear_ordered_semiring.add_comm
Try this: rw nat.left_distrib
Try this: rw ←nat.left_distrib
Try this: rw comm_semigroup.mul_comm
Try this: rw ←comm_semigroup.mul_comm
Try this: rw linear_ordered_semiring.add_zero
Try this: rw nat.add_one
Try this: rw ordered_cancel_comm_monoid.add_zero
Try this: rw comm_semiring.left_distrib
Try this: rw ←comm_semiring.left_distrib
Try this: rw nat.bit1_eq_succ_bit0
Try this: rw mul_comm
Try this: rw ←mul_comm
Try this: rw le_antisymm_iff
Try this: rw add_comm_monoid.add_zero
Try this: rw nat.succ_mul
Try this: rw ←heq_iff_eq
Try this: rw nat.mul_comm
Try this: rw ←nat.mul_comm
Try this: rw nat.bit1_succ_eq
Try this: rw norm_num.mul_bit1
Try this: rw ←int.of_nat_eq_of_nat_iff
Try this: rw norm_num.bin_add_zero
Try this: rw add_comm_semigroup.add_comm
Try this: rw ←add_comm_semigroup.add_comm
Try this: rw ordered_semiring.left_distrib
Try this: rw ←ordered_semiring.left_distrib
Try this: rw ←norm_num.bit0_add_one
Try this: rw semiring.add_comm
Try this: rw ←semiring.add_comm
Try this: rw ←norm_num.one_add_bit0
Try this: rw decidable_linear_ordered_cancel_comm_monoid.add_zero
Try this: rw ←int.neg_succ_of_nat.inj_eq
Try this: rw distrib.left_distrib
Try this: rw ←distrib.left_distrib
Try this: rw ←norm_num.add1_bit0
Try this: rw mul_add
Try this: rw ←mul_add
Try this: rw ordered_semiring.add_comm
Try this: rw ←ordered_semiring.add_comm
-/
example : 2 * (3 + 4) = 2 * 3 + 2 * 4 :=
begin
  -- rw_hint,
  try_for 5500 (do
    t ← target,
    s ← tactic.rw_hint t ff none 1000,
    guard $ ("rw left_distrib", "2 * 3 + 2 * 4 = 2 * 3 + 2 * 4") ∈ s),
  rw left_distrib,
end

example (P Q : Prop) (h : P ↔ Q) (p : P) : Q :=
begin
  (do s ← tactic.rw_hint_target, guard $ ("rw ←h", "P") ∈ s),
  rw ←h, exact p,
end

-- Verify that the `with` keyword behaves as expected.
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q ∨ Q :=
begin
  -- rw_hint with P,
  (do s ← tactic.rw_hint_target (some ```(P)),
      guard $ s.length = 1,
      guard $ ("rw ←h", "P ∨ P") ∈ s),
  -- rw_hint with ¬Q → Q,
  (do s ← tactic.rw_hint_target (some ```(¬Q → Q)),
      guard $ s.length = 2,
      guard $ ("rw classical.or_iff_not_imp_left", "¬Q → Q") ∈ s),
  -- rw_hint with _ ∨ _,
  (do s ← tactic.rw_hint_target (some ```(_ ∨ _)),
      guard $ ("rw ←h", "P ∨ P") ∈ s,
      guard $ ("rw or.comm", "Q ∨ Q") ∈ s),

  rw ←h, exact or.inl p,

end

-- Verify that in `conv` mode only rewrites that transform the entire focus are reported.
example (P Q : Prop) (h : P ↔ Q) (p : P) : Q ∨ Q :=
begin
  conv {
    (do s ← conv.lhs >>= (λ e, tactic.rw_hint e tt),
        guard $ "rw ←h" ∉ (s.map prod.fst)),
    (do s ← conv.lhs >>= (λ e, tactic.rw_hint e tt),
        guard $ ("rw classical.or_iff_not_imp_left", "¬Q → Q") ∈ s),
    congr,
    (do s ← conv.lhs >>= (λ e, tactic.rw_hint e tt),
        guard $ ("rw ←h", "P") ∈ s),
  },
  rw ←h, exact or.inl p,
end
