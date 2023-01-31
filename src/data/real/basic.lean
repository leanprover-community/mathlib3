/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import algebra.bounds
import algebra.order.archimedean
import algebra.star.basic
import data.real.cau_seq_completion

/-!
# Real numbers from Cauchy sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/

assert_not_exists finset
assert_not_exists module
assert_not_exists submonoid

open_locale pointwise

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure real := of_cauchy ::
(cauchy : cau_seq.completion.Cauchy (abs : ℚ → ℚ))
notation `ℝ` := real

attribute [pp_using_anonymous_constructor] real

namespace cau_seq.completion

-- this can't go in `data.real.cau_seq_completion` as the structure on `rat` isn't available
@[simp] theorem of_rat_rat {abv : ℚ → ℚ} [is_absolute_value abv] (q : ℚ) :
  of_rat (q : ℚ) = (q : @Cauchy _ _ _ _ abv _) := rfl

end cau_seq.completion

namespace real
open cau_seq cau_seq.completion

variables {x y : ℝ}

lemma ext_cauchy_iff : ∀ {x y : real}, x = y ↔ x.cauchy = y.cauchy
| ⟨a⟩ ⟨b⟩ := by split; cc

lemma ext_cauchy {x y : real} : x.cauchy = y.cauchy → x = y :=
ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equiv_Cauchy : ℝ ≃ cau_seq.completion.Cauchy abs :=
⟨real.cauchy, real.of_cauchy, λ ⟨_⟩, rfl, λ _, rfl⟩

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
@[irreducible] private def zero : ℝ := ⟨0⟩
@[irreducible] private def one : ℝ := ⟨1⟩
@[irreducible] private def add : ℝ → ℝ → ℝ | ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
@[irreducible] private def neg : ℝ → ℝ | ⟨a⟩ := ⟨-a⟩
@[irreducible] private def mul : ℝ → ℝ → ℝ | ⟨a⟩ ⟨b⟩ := ⟨a * b⟩
@[irreducible] private noncomputable def inv' : ℝ → ℝ | ⟨a⟩ := ⟨a⁻¹⟩

instance : has_zero ℝ := ⟨zero⟩
instance : has_one ℝ := ⟨one⟩
instance : has_add ℝ := ⟨add⟩
instance : has_neg ℝ := ⟨neg⟩
instance : has_mul ℝ := ⟨mul⟩
instance : has_sub ℝ := ⟨λ a b, a + (-b)⟩
noncomputable instance : has_inv ℝ := ⟨inv'⟩

lemma of_cauchy_zero : (⟨0⟩ : ℝ) = 0 := show _ = zero, by rw zero
lemma of_cauchy_one : (⟨1⟩ : ℝ) = 1 := show _ = one, by rw one
lemma of_cauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ := show _ = add _ _, by rw add
lemma of_cauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ := show _ = neg _, by rw neg
lemma of_cauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ :=
by { rw [sub_eq_add_neg, of_cauchy_add, of_cauchy_neg], refl }
lemma of_cauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ := show _ = mul _ _, by rw mul
lemma of_cauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ := show _ = inv' _, by rw inv'

lemma cauchy_zero : (0 : ℝ).cauchy = 0 := show zero.cauchy = 0, by rw zero
lemma cauchy_one : (1 : ℝ).cauchy = 1 := show one.cauchy = 1, by rw one
lemma cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
| ⟨a⟩ ⟨b⟩ := show (add _ _).cauchy = _, by rw add
lemma cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
| ⟨a⟩ := show (neg _).cauchy = _, by rw neg
lemma cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
| ⟨a⟩ ⟨b⟩ := show (mul _ _).cauchy = _, by rw mul
lemma cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
| ⟨a⟩ ⟨b⟩ := by { rw [sub_eq_add_neg, ←cauchy_neg, ←cauchy_add], refl }
lemma cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
| ⟨f⟩ := show (inv' _).cauchy = _, by rw inv'

instance : has_nat_cast ℝ := { nat_cast := λ n, ⟨n⟩ }
instance : has_int_cast ℝ := { int_cast := λ z, ⟨z⟩ }
instance : has_rat_cast ℝ := { rat_cast := λ q, ⟨q⟩ }

lemma of_cauchy_nat_cast (n : ℕ) : (⟨n⟩ : ℝ) = n := rfl
lemma of_cauchy_int_cast (z : ℤ) : (⟨z⟩ : ℝ) = z := rfl
lemma of_cauchy_rat_cast (q : ℚ) : (⟨q⟩ : ℝ) = q := rfl

lemma cauchy_nat_cast (n : ℕ) : (n : ℝ).cauchy = n := rfl
lemma cauchy_int_cast (z : ℤ) : (z : ℝ).cauchy = z := rfl
lemma cauchy_rat_cast (q : ℚ) : (q : ℝ).cauchy = q := rfl

instance : comm_ring ℝ :=
begin
  refine_struct { zero  := (0 : ℝ),
                  one   := (1 : ℝ),
                  mul   := (*),
                  add   := (+),
                  neg   := @has_neg.neg ℝ _,
                  sub   := @has_sub.sub ℝ _,
                  npow  := @npow_rec ℝ ⟨1⟩ ⟨(*)⟩,
                  nsmul := @nsmul_rec ℝ ⟨0⟩ ⟨(+)⟩,
                  zsmul := @zsmul_rec ℝ ⟨0⟩ ⟨(+)⟩ ⟨@has_neg.neg ℝ _⟩,
                  ..real.has_nat_cast,
                  ..real.has_int_cast, };
  repeat { rintro ⟨_⟩, };
  try { refl };
  simp [← of_cauchy_zero, ← of_cauchy_one, ←of_cauchy_add, ←of_cauchy_neg, ←of_cauchy_mul,
    λ n, show @coe ℕ ℝ ⟨_⟩ n = ⟨n⟩, from rfl, has_nat_cast.nat_cast, has_int_cast.int_cast];
  apply add_assoc <|> apply add_comm <|> apply mul_assoc <|> apply mul_comm <|>
    apply left_distrib <|> apply right_distrib <|> apply sub_eq_add_neg <|> skip,
end

/-- `real.equiv_Cauchy` as a ring equivalence. -/
@[simps]
def ring_equiv_Cauchy : ℝ ≃+* cau_seq.completion.Cauchy abs :=
{ to_fun := cauchy,
  inv_fun := of_cauchy,
  map_add' := cauchy_add,
  map_mul' := cauchy_mul,
  ..equiv_Cauchy }

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/
instance : ring ℝ               := by apply_instance
instance : comm_semiring ℝ      := by apply_instance
instance : semiring ℝ           := by apply_instance
instance : comm_monoid_with_zero ℝ := by apply_instance
instance : monoid_with_zero ℝ   := by apply_instance
instance : add_comm_group ℝ     := by apply_instance
instance : add_group ℝ          := by apply_instance
instance : add_comm_monoid ℝ    := by apply_instance
instance : add_monoid ℝ         := by apply_instance
instance : add_left_cancel_semigroup ℝ := by apply_instance
instance : add_right_cancel_semigroup ℝ := by apply_instance
instance : add_comm_semigroup ℝ := by apply_instance
instance : add_semigroup ℝ      := by apply_instance
instance : comm_monoid ℝ        := by apply_instance
instance : monoid ℝ             := by apply_instance
instance : comm_semigroup ℝ     := by apply_instance
instance : semigroup ℝ          := by apply_instance
instance : inhabited ℝ          := ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : star_ring ℝ          := star_ring_of_comm
instance : has_trivial_star ℝ   := ⟨λ _, rfl⟩

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : cau_seq ℚ abs) : ℝ := ⟨cau_seq.completion.mk x⟩

theorem mk_eq {f g : cau_seq ℚ abs} : mk f = mk g ↔ f ≈ g :=
ext_cauchy_iff.trans mk_eq

@[irreducible]
private def lt : ℝ → ℝ → Prop | ⟨x⟩ ⟨y⟩ :=
quotient.lift_on₂ x y (<) $
  λ f₁ g₁ f₂ g₂ hf hg, propext $
  ⟨λ h, lt_of_eq_of_lt (setoid.symm hf) (lt_of_lt_of_eq h hg),
   λ h, lt_of_eq_of_lt hf (lt_of_lt_of_eq h (setoid.symm hg))⟩

instance : has_lt ℝ := ⟨lt⟩

lemma lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g := show lt _ _ ↔ _, by rw lt; refl

@[simp] theorem mk_lt {f g : cau_seq ℚ abs} : mk f < mk g ↔ f < g :=
lt_cauchy

lemma mk_zero : mk 0 = 0 := by rw ← of_cauchy_zero; refl
lemma mk_one : mk 1 = 1 := by rw ← of_cauchy_one; refl
lemma mk_add {f g : cau_seq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ←of_cauchy_add]
lemma mk_mul {f g : cau_seq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ←of_cauchy_mul]
lemma mk_neg {f : cau_seq ℚ abs} : mk (-f) = -mk f := by simp [mk, ←of_cauchy_neg]

@[simp] theorem mk_pos {f : cau_seq ℚ abs} : 0 < mk f ↔ pos f :=
by rw [← mk_zero, mk_lt]; exact iff_of_eq (congr_arg pos (sub_zero f))

@[irreducible] private def le (x y : ℝ) : Prop := x < y ∨ x = y
instance : has_le ℝ := ⟨le⟩
private lemma le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y := show le _ _ ↔ _, by rw le

@[simp] theorem mk_le {f g : cau_seq ℚ abs} : mk f ≤ mk g ↔ f ≤ g :=
by simp [le_def, mk_eq]; refl

@[elab_as_eliminator]
protected lemma ind_mk {C : real → Prop} (x : real) (h : ∀ y, C (mk y)) : C x :=
begin
  cases x with x,
  induction x using quot.induction_on with x,
  exact h x
end

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
begin
  induction a using real.ind_mk,
  induction b using real.ind_mk,
  induction c using real.ind_mk,
  simp only [mk_lt, ← mk_add],
  show pos _ ↔ pos _, rw add_sub_add_left_eq_sub
end

instance : partial_order ℝ :=
{ le := (≤), lt := (<),
  lt_iff_le_not_le := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa using lt_iff_le_not_le,
  le_refl := λ a, a.ind_mk (by intro a; rw mk_le),
  le_trans := λ a b c, real.ind_mk a $ λ a, real.ind_mk b $ λ b, real.ind_mk c $ λ c,
    by simpa using le_trans,
  lt_iff_le_not_le := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa using lt_iff_le_not_le,
  le_antisymm := λ a b, real.ind_mk a $ λ a, real.ind_mk b $ λ b,
    by simpa [mk_eq] using @cau_seq.le_antisymm _ _ a b }

instance : preorder ℝ := by apply_instance

theorem rat_cast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y :=
begin
  rw [mk_lt] {md := tactic.transparency.semireducible},
  exact const_lt
end

protected theorem zero_lt_one : (0 : ℝ) < 1 :=
by convert rat_cast_lt.2 zero_lt_one; simp [←of_cauchy_rat_cast, of_cauchy_one, of_cauchy_zero]

protected lemma fact_zero_lt_one : fact ((0 : ℝ) < 1) := ⟨real.zero_lt_one⟩

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
begin
  induction a using real.ind_mk with a,
  induction b using real.ind_mk with b,
  simpa only [mk_lt, mk_pos, ← mk_mul] using cau_seq.mul_pos
end

instance : strict_ordered_comm_ring ℝ :=
{ exists_pair_ne := ⟨0, 1, real.zero_lt_one.ne⟩,
  add_le_add_left :=
  begin
    simp only [le_iff_eq_or_lt],
    rintros a b ⟨rfl, h⟩,
    { simp },
    { exact λ c, or.inr ((add_lt_add_iff_left c).2 ‹_›) }
  end,
  zero_le_one := le_of_lt real.zero_lt_one,
  mul_pos     := @real.mul_pos,
  .. real.comm_ring, .. real.partial_order, .. real.semiring }

instance : strict_ordered_ring ℝ            := infer_instance
instance : strict_ordered_comm_semiring ℝ   := infer_instance
instance : strict_ordered_semiring ℝ        := infer_instance
instance : ordered_ring ℝ                   := infer_instance
instance : ordered_semiring ℝ               := infer_instance
instance : ordered_add_comm_group ℝ         := infer_instance
instance : ordered_cancel_add_comm_monoid ℝ := infer_instance
instance : ordered_add_comm_monoid ℝ        := infer_instance
instance : nontrivial ℝ                     := infer_instance

@[irreducible]
private def sup : ℝ → ℝ → ℝ | ⟨x⟩ ⟨y⟩ :=
⟨quotient.map₂ (⊔) (λ x₁ x₂ hx y₁ y₂ hy, sup_equiv_sup hx hy) x y⟩

instance : has_sup ℝ := ⟨sup⟩

lemma of_cauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ := show _ = sup _ _, by { rw sup, refl }
@[simp] lemma mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b := of_cauchy_sup _ _

@[irreducible]
private def inf : ℝ → ℝ → ℝ | ⟨x⟩ ⟨y⟩ :=
⟨quotient.map₂ (⊓) (λ x₁ x₂ hx y₁ y₂ hy, inf_equiv_inf hx hy) x y⟩

instance : has_inf ℝ := ⟨inf⟩

lemma of_cauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ := show _ = inf _ _, by { rw inf, refl }
@[simp] lemma mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b := of_cauchy_inf _ _

instance : distrib_lattice ℝ :=
{ sup := (⊔),
  le := (≤),
  le_sup_left := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b, begin
    rw [←mk_sup, mk_le],
    exact cau_seq.le_sup_left,
  end,
  le_sup_right := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b, begin
    rw [←mk_sup, mk_le],
    exact cau_seq.le_sup_right,
  end,
  sup_le := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b c, real.ind_mk c $ λ c, begin
    simp_rw [←mk_sup, mk_le],
    exact cau_seq.sup_le,
  end,
  inf := (⊓),
  inf_le_left := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b, begin
    rw [←mk_inf, mk_le],
    exact cau_seq.inf_le_left,
  end,
  inf_le_right := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b, begin
    rw [←mk_inf, mk_le],
    exact cau_seq.inf_le_right,
  end,
  le_inf := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b c, real.ind_mk c $ λ c, begin
    simp_rw [←mk_inf, mk_le],
    exact cau_seq.le_inf,
  end,
  le_sup_inf := λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b c, real.ind_mk c $ λ c, eq.le begin
    simp only [←mk_sup, ←mk_inf],
    exact congr_arg mk (cau_seq.sup_inf_distrib_left _ _ _).symm
  end,
  .. real.partial_order  }

/- Extra instances to short-circuit type class resolution -/
instance : lattice ℝ         := infer_instance
instance : semilattice_inf ℝ := infer_instance
instance : semilattice_sup ℝ := infer_instance

open_locale classical

instance : is_total ℝ (≤) :=
⟨λ a, real.ind_mk a $ λ a b, real.ind_mk b $ λ b, by simpa using le_total a b⟩

noncomputable instance : linear_order ℝ :=
lattice.to_linear_order _

noncomputable instance : linear_ordered_comm_ring ℝ :=
{ .. real.nontrivial, .. real.strict_ordered_ring, .. real.comm_ring, .. real.linear_order }

/- Extra instances to short-circuit type class resolution -/
noncomputable instance : linear_ordered_ring ℝ        := by apply_instance
noncomputable instance : linear_ordered_semiring ℝ    := by apply_instance
instance : is_domain ℝ :=
{ .. real.nontrivial, .. real.comm_ring, .. linear_ordered_ring.is_domain }

noncomputable instance : linear_ordered_field ℝ :=
{ inv := has_inv.inv,
  mul_inv_cancel := begin
    rintros ⟨a⟩ h,
    rw mul_comm,
    simp only [←of_cauchy_inv, ←of_cauchy_mul, ← of_cauchy_one, ← of_cauchy_zero, ne.def] at *,
    exact cau_seq.completion.inv_mul_cancel h,
  end,
  inv_zero := by simp [← of_cauchy_zero, ←of_cauchy_inv],
  rat_cast := coe,
  rat_cast_mk  := λ n d hd h2,
    by rw [←of_cauchy_rat_cast, rat.cast_mk', of_cauchy_mul, of_cauchy_inv, of_cauchy_nat_cast,
           of_cauchy_int_cast],
  ..real.linear_ordered_comm_ring }

/- Extra instances to short-circuit type class resolution -/

noncomputable instance : linear_ordered_add_comm_group ℝ          := by apply_instance
noncomputable instance field : field ℝ                            := by apply_instance
noncomputable instance : division_ring ℝ                          := by apply_instance
noncomputable instance decidable_lt (a b : ℝ) : decidable (a < b) := by apply_instance
noncomputable instance decidable_le (a b : ℝ) : decidable (a ≤ b) := by apply_instance
noncomputable instance decidable_eq (a b : ℝ) : decidable (a = b) := by apply_instance

/-- Show an underlying cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
meta instance : has_repr ℝ :=
{ repr := λ r, "real.of_cauchy " ++ repr r.cauchy }

theorem le_mk_of_forall_le {f : cau_seq ℚ abs} :
  (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f :=
begin
  intro h,
  induction x using real.ind_mk with x,
  apply le_of_not_lt,
  rw mk_lt,
  rintro ⟨K, K0, hK⟩,
  obtain ⟨i, H⟩ := exists_forall_ge_and h
    (exists_forall_ge_and hK (f.cauchy₃ $ half_pos K0)),
  apply not_lt_of_le (H _ le_rfl).1,
  rw [mk_lt] {md := tactic.transparency.semireducible},
  refine ⟨_, half_pos K0, i, λ j ij, _⟩,
  have := add_le_add (H _ ij).2.1
    (le_of_lt (abs_lt.1 $ (H _ le_rfl).2.2 _ ij).1),
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
end

theorem mk_le_of_forall_le {f : cau_seq ℚ abs} {x : ℝ}
  (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) : mk f ≤ x :=
begin
  cases h with i H,
  rw [← neg_le_neg_iff, ← mk_neg],
  exact le_mk_of_forall_le ⟨i, λ j ij, by simp [H _ ij]⟩
end

theorem mk_near_of_forall_near {f : cau_seq ℚ abs} {x : ℝ} {ε : ℝ}
  (H : ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| ≤ ε) : |mk f - x| ≤ ε :=
abs_sub_le_iff.2
  ⟨sub_le_iff_le_add'.2 $ mk_le_of_forall_le $
    H.imp $ λ i h j ij, sub_le_iff_le_add'.1 (abs_sub_le_iff.1 $ h j ij).1,
  sub_le_comm.1 $ le_mk_of_forall_le $
    H.imp $ λ i h j ij, sub_le_comm.1 (abs_sub_le_iff.1 $ h j ij).2⟩

instance : archimedean ℝ :=
archimedean_iff_rat_le.2 $ λ x, real.ind_mk x $ λ f,
let ⟨M, M0, H⟩ := f.bounded' 0 in
⟨M, mk_le_of_forall_le ⟨0, λ i _,
  rat.cast_le.2 $ le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : floor_ring ℝ := archimedean.floor_ring _

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : is_cau_seq abs f ↔ is_cau_seq
  abs (λ i, (f i : ℝ)) :=
⟨λ H ε ε0,
  let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0 in
  (H _ δ0).imp $ λ i hi j ij, lt_trans
    (by simpa using (@rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
 λ H ε ε0, (H _ (rat.cast_pos.2 ε0)).imp $
   λ i hi j ij, (@rat.cast_lt ℝ _ _ _).1 $ by simpa using hi _ ij⟩

theorem of_near (f : ℕ → ℚ) (x : ℝ)
  (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
  ∃ h', real.mk ⟨f, h'⟩ = x :=
⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
 sub_eq_zero.1 $ abs_eq_zero.1 $
  eq_of_le_of_forall_le_of_dense (abs_nonneg _) $ λ ε ε0,
    mk_near_of_forall_near $
    (h _ ε0).imp (λ i h j ij, le_of_lt (h j ij))⟩

theorem exists_floor (x : ℝ) : ∃ (ub : ℤ), (ub:ℝ) ≤ x ∧
   ∀ (z : ℤ), (z:ℝ) ≤ x → z ≤ ub :=
int.exists_greatest_of_bdd
  (let ⟨n, hn⟩ := exists_int_gt x in ⟨n, λ z h',
    int.cast_le.1 $ le_trans h' $ le_of_lt hn⟩)
  (let ⟨n, hn⟩ := exists_int_lt x in ⟨n, le_of_lt hn⟩)

theorem exists_is_lub (S : set ℝ) (hne : S.nonempty) (hbdd : bdd_above S) :
  ∃ x, is_lub S x :=
begin
  rcases ⟨hne, hbdd⟩ with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩,
  have : ∀ d : ℕ, bdd_above {m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d},
  { cases exists_int_gt U with k hk,
    refine λ d, ⟨k * d, λ z h, _⟩,
    rcases h with ⟨y, yS, hy⟩,
    refine int.cast_le.1 (hy.trans _),
    push_cast,
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg },
  choose f hf using λ d : ℕ, int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, int.floor_le _⟩,
  have hf₁ : ∀ n > 0, ∃ y ∈ S, ((f n / n:ℚ):ℝ) ≤ y := λ n n0,
    let ⟨y, yS, hy⟩ := (hf n).1 in
    ⟨y, yS, by simpa using (div_le_iff ((nat.cast_pos.2 n0):((_:ℝ) < _))).2 hy⟩,
  have hf₂ : ∀ (n > 0) (y ∈ S), (y - (n:ℕ)⁻¹ : ℝ) < (f n / n:ℚ),
  { intros n n0 y yS,
    have := (int.sub_one_lt_floor _).trans_le (int.cast_le.2 $ (hf n).2 _ ⟨y, yS, int.floor_le _⟩),
    simp [-sub_eq_add_neg],
    rwa [lt_div_iff ((nat.cast_pos.2 n0):((_:ℝ) < _)), sub_mul, _root_.inv_mul_cancel],
    exact ne_of_gt (nat.cast_pos.2 n0) },
  have hg : is_cau_seq abs (λ n, f n / n : ℕ → ℚ),
  { intros ε ε0,
    suffices : ∀ j k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε,
    { refine ⟨_, λ j ij, abs_lt.2 ⟨_, this _ ij  _ le_rfl⟩⟩,
      rw [neg_lt, neg_sub], exact this _ le_rfl _ ij },
    intros j ij k ik,
    replace ij := le_trans (nat.le_ceil _) (nat.cast_le.2 ij),
    replace ik := le_trans (nat.le_ceil _) (nat.cast_le.2 ik),
    have j0 := nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij),
    have k0 := nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik),
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩,
    refine lt_of_lt_of_le ((@rat.cast_lt ℝ _ _ _).1 _)
      ((inv_le ε0 (nat.cast_pos.2 k0)).1 ik),
    simpa using sub_lt_iff_lt_add'.2
      (lt_of_le_of_lt hy $ sub_lt_iff_lt_add.1 $ hf₂ _ k0 _ yS) },
  let g : cau_seq ℚ abs := ⟨λ n, f n / n, hg⟩,
  refine ⟨mk g, ⟨λ x xS, _, λ y h, _⟩⟩,
  { refine le_of_forall_ge_of_dense (λ z xz, _),
    cases exists_nat_gt (x - z)⁻¹ with K hK,
    refine le_mk_of_forall_le ⟨K, λ n nK, _⟩,
    replace xz := sub_pos.2 xz,
    replace hK := hK.le.trans (nat.cast_le.2 nK),
    have n0 : 0 < n := nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK),
    refine le_trans _ (hf₂ _ n0 _ xS).le,
    rwa [le_sub_comm, inv_le ((nat.cast_pos.2 n0):((_:ℝ) < _)) xz] },
  { exact mk_le_of_forall_le ⟨1, λ n n1,
      let ⟨x, xS, hx⟩ := hf₁ _ n1 in le_trans hx (h xS)⟩ }
end

noncomputable instance : has_Sup ℝ :=
⟨λ S, if h : S.nonempty ∧ bdd_above S then classical.some (exists_is_lub S h.1 h.2) else 0⟩

lemma Sup_def (S : set ℝ) :
  Sup S = if h : S.nonempty ∧ bdd_above S
    then classical.some (exists_is_lub S h.1 h.2) else 0 := rfl

protected theorem is_lub_Sup (S : set ℝ) (h₁ : S.nonempty) (h₂ : bdd_above S) : is_lub S (Sup S) :=
by { simp only [Sup_def, dif_pos (and.intro h₁ h₂)], apply classical.some_spec }

noncomputable instance : has_Inf ℝ := ⟨λ S, -Sup (-S)⟩

lemma Inf_def (S : set ℝ) : Inf S = -Sup (-S) := rfl

protected theorem is_glb_Inf (S : set ℝ) (h₁ : S.nonempty) (h₂ : bdd_below S) :
  is_glb S (Inf S) :=
begin
  rw [Inf_def, ← is_lub_neg', neg_neg],
  exact real.is_lub_Sup _ h₁.neg h₂.neg
end

noncomputable instance : conditionally_complete_linear_order ℝ :=
{ Sup := has_Sup.Sup,
  Inf := has_Inf.Inf,
  le_cSup := λ s a hs ha, (real.is_lub_Sup s ⟨a, ha⟩ hs).1 ha,
  cSup_le := λ s a hs ha, (real.is_lub_Sup s hs ⟨a, ha⟩).2 ha,
  cInf_le := λ s a hs ha, (real.is_glb_Inf s ⟨a, ha⟩ hs).1 ha,
  le_cInf := λ s a hs ha, (real.is_glb_Inf s hs ⟨a, ha⟩).2 ha,
 ..real.linear_order, ..real.lattice}

lemma lt_Inf_add_pos {s : set ℝ} (h : s.nonempty) {ε : ℝ} (hε : 0 < ε) :
  ∃ a ∈ s, a < Inf s + ε :=
exists_lt_of_cInf_lt h $ lt_add_of_pos_right _ hε

lemma add_neg_lt_Sup {s : set ℝ} (h : s.nonempty) {ε : ℝ} (hε : ε < 0) :
  ∃ a ∈ s, Sup s + ε < a :=
exists_lt_of_lt_cSup h $ add_lt_iff_neg_left.2 hε

lemma Inf_le_iff {s : set ℝ} (h : bdd_below s) (h' : s.nonempty) {a : ℝ} :
  Inf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε :=
begin
  rw le_iff_forall_pos_lt_add,
  split; intros H ε ε_pos,
  { exact exists_lt_of_cInf_lt h' (H ε ε_pos) },
  { rcases H ε ε_pos with ⟨x, x_in, hx⟩,
    exact cInf_lt_of_lt h x_in hx }
end

lemma le_Sup_iff {s : set ℝ} (h : bdd_above s) (h' : s.nonempty) {a : ℝ} :
  a ≤ Sup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x :=
begin
  rw le_iff_forall_pos_lt_add,
  refine ⟨λ H ε ε_neg, _, λ H ε ε_pos, _⟩,
  { exact exists_lt_of_lt_cSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg))) },
  { rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩,
    exact sub_lt_iff_lt_add.mp (lt_cSup_of_lt h x_in hx) }
end

@[simp] theorem Sup_empty : Sup (∅ : set ℝ) = 0 := dif_neg $ by simp

lemma csupr_empty {α : Sort*} [is_empty α] (f : α → ℝ) : (⨆ i, f i) = 0 :=
begin
  dsimp [supr],
  convert real.Sup_empty,
  rw set.range_eq_empty_iff,
  apply_instance
end

@[simp] lemma csupr_const_zero {α : Sort*} : (⨆ i : α, (0:ℝ)) = 0 :=
begin
  casesI is_empty_or_nonempty α,
  { exact real.csupr_empty _ },
  { exact csupr_const },
end

theorem Sup_of_not_bdd_above {s : set ℝ} (hs : ¬ bdd_above s) : Sup s = 0 :=
dif_neg $ assume h, hs h.2

lemma supr_of_not_bdd_above {α : Sort*} {f : α → ℝ} (hf : ¬ bdd_above (set.range f)) :
  (⨆ i, f i) = 0 := Sup_of_not_bdd_above hf

theorem Sup_univ : Sup (@set.univ ℝ) = 0 :=
real.Sup_of_not_bdd_above $ λ ⟨x, h⟩, not_le_of_lt (lt_add_one _) $ h (set.mem_univ _)

@[simp] theorem Inf_empty : Inf (∅ : set ℝ) = 0 :=
by simp [Inf_def, Sup_empty]

lemma cinfi_empty {α : Sort*} [is_empty α] (f : α → ℝ) : (⨅ i, f i) = 0 :=
by rw [infi_of_empty', Inf_empty]

@[simp] lemma cinfi_const_zero {α : Sort*} : (⨅ i : α, (0:ℝ)) = 0 :=
begin
  casesI is_empty_or_nonempty α,
  { exact real.cinfi_empty _ },
  { exact cinfi_const },
end

theorem Inf_of_not_bdd_below {s : set ℝ} (hs : ¬ bdd_below s) : Inf s = 0 :=
neg_eq_zero.2 $ Sup_of_not_bdd_above $ mt bdd_above_neg.1 hs

lemma infi_of_not_bdd_below  {α : Sort*} {f : α → ℝ} (hf : ¬ bdd_below (set.range f)) :
  (⨅ i, f i) = 0 := Inf_of_not_bdd_below hf

/--
As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
lemma Sup_nonneg (S : set ℝ) (hS : ∀ x ∈ S, (0:ℝ) ≤ x) : 0 ≤ Sup S :=
begin
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩,
  { exact Sup_empty.ge },
  { apply dite _ (λ h, le_cSup_of_le h hy $ hS y hy) (λ h, (Sup_of_not_bdd_above h).ge) }
end

/--
As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
lemma Sup_nonpos (S : set ℝ) (hS : ∀ x ∈ S, x ≤ (0:ℝ)) : Sup S ≤ 0 :=
begin
  rcases S.eq_empty_or_nonempty with rfl | hS₂,
  exacts [Sup_empty.le, cSup_le hS₂ hS],
end

/--
As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
lemma Inf_nonneg (S : set ℝ) (hS : ∀ x ∈ S, (0:ℝ) ≤ x) : 0 ≤ Inf S :=
begin
  rcases S.eq_empty_or_nonempty with rfl | hS₂,
  exacts [Inf_empty.ge, le_cInf hS₂ hS]
end

/--
As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
lemma Inf_nonpos (S : set ℝ) (hS : ∀ x ∈ S, x ≤ (0:ℝ)) : Inf S ≤ 0 :=
begin
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩,
  { exact Inf_empty.le },
  { apply dite _ (λ h, cInf_le_of_le h hy $ hS y hy) (λ h, (Inf_of_not_bdd_below h).le) }
end

lemma Inf_le_Sup (s : set ℝ) (h₁ : bdd_below s) (h₂ : bdd_above s) : Inf s ≤ Sup s :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hne,
  { rw [Inf_empty, Sup_empty] },
  { exact cInf_le_cSup h₁ h₂ hne }
end

theorem cau_seq_converges (f : cau_seq ℝ abs) : ∃ x, f ≈ const abs x :=
begin
  let S := {x : ℝ | const abs x < f},
  have lb : ∃ x, x ∈ S := exists_lt f,
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x :=
    λ x h y yS, le_of_lt $ const_lt.1 $ cau_seq.lt_trans yS h,
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub',
  refine ⟨Sup S,
    ((lt_total _ _).resolve_left (λ h, _)).resolve_right (λ h, _)⟩,
  { rcases h with ⟨ε, ε0, i, ih⟩,
    refine (cSup_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, sub_right_comm,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij },
  { rcases h with ⟨ε, ε0, i, ih⟩,
    refine (le_cSup ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0)),
    refine ⟨_, half_pos ε0, i, λ j ij, _⟩,
    rw [sub_apply, const_apply, add_comm, ← sub_sub,
      le_sub_iff_add_le, add_halves],
    exact ih _ ij }
end

instance : cau_seq.is_complete ℝ abs := ⟨cau_seq_converges⟩

end real
