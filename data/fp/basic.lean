/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Implementation of floating-point numbers.
-/

import data.rat

namespace fp

inductive rmode
| NE -- round to nearest even

class float_cfg :=
(prec emax : ℕ)
(prec_pos : prec > 0)
(prec_max : prec ≤ emax)

variable [C : float_cfg]
include C

def prec := C.prec
def emax := C.emax
def emin : ℤ := 1 - C.emax

structure nan_pl :=
(sign : bool)
(pl : fin (2^prec))
(pl_pos : 0 < pl.1)

class fpsettings :=
(merge_nan : nan_pl → nan_pl → nan_pl)
(default_nan : nan_pl)

namespace lean
instance fpsettings : fpsettings :=
{ merge_nan := λ n1 n2, n1,
  default_nan := ⟨ff,
    ⟨1, nat.pow_lt_pow_of_lt_right dec_trivial C.prec_pos⟩, dec_trivial⟩ }
end lean

def valid_finite (e : ℤ) (m : ℕ) : Prop :=
emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin

instance dec_valid_finite (e m) : decidable (valid_finite e m) :=
by unfold valid_finite; apply_instance

inductive float
| inf {} : bool → float
| nan {} : nan_pl → float
| finite {} : bool → Π e m, valid_finite e m → float

def float.is_finite : float → bool
| (float.finite s e m f) := tt
| _ := ff

def shift2 (a b : ℕ) : ℤ → ℕ × ℕ
| (int.of_nat e) := (a.shiftl e, b)
| -[1+ e] := (a, b.shiftl e.succ)

def to_rat : Π (f : float), f.is_finite → ℚ
| (float.finite s e m f) _ :=
  let (n, d) := shift2 m 1 e,
      r := rat.mk_nat n d in
  if s then -r else r

theorem float.zero.valid : valid_finite emin 0 :=
⟨begin
  rw add_sub_assoc,
  apply le_add_of_nonneg_right,
  apply sub_nonneg_of_le,
  apply int.coe_nat_le_coe_nat_of_le,
  exact C.prec_pos
end, begin
  unfold emin,
  simp, rw ← sub_eq_add_neg,
  transitivity,
  apply sub_left_le_of_le_add,
  apply le_add_of_nonneg_left,
  apply int.coe_zero_le,
  apply int.coe_nat_le_coe_nat_of_le C.prec_max
end, begin
  rw max_eq_right,
  change (nat.size 0 : ℤ) with 0,
  simp, rw ← sub_eq_add_neg,
  apply sub_left_le_of_le_add,
  apply le_add_of_nonneg_left,
  apply int.coe_zero_le
end⟩

def float.zero (s : bool) : float :=
float.finite s emin 0 float.zero.valid

protected def float.sign : float → bool
| (float.inf s) := s
| (float.nan ⟨s, pl, h⟩) := s
| (float.finite s e m f) := s

protected def float.is_zero : float → bool
| (float.finite s e 0 f) := tt
| _ := ff

protected def float.neg : float → float
| (float.inf s) := float.inf (bnot s)
| (float.nan ⟨s, pl, h⟩) := float.nan ⟨bnot s, pl, h⟩
| (float.finite s e m f) := float.finite (bnot s) e m f

def div_nat_lt_two_pow (n d : ℕ) : ℤ → bool
| (int.of_nat e) := n < d.shiftl e
| -[1+ e] := n.shiftl e.succ < d


-- TODO(Mario): Prove these and drop 'meta'
set_option eqn_compiler.zeta true
meta def of_pos_rat_dn (n : ℕ+) (d : ℕ+) : float × bool :=
let e₁ : ℤ := n.1.size - d.1.size - prec,
    (d₁, n₁) := shift2 d.1 n.1 (e₁ + prec),
    e₂ := if n₁ < d₁ then e₁ - 1 else e₁,
    e₃ := max e₂ emin,
    (d₂, n₂) := shift2 d.1 n.1 (e₃ + prec),
    r := rat.mk_nat n₂ d₂,
    m := r.floor in
(float.finite ff e₃ (int.to_nat m) undefined, r.denom = 1)

meta def next_up_pos (e m) (v : valid_finite e m) : float :=
let m' := m.succ in
if ss : m'.size = m.size then
  float.finite ff e m' (by unfold valid_finite at *; rw ss; exact v)
else if h : e = emax then
  float.inf ff
else
  float.finite ff e.succ (nat.div2 m') undefined

meta def next_dn_pos (e m) (v : valid_finite e m) : float :=
match m with
| 0 := next_up_pos _ _ float.zero.valid
| nat.succ m' :=
  if ss : m'.size = m.size then
    float.finite ff e m' (by unfold valid_finite at *; rw ss; exact v)
  else if h : e = emin then
    float.finite ff emin m' undefined
  else
    float.finite ff e.pred (bit1 m') undefined
end

meta def next_up : float → float
| (float.finite ff e m f) := next_up_pos e m f
| (float.finite tt e m f) := float.neg $ next_dn_pos e m f
| f := f

meta def next_dn : float → float
| (float.finite ff e m f) := next_dn_pos e m f
| (float.finite tt e m f) := float.neg $ next_up_pos e m f
| f := f

meta def of_rat_up : ℚ → float
| ⟨0, _, _, _⟩          := float.zero ff
| ⟨nat.succ n, d, h, _⟩ :=
  let (f, exact) := of_pos_rat_dn n.succ_pnat ⟨d, h⟩ in
  if exact then f else next_up f
| ⟨-[1+n], d, h, _⟩     := float.neg (of_pos_rat_dn n.succ_pnat ⟨d, h⟩).1

meta def of_rat_dn (r : ℚ) : float :=
float.neg $ of_rat_up (-r)

meta def of_rat : rmode → ℚ → float
| rmode.NE r :=
  let low := of_rat_dn r, high := of_rat_up r in
  if hf : high.is_finite then
    if r = to_rat _ hf then high else
    if lf : low.is_finite then
      if r - to_rat _ lf > to_rat _ hf - r then high else
      if r - to_rat _ lf < to_rat _ hf - r then low else
      match low, lf with float.finite s e m f, _ :=
        if 2 ∣ m then low else high
      end
    else float.inf tt
  else float.inf ff

namespace float

variable [S : fpsettings]

def default_nan : float := nan fpsettings.default_nan

instance : has_neg float := ⟨float.neg⟩

meta def add (mode : rmode) : float → float → float
| (nan p₁) (nan p₂) := nan $ fpsettings.merge_nan p₁ p₂
| (nan p₁) _        := nan p₁
| _        (nan p₂) := nan p₂
| (inf tt) (inf ff) := default_nan
| (inf ff) (inf tt) := default_nan
| (inf s₁) _        := inf s₁
| _        (inf s₂) := inf s₂
| (finite s₁ e₁ m₁ v₁) (finite s₂ e₂ m₂ v₂) :=
  let f₁ := finite s₁ e₁ m₁ v₁, f₂ := finite s₂ e₂ m₂ v₂ in
  of_rat mode (to_rat f₁ rfl + to_rat f₂ rfl)

meta instance : has_add float := ⟨float.add rmode.NE⟩

meta def sub (mode : rmode) (f1 f2 : float) : float :=
add mode f1 (-f2)

meta instance : has_sub float := ⟨float.sub rmode.NE⟩

meta def mul (mode : rmode) : float → float → float
| (nan p₁) (nan p₂) := nan $ fpsettings.merge_nan p₁ p₂
| (nan p₁) _        := nan p₁
| _        (nan p₂) := nan p₂
| (inf s₁) f₂       := if f₂.is_zero then default_nan else inf (bxor s₁ f₂.sign)
| f₁       (inf s₂) := if f₁.is_zero then default_nan else inf (bxor f₁.sign s₂)
| (finite s₁ e₁ m₁ v₁) (finite s₂ e₂ m₂ v₂) :=
  let f₁ := finite s₁ e₁ m₁ v₁, f₂ := finite s₂ e₂ m₂ v₂ in
  of_rat mode (to_rat f₁ rfl * to_rat f₂ rfl)

meta def div (mode : rmode) : float → float → float
| (nan p₁) (nan p₂) := nan $ fpsettings.merge_nan p₁ p₂
| (nan p₁) _        := nan p₁
| _        (nan p₂) := nan p₂
| (inf s₁) (inf s₂) := default_nan
| (inf s₁) f₂       := inf (bxor s₁ f₂.sign)
| f₁       (inf s₂) := zero (bxor f₁.sign s₂)
| (finite s₁ e₁ m₁ v₁) (finite s₂ e₂ m₂ v₂) :=
  let f₁ := finite s₁ e₁ m₁ v₁, f₂ := finite s₂ e₂ m₂ v₂ in
  if f₂.is_zero then inf (bxor s₁ s₂) else
  of_rat mode (to_rat f₁ rfl / to_rat f₂ rfl)

end float

end fp