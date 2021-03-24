/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.rat
import data.semiquot
/-!
# Implementation of floating-point numbers (experimental).
-/

def int.shift2 (a b : ℕ) : ℤ → ℕ × ℕ
| (int.of_nat e) := (a.shiftl e, b)
| -[1+ e] := (a, b.shiftl e.succ)

namespace fp

@[derive inhabited]
inductive rmode
| NE -- round to nearest even

class float_cfg :=
(prec emax : ℕ)
(prec_pos : 0 < prec)
(prec_max : prec ≤ emax)

variable [C : float_cfg]
include C

def prec := C.prec
def emax := C.emax
def emin : ℤ := 1 - C.emax

def valid_finite (e : ℤ) (m : ℕ) : Prop :=
emin ≤ e + prec - 1 ∧ e + prec - 1 ≤ emax ∧ e = max (e + m.size - prec) emin

instance dec_valid_finite (e m) : decidable (valid_finite e m) :=
by unfold valid_finite; apply_instance

inductive float
| inf : bool → float
| nan : float
| finite : bool → Π e m, valid_finite e m → float

def float.is_finite : float → bool
| (float.finite s e m f) := tt
| _ := ff

def to_rat : Π (f : float), f.is_finite → ℚ
| (float.finite s e m f) _ :=
  let (n, d) := int.shift2 m 1 e,
      r := rat.mk_nat n d in
  if s then -r else r

theorem float.zero.valid : valid_finite emin 0 :=
⟨begin
  rw add_sub_assoc,
  apply le_add_of_nonneg_right,
  apply sub_nonneg_of_le,
  apply int.coe_nat_le_coe_nat_of_le,
  exact C.prec_pos
end,
suffices prec ≤ 2 * emax,
begin
  rw ← int.coe_nat_le at this,
  rw ← sub_nonneg at *,
  simp only [emin, emax] at *,
  ring_nf,
  assumption
end, le_trans C.prec_max (nat.le_mul_of_pos_left dec_trivial),
by rw max_eq_right; simp [sub_eq_add_neg]⟩

def float.zero (s : bool) : float :=
float.finite s emin 0 float.zero.valid

instance : inhabited float := ⟨float.zero tt⟩

protected def float.sign' : float → semiquot bool
| (float.inf s) := pure s
| float.nan := ⊤
| (float.finite s e m f) := pure s

protected def float.sign : float → bool
| (float.inf s) := s
| float.nan := ff
| (float.finite s e m f) := s

protected def float.is_zero : float → bool
| (float.finite s e 0 f) := tt
| _ := ff

protected def float.neg : float → float
| (float.inf s) := float.inf (bnot s)
| float.nan := float.nan
| (float.finite s e m f) := float.finite (bnot s) e m f

def div_nat_lt_two_pow (n d : ℕ) : ℤ → bool
| (int.of_nat e) := n < d.shiftl e
| -[1+ e] := n.shiftl e.succ < d


-- TODO(Mario): Prove these and drop 'meta'
meta def of_pos_rat_dn (n : ℕ+) (d : ℕ+) : float × bool :=
begin
  let e₁ : ℤ := n.1.size - d.1.size - prec,
  cases h₁ : int.shift2 d.1 n.1 (e₁ + prec) with d₁ n₁,
  let e₂ := if n₁ < d₁ then e₁ - 1 else e₁,
  let e₃ := max e₂ emin,
  cases h₂ : int.shift2 d.1 n.1 (e₃ + prec) with d₂ n₂,
  let r := rat.mk_nat n₂ d₂,
  let m := r.floor,
  refine (float.finite ff e₃ (int.to_nat m) _, r.denom = 1),
  { exact undefined }
end

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

instance : has_neg float := ⟨float.neg⟩

meta def add (mode : rmode) : float → float → float
| nan      _        := nan
| _        nan      := nan
| (inf tt) (inf ff) := nan
| (inf ff) (inf tt) := nan
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
| nan      _        := nan
| _        nan      := nan
| (inf s₁) f₂       := if f₂.is_zero then nan else inf (bxor s₁ f₂.sign)
| f₁       (inf s₂) := if f₁.is_zero then nan else inf (bxor f₁.sign s₂)
| (finite s₁ e₁ m₁ v₁) (finite s₂ e₂ m₂ v₂) :=
  let f₁ := finite s₁ e₁ m₁ v₁, f₂ := finite s₂ e₂ m₂ v₂ in
  of_rat mode (to_rat f₁ rfl * to_rat f₂ rfl)

meta def div (mode : rmode) : float → float → float
| nan      _        := nan
| _        nan      := nan
| (inf s₁) (inf s₂) := nan
| (inf s₁) f₂       := inf (bxor s₁ f₂.sign)
| f₁       (inf s₂) := zero (bxor f₁.sign s₂)
| (finite s₁ e₁ m₁ v₁) (finite s₂ e₂ m₂ v₂) :=
  let f₁ := finite s₁ e₁ m₁ v₁, f₂ := finite s₂ e₂ m₂ v₂ in
  if f₂.is_zero then inf (bxor s₁ s₂) else
  of_rat mode (to_rat f₁ rfl / to_rat f₂ rfl)

end float

end fp
