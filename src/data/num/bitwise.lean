/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.num.basic
import data.bitvec.core

/-!
# Bitwise operations using binary representation of integers

## Definitions

* bitwise operations for `pos_num` and `num`,
* `snum`, a type that represents integers as a bit string with a sign bit at the end,
* arithmetic operations for `snum`.
-/

namespace pos_num

  /-- Bitwise "or" for `pos_num`. -/
  def lor : pos_num → pos_num → pos_num
  | 1        (bit0 q) := bit1 q
  | 1        q        := q
  | (bit0 p) 1        := bit1 p
  | p        1        := p
  | (bit0 p) (bit0 q) := bit0 (lor p q)
  | (bit0 p) (bit1 q) := bit1 (lor p q)
  | (bit1 p) (bit0 q) := bit1 (lor p q)
  | (bit1 p) (bit1 q) := bit1 (lor p q)

  /-- Bitwise "and" for `pos_num`. -/
  def land : pos_num → pos_num → num
  | 1        (bit0 q) := 0
  | 1        _        := 1
  | (bit0 p) 1        := 0
  | _        1        := 1
  | (bit0 p) (bit0 q) := num.bit0 (land p q)
  | (bit0 p) (bit1 q) := num.bit0 (land p q)
  | (bit1 p) (bit0 q) := num.bit0 (land p q)
  | (bit1 p) (bit1 q) := num.bit1 (land p q)

  /-- Bitwise `λ a b, a && !b` for `pos_num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
  def ldiff : pos_num → pos_num → num
  | 1        (bit0 q) := 1
  | 1        _        := 0
  | (bit0 p) 1        := num.pos (bit0 p)
  | (bit1 p) 1        := num.pos (bit0 p)
  | (bit0 p) (bit0 q) := num.bit0 (ldiff p q)
  | (bit0 p) (bit1 q) := num.bit0 (ldiff p q)
  | (bit1 p) (bit0 q) := num.bit1 (ldiff p q)
  | (bit1 p) (bit1 q) := num.bit0 (ldiff p q)

  /-- Bitwise "xor" for `pos_num`. -/
  def lxor : pos_num → pos_num → num
  | 1        1        := 0
  | 1        (bit0 q) := num.pos (bit1 q)
  | 1        (bit1 q) := num.pos (bit0 q)
  | (bit0 p) 1        := num.pos (bit1 p)
  | (bit1 p) 1        := num.pos (bit0 p)
  | (bit0 p) (bit0 q) := num.bit0 (lxor p q)
  | (bit0 p) (bit1 q) := num.bit1 (lxor p q)
  | (bit1 p) (bit0 q) := num.bit1 (lxor p q)
  | (bit1 p) (bit1 q) := num.bit0 (lxor p q)

  /-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
  def test_bit : pos_num → nat → bool
  | 1        0     := tt
  | 1        (n+1) := ff
  | (bit0 p) 0     := ff
  | (bit0 p) (n+1) := test_bit p n
  | (bit1 p) 0     := tt
  | (bit1 p) (n+1) := test_bit p n

  /-- `n.one_bits 0` is the list of indices of active bits in the binary representation of `n`. -/
  def one_bits : pos_num → nat → list nat
  | 1        d := [d]
  | (bit0 p) d := one_bits p (d+1)
  | (bit1 p) d := d :: one_bits p (d+1)

  /-- Left-shift the binary representation of a `pos_num`. -/
  def shiftl (p : pos_num) : nat → pos_num
  | 0     := p
  | (n+1) := bit0 (shiftl n)

  /-- Right-shift the binary representation of a `pos_num`. -/
  def shiftr : pos_num → nat → num
  | p        0     := num.pos p
  | 1        (n+1) := 0
  | (bit0 p) (n+1) := shiftr p n
  | (bit1 p) (n+1) := shiftr p n

end pos_num

namespace num

  /-- Bitwise "or" for `num`. -/
  def lor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := pos (p.lor q)

  /-- Bitwise "and" for `num`. -/
  def land : num → num → num
  | 0       q       := 0
  | p       0       := 0
  | (pos p) (pos q) := p.land q

  /-- Bitwise `λ a b, a && !b` for `num`. For example, `ldiff 5 9 = 4`:

     101
    1001
    ----
     100

  -/
  def ldiff : num → num → num
  | 0       q       := 0
  | p       0       := p
  | (pos p) (pos q) := p.ldiff q

  /-- Bitwise "xor" for `num`. -/
  def lxor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := p.lxor q

  /-- Left-shift the binary representation of a `num`. -/
  def shiftl : num → nat → num
  | 0       n := 0
  | (pos p) n := pos (p.shiftl n)

  /-- Right-shift the binary representation of a `pos_num`. -/
  def shiftr : num → nat → num
  | 0       n := 0
  | (pos p) n := p.shiftr n

  /-- `a.test_bit n` is `tt` iff the `n`-th bit (starting from the LSB) in the binary representation
      of `a` is active. If the size of `a` is less than `n`, this evaluates to `ff`. -/
  def test_bit : num → nat → bool
  | 0       n := ff
  | (pos p) n := p.test_bit n

  /-- `n.one_bits` is the list of indices of active bits in the binary representation of `n`. -/
  def one_bits : num → list nat
  | 0       := []
  | (pos p) := p.one_bits 0

end num

/-- This is a nonzero (and "non minus one") version of `snum`.
    See the documentation of `snum` for more details. -/
@[derive has_reflect, derive decidable_eq]
inductive nzsnum : Type
| msb : bool → nzsnum
| bit : bool → nzsnum → nzsnum

/-- Alternative representation of integers using a sign bit at the end.
  The convention on sign here is to have the argument to `msb` denote
  the sign of the MSB itself, with all higher bits set to the negation
  of this sign. The result is interpreted in two's complement.

     13  = ..0001101(base 2) = nz (bit1 (bit0 (bit1 (msb tt))))
     -13 = ..1110011(base 2) = nz (bit1 (bit1 (bit0 (msb ff))))

  As with `num`, a special case must be added for zero, which has no msb,
  but by two's complement symmetry there is a second special case for -1.
  Here the `bool` field indicates the sign of the number.

     0  = ..0000000(base 2) = zero ff
     -1 = ..1111111(base 2) = zero tt -/
@[derive has_reflect, derive decidable_eq]
inductive snum : Type
| zero : bool → snum
| nz : nzsnum → snum
instance : has_coe nzsnum snum := ⟨snum.nz⟩
instance : has_zero snum := ⟨snum.zero ff⟩
instance : has_one nzsnum := ⟨nzsnum.msb tt⟩
instance : has_one snum := ⟨snum.nz 1⟩
instance : inhabited nzsnum := ⟨1⟩
instance : inhabited snum := ⟨0⟩

/-!
The `snum` representation uses a bit string, essentially a list of 0 (`ff`) and 1 (`tt`) bits,
and the negation of the MSB is sign-extended to all higher bits.
-/
namespace nzsnum
  notation a :: b := bit a b

  /-- Sign of a `nzsnum`. -/
  def sign : nzsnum → bool
  | (msb b) := bnot b
  | (b :: p) := sign p

  /-- Bitwise `not` for `nzsnum`. -/
  @[pattern] def not : nzsnum → nzsnum
  | (msb b) := msb (bnot b)
  | (b :: p) := bnot b :: not p
  prefix `~`:100 := not

  /-- Add an inactive bit at the end of a `nzsnum`. This mimics `pos_num.bit0`. -/
  def bit0 : nzsnum → nzsnum := bit ff

  /-- Add an active bit at the end of a `nzsnum`. This mimics `pos_num.bit1`. -/
  def bit1 : nzsnum → nzsnum := bit tt

  /-- The `head` of a `nzsnum` is the boolean value of its LSB. -/
  def head : nzsnum → bool
  | (msb b)  := b
  | (b :: p) := b

  /-- The `tail` of a `nzsnum` is the `snum` obtained by removing the LSB.
      Edge cases: `tail 1 = 0` and `tail (-2) = -1`. -/
  def tail : nzsnum → snum
  | (msb b)  := snum.zero (bnot b)
  | (b :: p) := p

end nzsnum

namespace snum
  open nzsnum

  /-- Sign of a `snum`. -/
  def sign : snum → bool
  | (zero z) := z
  | (nz p)   := p.sign

  /-- Bitwise `not` for `snum`. -/
  @[pattern] def not : snum → snum
  | (zero z) := zero (bnot z)
  | (nz p)   := ~p
  prefix ~ := not

  /-- Add a bit at the end of a `snum`. This mimics `nzsnum.bit`. -/
  @[pattern] def bit : bool → snum → snum
  | b (zero z) := if b = z then zero b else msb b
  | b (nz p)   := p.bit b

  notation a :: b := bit a b

  /-- Add an inactive bit at the end of a `snum`. This mimics `znum.bit0`. -/
  def bit0 : snum → snum := bit ff

  /-- Add an active bit at the end of a `snum`. This mimics `znum.bit1`. -/
  def bit1 : snum → snum := bit tt

  theorem bit_zero (b) : b :: zero b = zero b := by cases b; refl

  theorem bit_one (b) : b :: zero (bnot b) = msb b := by cases b; refl

end snum

namespace nzsnum
  open snum

  /-- A dependent induction principle for `nzsnum`, with base cases
      `0 : snum` and `(-1) : snum`. -/
  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p : nzsnum, C p
  | (msb b)  := by rw ←bit_one; exact s b (snum.zero (bnot b)) (z (bnot b))
  | (bit b p) := s b p (drec' p)
end nzsnum

namespace snum
  open nzsnum

  /-- The `head` of a `snum` is the boolean value of its LSB. -/
  def head : snum → bool
  | (zero z) := z
  | (nz p)   := p.head

  /-- The `tail` of a `snum` is obtained by removing the LSB.
      Edge cases: `tail 1 = 0`, `tail (-2) = -1`, `tail 0 = 0` and `tail (-1) = -1`. -/
  def tail : snum → snum
  | (zero z) := zero z
  | (nz p)   := p.tail

  /-- A dependent induction principle for `snum` which avoids relying on `nzsnum`. -/
  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p, C p
  | (zero b) := z b
  | (nz p)   := p.drec' z s

  /-- An induction principle for `snum` which avoids relying on `nzsnum`. -/
  def rec' {α} (z : bool → α) (s : bool → snum → α → α) : snum → α :=
  drec' z s

  /-- `snum.test_bit n a` is `tt` iff the `n`-th bit (starting from the LSB) of `a` is active.
      If the size of `a` is less than `n`, this evaluates to `ff`. -/
  def test_bit : nat → snum → bool
  | 0     p := head p
  | (n+1) p := test_bit n (tail p)

  /-- The successor of a `snum` (i.e. the operation adding one). -/
  def succ : snum → snum :=
  rec' (λ b, cond b 0 1) (λb p succp, cond b (ff :: succp) (tt :: p))

  /-- The predecessor of a `snum` (i.e. the operation of removing one). -/
  def pred : snum → snum :=
  rec' (λ b, cond b (~1) ~0) (λb p predp, cond b (ff :: p) (tt :: predp))

  /-- The opposite of a `snum`. -/
  protected def neg (n : snum) : snum := succ ~n

  instance : has_neg snum := ⟨snum.neg⟩

  /-- `snum.czadd a b n` is `n + a - b` (where `a` and `b` should be read as either 0 or 1).
      This is useful to implement the carry system in `cadd`. -/
  def czadd : bool → bool → snum → snum
  | ff ff p := p
  | ff tt p := pred p
  | tt ff p := succ p
  | tt tt p := p

end snum

namespace snum

/-- `a.bits n` is the vector of the `n` first bits of `a` (starting from the LSB). -/
def bits : snum → Π n, vector bool n
| p 0     := vector.nil
| p (n+1) := head p ::ᵥ bits (tail p) n

def cadd : snum → snum → bool → snum :=
rec' (λ a p c, czadd c a p) $ λa p IH,
rec' (λb c, czadd c b (a :: p)) $ λb q _ c,
bitvec.xor3 a b c :: IH q (bitvec.carry a b c)

/-- Add two `snum`s. -/
protected def add (a b : snum) : snum := cadd a b ff

instance : has_add snum := ⟨snum.add⟩

/-- Substract two `snum`s. -/
protected def sub (a b : snum) : snum := a + -b

instance : has_sub snum := ⟨snum.sub⟩

/-- Multiply two `snum`s. -/
protected def mul (a : snum) : snum → snum :=
rec' (λ b, cond b (-a) 0) $ λb q IH,
cond b (bit0 IH + a) (bit0 IH)

instance : has_mul snum := ⟨snum.mul⟩

end snum
