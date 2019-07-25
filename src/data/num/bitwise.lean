/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Bitwise operations using binary representation of integers.
-/

import data.num.basic data.bitvec

namespace pos_num

  def lor : pos_num → pos_num → pos_num
  | 1        (bit0 q) := bit1 q
  | 1        q        := q
  | (bit0 p) 1        := bit1 p
  | p        1        := p
  | (bit0 p) (bit0 q) := bit0 (lor p q)
  | (bit0 p) (bit1 q) := bit1 (lor p q)
  | (bit1 p) (bit0 q) := bit1 (lor p q)
  | (bit1 p) (bit1 q) := bit1 (lor p q)

  def land : pos_num → pos_num → num
  | 1        (bit0 q) := 0
  | 1        _        := 1
  | (bit0 p) 1        := 0
  | _        1        := 1
  | (bit0 p) (bit0 q) := num.bit0 (land p q)
  | (bit0 p) (bit1 q) := num.bit0 (land p q)
  | (bit1 p) (bit0 q) := num.bit0 (land p q)
  | (bit1 p) (bit1 q) := num.bit1 (land p q)

  def ldiff : pos_num → pos_num → num
  | 1        (bit0 q) := 1
  | 1        _        := 0
  | (bit0 p) 1        := num.pos (bit0 p)
  | (bit1 p) 1        := num.pos (bit0 p)
  | (bit0 p) (bit0 q) := num.bit0 (ldiff p q)
  | (bit0 p) (bit1 q) := num.bit0 (ldiff p q)
  | (bit1 p) (bit0 q) := num.bit1 (ldiff p q)
  | (bit1 p) (bit1 q) := num.bit0 (ldiff p q)

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

  def test_bit : pos_num → nat → bool
  | 1        0     := tt
  | 1        (n+1) := ff
  | (bit0 p) 0     := ff
  | (bit0 p) (n+1) := test_bit p n
  | (bit1 p) 0     := tt
  | (bit1 p) (n+1) := test_bit p n

  def one_bits : pos_num → nat → list nat
  | 1        d := [d]
  | (bit0 p) d := one_bits p (d+1)
  | (bit1 p) d := d :: one_bits p (d+1)

  def shiftl (p : pos_num) : nat → pos_num
  | 0     := p
  | (n+1) := bit0 (shiftl n)

  def shiftr : pos_num → nat → num
  | p        0     := num.pos p
  | 1        (n+1) := 0
  | (bit0 p) (n+1) := shiftr p n
  | (bit1 p) (n+1) := shiftr p n

end pos_num

namespace num

  def lor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := pos (p.lor q)

  def land : num → num → num
  | 0       q       := 0
  | p       0       := 0
  | (pos p) (pos q) := p.land q

  def ldiff : num → num → num
  | 0       q       := 0
  | p       0       := p
  | (pos p) (pos q) := p.ldiff q

  def lxor : num → num → num
  | 0       q       := q
  | p       0       := p
  | (pos p) (pos q) := p.lxor q

  def shiftl : num → nat → num
  | 0       n := 0
  | (pos p) n := pos (p.shiftl n)

  def shiftr : num → nat → num
  | 0       n := 0
  | (pos p) n := p.shiftr n

  def test_bit : num → nat → bool
  | 0       n := ff
  | (pos p) n := p.test_bit n

  def one_bits : num → list nat
  | 0       := []
  | (pos p) := p.one_bits 0

end num

/-- See `snum`. -/
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

/- The snum representation uses a bit string, essentially a list of 0 (ff) and 1 (tt) bits,
   and the negation of the MSB is sign-extended to all higher bits. -/
namespace nzsnum
  notation a :: b := bit a b

  def sign : nzsnum → bool
  | (msb b) := bnot b
  | (b :: p) := sign p

  @[pattern] def not : nzsnum → nzsnum
  | (msb b) := msb (bnot b)
  | (b :: p) := bnot b :: not p
  prefix ~ := not

  def bit0 : nzsnum → nzsnum := bit ff
  def bit1 : nzsnum → nzsnum := bit tt

  def head : nzsnum → bool
  | (msb b)  := b
  | (b :: p) := b

  def tail : nzsnum → snum
  | (msb b)  := snum.zero (bnot b)
  | (b :: p) := p

end nzsnum

namespace snum
  open nzsnum

  def sign : snum → bool
  | (zero z) := z
  | (nz p)   := p.sign

  @[pattern] def not : snum → snum
  | (zero z) := zero (bnot z)
  | (nz p)   := ~p
  prefix ~ := not

  @[pattern] def bit : bool → snum → snum
  | b (zero z) := if b = z then zero b else msb b
  | b (nz p)   := p.bit b

  notation a :: b := bit a b

  def bit0 : snum → snum := bit ff
  def bit1 : snum → snum := bit tt

  theorem bit_zero (b) : b :: zero b = zero b := by cases b; refl

  theorem bit_one (b) : b :: zero (bnot b) = msb b := by cases b; refl

end snum

namespace nzsnum
  open snum

  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p : nzsnum, C p
  | (msb b)  := by rw ←bit_one; exact s b (snum.zero (bnot b)) (z (bnot b))
  | (bit b p) := s b p (drec' p)
end nzsnum

namespace snum
  open nzsnum

  def head : snum → bool
  | (zero z) := z
  | (nz p)   := p.head

  def tail : snum → snum
  | (zero z) := zero z
  | (nz p)   := p.tail

  def drec' {C : snum → Sort*} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p, C p
  | (zero b) := z b
  | (nz p)   := p.drec' z s

  def rec' {α} (z : bool → α) (s : bool → snum → α → α) : snum → α :=
  drec' z s

  def test_bit : nat → snum → bool
  | 0     p := head p
  | (n+1) p := test_bit n (tail p)

  def succ : snum → snum :=
  rec' (λ b, cond b 0 1) (λb p succp, cond b (ff :: succp) (tt :: p))

  def pred : snum → snum :=
  rec' (λ b, cond b (~1) ~0) (λb p predp, cond b (ff :: p) (tt :: predp))

  protected def neg (n : snum) : snum := succ ~n

  instance : has_neg snum := ⟨snum.neg⟩

  -- First bit is 0 or 1 (tt), second bit is 0 or -1 (tt)
  def czadd : bool → bool → snum → snum
  | ff ff p := p
  | ff tt p := pred p
  | tt ff p := succ p
  | tt tt p := p

end snum

namespace snum

def bits : snum → Π n, vector bool n
| p 0     := vector.nil
| p (n+1) := head p :: bits (tail p) n


def cadd : snum → snum → bool → snum :=
rec' (λ a p c, czadd c a p) $ λa p IH,
rec' (λb c, czadd c b (a :: p)) $ λb q _ c,
bitvec.xor3 a b c :: IH q (bitvec.carry a b c)

protected def add (a b : snum) : snum := cadd a b ff

instance : has_add snum := ⟨snum.add⟩

protected def sub (a b : snum) : snum := a + -b

instance : has_sub snum := ⟨snum.sub⟩

protected def mul (a : snum) : snum → snum :=
rec' (λ b, cond b (-a) 0) $ λb q IH,
cond b (bit0 IH + a) (bit0 IH)

instance : has_mul snum := ⟨snum.mul⟩

end snum
