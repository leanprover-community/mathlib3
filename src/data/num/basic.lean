/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

Binary representation of integers using inductive types.

Note: Unlike in Coq, where this representation is preferred because of
the reliance on kernel reduction, in Lean this representation is discouraged
in favor of the "Peano" natural numbers `nat`, and the purpose of this
collection of theorems is to show the equivalence of the different approaches.
-/

import data.pnat data.bool data.vector data.bitvec

/-- The type of positive binary numbers.

     13 = 1101(base 2) = bit1 (bit0 (bit1 one)) -/
@[derive has_reflect, derive decidable_eq]
inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num
instance : has_one pos_num := ⟨pos_num.one⟩

/-- The type of nonnegative binary numbers, using `pos_num`.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one))) -/
@[derive has_reflect, derive decidable_eq]
inductive num : Type
| zero  : num
| pos   : pos_num → num
instance : has_zero num := ⟨num.zero⟩
instance : has_one num := ⟨num.pos 1⟩

/-- Representation of integers using trichotomy around zero.

     13 = 1101(base 2) = pos (bit1 (bit0 (bit1 one)))
     -13 = -1101(base 2) = neg (bit1 (bit0 (bit1 one))) -/
@[derive has_reflect, derive decidable_eq]
inductive znum : Type
| zero : znum
| pos  : pos_num → znum
| neg  : pos_num → znum
instance : has_zero znum := ⟨znum.zero⟩
instance : has_one znum := ⟨znum.pos 1⟩

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

namespace pos_num

  def bit (b : bool) : pos_num → pos_num := cond b bit1 bit0

  def succ : pos_num → pos_num
  | 1        := bit0 one
  | (bit1 n) := bit0 (succ n)
  | (bit0 n) := bit1 n

  def is_one : pos_num → bool
  | 1 := tt
  | _ := ff

  protected def add : pos_num → pos_num → pos_num
  | 1        b        := succ b
  | a        1        := succ a
  | (bit0 a) (bit0 b) := bit0 (add a b)
  | (bit1 a) (bit1 b) := bit0 (succ (add a b))
  | (bit0 a) (bit1 b) := bit1 (add a b)
  | (bit1 a) (bit0 b) := bit1 (add a b)

  instance : has_add pos_num := ⟨pos_num.add⟩

  def pred' : pos_num → num
  | 1        := 0
  | (bit0 n) := num.pos (num.cases_on (pred' n) 1 bit1)
  | (bit1 n) := num.pos (bit0 n)

  def pred (a : pos_num) : pos_num :=
  num.cases_on (pred' a) 1 id

  def size : pos_num → pos_num
  | 1        := 1
  | (bit0 n) := succ (size n)
  | (bit1 n) := succ (size n)

  def nat_size : pos_num → nat
  | 1        := 1
  | (bit0 n) := nat.succ (nat_size n)
  | (bit1 n) := nat.succ (nat_size n)

  protected def mul (a : pos_num) : pos_num → pos_num
  | 1        := a
  | (bit0 b) := bit0 (mul b)
  | (bit1 b) := bit0 (mul b) + a

  instance : has_mul pos_num := ⟨pos_num.mul⟩

  def of_nat_succ : ℕ → pos_num
  | 0            := 1
  | (nat.succ n) := succ (of_nat_succ n)

  def of_nat (n : ℕ) : pos_num := of_nat_succ (nat.pred n)

  open ordering
  def cmp : pos_num → pos_num → ordering
  | 1        1        := eq
  | _        1        := gt
  | 1        _        := lt
  | (bit0 a) (bit0 b) := cmp a b
  | (bit0 a) (bit1 b) := ordering.cases_on (cmp a b) lt lt gt
  | (bit1 a) (bit0 b) := ordering.cases_on (cmp a b) lt gt gt
  | (bit1 a) (bit1 b) := cmp a b

  instance : has_lt pos_num := ⟨λa b, cmp a b = ordering.lt⟩
  instance : has_le pos_num := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel pos_num (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel pos_num (≤)
  | a b := by dsimp [(≤)]; apply_instance

end pos_num

section
  variables {α : Type*} [has_zero α] [has_one α] [has_add α]

  def cast_pos_num : pos_num → α
  | 1                := 1
  | (pos_num.bit0 a) := bit0 (cast_pos_num a)
  | (pos_num.bit1 a) := bit1 (cast_pos_num a)

  def cast_num : num → α
  | 0           := 0
  | (num.pos p) := cast_pos_num p

  @[priority 0] instance pos_num_coe : has_coe pos_num α := ⟨cast_pos_num⟩

  @[priority 0] instance num_nat_coe : has_coe num α := ⟨cast_num⟩

  instance : has_repr pos_num := ⟨λ n, repr (n : ℕ)⟩
  instance : has_repr num := ⟨λ n, repr (n : ℕ)⟩
end

namespace num
  open pos_num

  def succ' : num → pos_num
  | 0       := 1
  | (pos p) := succ p

  def succ (n : num) : num := pos (succ' n)

  protected def add : num → num → num
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)

  instance : has_add num := ⟨num.add⟩

  protected def bit0 : num → num
  | 0       := 0
  | (pos n) := pos (pos_num.bit0 n)

  protected def bit1 : num → num
  | 0       := 1
  | (pos n) := pos (pos_num.bit1 n)

  def bit (b : bool) : num → num := cond b num.bit1 num.bit0

  def size : num → num
  | 0       := 0
  | (pos n) := pos (pos_num.size n)

  def nat_size : num → nat
  | 0       := 0
  | (pos n) := pos_num.nat_size n

  protected def mul : num → num → num
  | 0       _       := 0
  | _       0       := 0
  | (pos a) (pos b) := pos (a * b)

  instance : has_mul num := ⟨num.mul⟩

  open ordering
  def cmp : num → num → ordering
  | 0       0       := eq
  | _       0       := gt
  | 0       _       := lt
  | (pos a) (pos b) := pos_num.cmp a b

  instance : has_lt num := ⟨λa b, cmp a b = ordering.lt⟩
  instance : has_le num := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel num (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel num (≤)
  | a b := by dsimp [(≤)]; apply_instance

  def to_znum : num → znum
  | 0       := 0
  | (pos a) := znum.pos a

  def to_znum_neg : num → znum
  | 0       := 0
  | (pos a) := znum.neg a

  def of_nat' : ℕ → num :=
  nat.binary_rec 0 (λ b n, cond b num.bit1 num.bit0)

end num

namespace znum
  open pos_num

  def zneg : znum → znum
  | 0       := 0
  | (pos a) := neg a
  | (neg a) := pos a

  instance : has_neg znum := ⟨zneg⟩

  def abs : znum → num
  | 0       := 0
  | (pos a) := num.pos a
  | (neg a) := num.pos a

  def succ : znum → znum
  | 0       := 1
  | (pos a) := pos (pos_num.succ a)
  | (neg a) := (pos_num.pred' a).to_znum_neg

  def pred : znum → znum
  | 0       := neg 1
  | (pos a) := (pos_num.pred' a).to_znum
  | (neg a) := neg (pos_num.succ a)

  protected def bit0 : znum → znum
  | 0       := 0
  | (pos n) := pos (pos_num.bit0 n)
  | (neg n) := neg (pos_num.bit0 n)

  protected def bit1 : znum → znum
  | 0       := 1
  | (pos n) := pos (pos_num.bit1 n)
  | (neg n) := neg (num.cases_on (pred' n) 1 pos_num.bit1)

  protected def bitm1 : znum → znum
  | 0       := neg 1
  | (pos n) := pos (num.cases_on (pred' n) 1 pos_num.bit1)
  | (neg n) := neg (pos_num.bit1 n)

  def of_int' : ℤ → znum
  | (n : ℕ) := num.to_znum (num.of_nat' n)
  | -[1+ n] := num.to_znum_neg (num.of_nat' (n+1))

end znum

namespace pos_num
  open znum

  def sub' : pos_num → pos_num → znum
  | a        1        := (pred' a).to_znum
  | 1        b        := (pred' b).to_znum_neg
  | (bit0 a) (bit0 b) := (sub' a b).bit0
  | (bit0 a) (bit1 b) := (sub' a b).bitm1
  | (bit1 a) (bit0 b) := (sub' a b).bit1
  | (bit1 a) (bit1 b) := (sub' a b).bit0

  def of_znum' : znum → option pos_num
  | (znum.pos p) := some p
  | _            := none

  def of_znum : znum → pos_num
  | (znum.pos p) := p
  | _            := 1

  protected def sub (a b : pos_num) : pos_num :=
  match sub' a b with
  | (znum.pos p) := p
  | _ := 1
  end

  instance : has_sub pos_num := ⟨pos_num.sub⟩
end pos_num

namespace num
  def ppred : num → option num
  | 0       := none
  | (pos p) := some p.pred'

  def pred : num → num
  | 0       := 0
  | (pos p) := p.pred'

  def div2 : num → num
  | 0 := 0
  | 1 := 0
  | (pos (pos_num.bit0 p)) := pos p
  | (pos (pos_num.bit1 p)) := pos p

  def of_znum' : znum → option num
  | 0            := some 0
  | (znum.pos p) := some (pos p)
  | (znum.neg p) := none

  def of_znum : znum → num
  | (znum.pos p) := pos p
  | _            := 0

  def sub' : num → num → znum
  | 0       0       := 0
  | (pos a) 0       := znum.pos a
  | 0       (pos b) := znum.neg b
  | (pos a) (pos b) := a.sub' b

  def psub (a b : num) : option num :=
  of_znum' (sub' a b)

  protected def sub (a b : num) : num :=
  of_znum (sub' a b)

  instance : has_sub num := ⟨num.sub⟩
end num

namespace znum
  open pos_num

  protected def add : znum → znum → znum
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)
  | (pos a) (neg b) := sub' a b
  | (neg a) (pos b) := sub' b a
  | (neg a) (neg b) := neg (a + b)

  instance : has_add znum := ⟨znum.add⟩

  protected def mul : znum → znum → znum
  | 0       a       := 0
  | b       0       := 0
  | (pos a) (pos b) := pos (a * b)
  | (pos a) (neg b) := neg (a * b)
  | (neg a) (pos b) := neg (a * b)
  | (neg a) (neg b) := pos (a * b)

  instance : has_mul znum := ⟨znum.mul⟩

  open ordering
  def cmp : znum → znum → ordering
  | 0       0       := eq
  | (pos a) (pos b) := pos_num.cmp a b
  | (neg a) (neg b) := pos_num.cmp b a
  | (pos _) _       := gt
  | (neg _) _       := lt
  | _       (pos _) := lt
  | _       (neg _) := gt

  instance : has_lt znum := ⟨λa b, cmp a b = ordering.lt⟩
  instance : has_le znum := ⟨λa b, ¬ b < a⟩

  instance decidable_lt : @decidable_rel znum (<)
  | a b := by dsimp [(<)]; apply_instance

  instance decidable_le : @decidable_rel znum (≤)
  | a b := by dsimp [(≤)]; apply_instance

end znum

namespace pos_num
  
  def divmod_aux (d : pos_num) (q r : num) : num × num :=
  match num.of_znum' (num.sub' r (num.pos d)) with
  | some r' := (num.bit1 q, r')
  | none    := (num.bit0 q, r)
  end
  
  def divmod (d : pos_num) : pos_num → num × num
  | (bit0 n) := let (q, r₁) := divmod n in
    divmod_aux d q (num.bit0 r₁)
  | (bit1 n) := let (q, r₁) := divmod n in
    divmod_aux d q (num.bit1 r₁)
  | 1        := divmod_aux d 0 1

  def div' (n d : pos_num) : num := (divmod d n).1

  def mod' (n d : pos_num) : num := (divmod d n).2

  def sqrt_aux1 (b : pos_num) (r n : num) : num × num :=
  match num.of_znum' (n.sub' (r + num.pos b)) with
  | some n' := (r.div2 + num.pos b, n')
  | none := (r.div2, n)
  end
    
  def sqrt_aux : pos_num → num → num → num
  | b@(bit0 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | b@(bit1 b') r n := let (r', n') := sqrt_aux1 b r n in sqrt_aux b' r' n'
  | 1           r n := (sqrt_aux1 1 r n).1
/-

def sqrt_aux : ℕ → ℕ → ℕ → ℕ
| b r n := if b0 : b = 0 then r else
  let b' := shiftr b 2 in
  have b' < b, from sqrt_aux_dec b0,
  match (n - (r + b : ℕ) : ℤ) with
  | (n' : ℕ) := sqrt_aux b' (div2 r + b) n'
  | _ := sqrt_aux b' (div2 r) n
  end

/-- `sqrt n` is the square root of a natural number `n`. If `n` is not a
  perfect square, it returns the largest `k:ℕ` such that `k*k ≤ n`. -/
def sqrt (n : ℕ) : ℕ :=
match size n with
| 0      := 0
| succ s := sqrt_aux (shiftl 1 (bit0 (div2 s))) 0 n
end
-/

end pos_num

namespace num

  def div : num → num → num
  | 0       _       := 0
  | _       0       := 0
  | (pos n) (pos d) := pos_num.div' n d

  def mod : num → num → num
  | 0       _       := 0
  | n       0       := n
  | (pos n) (pos d) := pos_num.mod' n d

  instance : has_div num := ⟨num.div⟩
  instance : has_mod num := ⟨num.mod⟩

  def gcd_aux : nat → num → num → num
  | 0            a b := b
  | (nat.succ n) 0 b := b
  | (nat.succ n) a b := gcd_aux n (b % a) a

  def gcd (a b : num) : num :=
  if a ≤ b then
    gcd_aux (a.nat_size + b.nat_size) a b
  else
    gcd_aux (b.nat_size + a.nat_size) b a

end num

namespace znum

  def div : znum → znum → znum
  | 0       _       := 0
  | _       0       := 0
  | (pos n) (pos d) := num.to_znum (pos_num.div' n d)
  | (pos n) (neg d) := num.to_znum_neg (pos_num.div' n d)
  | (neg n) (pos d) := neg (pos_num.pred' n / num.pos d).succ'
  | (neg n) (neg d) := pos (pos_num.pred' n / num.pos d).succ'

  def mod : znum → znum → znum
  | 0       d := 0
  | (pos n) d := num.to_znum (num.pos n % d.abs)
  | (neg n) d := d.abs.sub' (pos_num.pred' n % d.abs).succ

  instance : has_div znum := ⟨znum.div⟩
  instance : has_mod znum := ⟨znum.mod⟩

  def gcd (a b : znum) : num := a.abs.gcd b.abs

end znum

section
  variables {α : Type*} [has_zero α] [has_one α] [has_add α] [has_neg α]

  def cast_znum : znum → α
  | 0            := 0
  | (znum.pos p) := p
  | (znum.neg p) := -p

  @[priority 0] instance znum_coe : has_coe znum α := ⟨cast_znum⟩

  instance : has_repr znum := ⟨λ n, repr (n : ℤ)⟩
end

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

  def bits : snum → Π n, vector bool n
  | p 0     := vector.nil
  | p (n+1) := head p :: bits (tail p) n

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

namespace int
  def of_snum : snum → ℤ :=
  snum.rec' (λ a, cond a (-1) 0) (λa p IH, cond a (bit1 IH) (bit0 IH))

  instance snum_coe : has_coe snum ℤ := ⟨of_snum⟩
end int

instance : has_lt snum := ⟨λa b, (a : ℤ) < b⟩
instance : has_le snum := ⟨λa b, (a : ℤ) ≤ b⟩
