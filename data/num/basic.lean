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

import data.pnat data.bool
universe u

inductive pos_num : Type
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num
instance : has_one pos_num := ⟨pos_num.one⟩
instance : decidable_eq pos_num := by tactic.mk_dec_eq_instance

inductive num : Type
| zero  : num
| pos   : pos_num → num
instance : has_zero num := ⟨num.zero⟩
instance : has_one num := ⟨num.pos 1⟩
instance : has_coe pos_num num := ⟨num.pos⟩
instance : decidable_eq num := by tactic.mk_dec_eq_instance

-- Representation of integers using trichotomy around zero
inductive znum : Type
| zero : znum
| pos  : pos_num → znum
| neg  : pos_num → znum
instance : has_zero znum := ⟨znum.zero⟩
instance : has_one znum := ⟨znum.pos 1⟩
instance : has_coe pos_num znum := ⟨znum.pos⟩
instance : decidable_eq znum := by tactic.mk_dec_eq_instance

-- Alternative representation of integers using a sign bit at the end
inductive nzsnum : Type
| one : bool → nzsnum
| bit : bool → nzsnum → nzsnum
inductive snum : Type
| zero : bool → snum
| nz : nzsnum → snum
instance : has_coe nzsnum snum := ⟨snum.nz⟩
instance : has_zero snum := ⟨snum.zero ff⟩
instance : has_one nzsnum := ⟨nzsnum.one tt⟩
instance : has_one snum := ⟨snum.nz 1⟩
instance : decidable_eq nzsnum := by tactic.mk_dec_eq_instance
instance : decidable_eq snum := by tactic.mk_dec_eq_instance

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

  def pred' : pos_num → option pos_num
  | 1        := none
  | (bit0 n) := some (option.cases_on (pred' n) 1 bit1)
  | (bit1 n) := bit0 n

  def pred (a : pos_num) : pos_num := (pred' a).get_or_else 1

  def size : pos_num → pos_num
  | 1        := 1
  | (bit0 n) := succ (size n)
  | (bit1 n) := succ (size n)

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

  instance : has_ordering pos_num := ⟨cmp⟩

  def psub : pos_num → pos_num → option pos_num
  | 1        b        := none
  | a        1        := pred' a
  | (bit0 a) (bit0 b) := bit0 <$> psub a b
  | (bit0 a) (bit1 b) := bit1 <$> psub a b
  | (bit1 a) (bit0 b) := bit1 <$> psub a b
  | (bit1 a) (bit1 b) := bit0 <$> psub a b

  protected def sub (a b : pos_num) : pos_num := (psub a b).get_or_else 1

  instance : has_sub pos_num := ⟨pos_num.sub⟩

end pos_num

section
  variables {α : Type u} [has_zero α] [has_one α] [has_add α]

  def cast_pos_num : pos_num → α
  | 1                := 1
  | (pos_num.bit0 a) := bit0 (cast_pos_num a)
  | (pos_num.bit1 a) := bit1 (cast_pos_num a)

  def cast_num : num → α
  | 0           := 0
  | (num.pos p) := cast_pos_num p

  @[priority 0] instance pos_num_coe : has_coe pos_num α := ⟨cast_pos_num⟩

  @[priority 0] instance num_nat_coe : has_coe num α := ⟨cast_num⟩
end

namespace nat
  def of_pos_num : pos_num → nat := cast_pos_num
  def of_num : num → nat := cast_num
end nat

instance : has_lt pos_num := ⟨λa b, (a : ℕ) < b⟩
instance : has_le pos_num := ⟨λa b, (a : ℕ) ≤ b⟩

instance : has_lt num := ⟨λa b, (a : ℕ) < b⟩
instance : has_le num := ⟨λa b, (a : ℕ) ≤ b⟩

namespace num
  open pos_num

  def succ' : num → pos_num
  | 0       := 1
  | (pos p) := succ p

  def succ (n : num) : num := pos (succ' n)

  def of_nat : nat → num
  | 0 := 0
  | (nat.succ n) := succ (of_nat n)

  instance nat_num_coe : has_coe nat num := ⟨of_nat⟩

  protected def add : num → num → num
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)

  instance : has_add num := ⟨num.add⟩

  def pred : num → num
  | 0       := 0
  | (pos p) := option.cases_on (pred' p) 0 pos

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

  instance : has_ordering num := ⟨cmp⟩

  protected def sub : num → num → num
  | a       0       := a
  | 0       b       := b
  | (pos a) (pos b) := option.cases_on (psub a b) 0 pos

  instance : has_sub num := ⟨num.sub⟩

  def to_znum : num → znum
  | 0       := 0
  | (pos a) := znum.pos a

  instance coe_znum : has_coe num znum := ⟨to_znum⟩

end num

namespace znum
  open pos_num

  def succ : znum → znum
  | 0       := 1
  | (pos a) := pos (pos_num.succ a)
  | (neg a) := option.cases_on (pos_num.pred' a) 0 neg

  def pred : znum → znum
  | 0       := neg 1
  | (pos a) := option.cases_on (pos_num.pred' a) 0 pos
  | (neg a) := neg (pos_num.succ a)

  def zneg : znum → znum
  | 0       := 0
  | (pos a) := neg a
  | (neg a) := pos a

  instance : has_neg znum := ⟨zneg⟩

  protected def add : znum → znum → znum
  | 0       a       := a
  | b       0       := b
  | (pos a) (pos b) := pos (a + b)
  | (pos a) (neg b) := option.cases_on (psub a b) (option.cases_on (psub b a) 0 neg) pos
  | (neg a) (pos b) := option.cases_on (psub a b) (option.cases_on (psub b a) 0 pos) neg
  | (neg a) (neg b) := neg (a + b)

  instance : has_add znum := ⟨znum.add⟩

  protected def sub (a b : znum) : znum := a + zneg b

  instance : has_sub znum := ⟨znum.sub⟩

  protected def mul : znum → znum → znum
  | 0       a       := 0
  | b       0       := 0
  | (pos a) (pos b) := pos (a * b)
  | (pos a) (neg b) := neg (a * b)
  | (neg a) (pos b) := neg (a * b)
  | (neg a) (neg b) := pos (a * b)

  instance : has_mul znum := ⟨znum.mul⟩

end znum

namespace int
  def of_znum : znum → ℤ
  | 0       := 0
  | (znum.pos a) := a
  | (znum.neg a) := -[1+ option.cases_on (pos_num.pred' a) 0 nat.of_pos_num]

  instance znum_coe : has_coe znum ℤ := ⟨of_znum⟩
end int

instance : has_lt znum := ⟨λa b, (a : ℤ) < b⟩
instance : has_le znum := ⟨λa b, (a : ℤ) ≤ b⟩

/- The snum representation uses a bit string, essentially a list of 0 (ff) and 1 (tt) bits,
   and the negation of the MSB is sign-extended to all higher bits. -/
namespace nzsnum
  notation a :: b := bit a b

  def sign : nzsnum → bool
  | (one b) := bnot b
  | (b :: p) := sign p

  @[pattern] def not : nzsnum → nzsnum
  | (one b) := one (bnot b)
  | (b :: p) := bnot b :: not p
  prefix ~ := not

  def bit0 : nzsnum → nzsnum := bit ff
  def bit1 : nzsnum → nzsnum := bit tt

  def head : nzsnum → bool
  | (one b)  := b
  | (b :: p) := b

  def tail : nzsnum → snum
  | (one b)  := snum.zero (bnot b)
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
  | b (zero z) := if b = z then zero b else one b
  | b (nz p)   := p.bit b

  notation a :: b := bit a b

  def bit0 : snum → snum := bit ff
  def bit1 : snum → snum := bit tt

  theorem bit_zero (b) : b :: zero b = zero b := by cases b; refl

  theorem bit_one (b) : b :: zero (bnot b) = one b := by cases b; refl

end snum

namespace nzsnum
  open snum

  def drec' {C : snum → Sort u} (z : Π b, C (snum.zero b))
    (s : Π b p, C p → C (b :: p)) : Π p : nzsnum, C p
  | (one b)  := by rw ←bit_one; exact s b (snum.zero (bnot b)) (z (bnot b))
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

  def drec' {C : snum → Sort u} (z : Π b, C (snum.zero b))
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
