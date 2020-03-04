import algebra.group_power
import category.liftable

import data.bitvec
import data.list.basic
import data.stream
import tactic.cache
-- import util.data.list
import data.fin
-- import util.meta.tactic

import tactic.interactive
import tactic.norm_num

import system.io
import system.random

open list io applicative

universes u v w

@[reducible]
def rand_g (g : Type) := state (ulift g)
@[reducible]
def rand := rand_g std_gen

instance (g : Type) : liftable (rand_g.{u} g) (rand_g.{v} g) :=
@state_t.liftable' _ _ _ _ _ _ _ _ _  (equiv.ulift.trans.{u u u u u} equiv.ulift.symm)

open ulift

def random.next {gen : Type} [random_gen gen] : rand_g gen ℕ :=
⟨ prod.map id up ∘ random_gen.next ∘ down ⟩

def range {α : Type u} [has_le α] (i j : α) :=
{ x : α // i ≤ x ∧ x ≤ j }

infix ` .. `:41 := range

open stream

class random (α : Type u) extends has_le α :=
(random : Π (g : Type) [random_gen g], rand_g g α)
(random_r : Π g [random_gen g] (x y : α),
              x ≤ y →
              rand_g g (x .. y))
(random_series : Π (gen : Type) [random_gen gen], gen → stream α :=
by { intros, resetI,
     exact corec prod.fst ((random gen).run ∘ prod.snd) ( (random gen).run ⟨ a ⟩ ) } )
(random_series_r : Π (g : Type) [random_gen g] (x y : α)
                        (h : x ≤ y),
                        g →
                        stream (x .. y) :=
by { introsI,
     exact corec prod.fst ((random_r g x y h).run ∘ prod.snd) ((random_r g x y h).run ⟨ a ⟩) } )

namespace tactic.interactive

-- meta def time_in_nanos : tactic ℕ :=
-- do time ← tactic.unsafe_run_io (@io.cmd { cmd := "gdate", args := [ "+%s%N" ] } ),
--    pure time.to_nat

meta def check_range : tactic unit :=
assumption <|> do
`[apply of_as_true, trivial]

end tactic.interactive

export tactic.interactive (check_range)

namespace io

def read_dev_random (n : ℕ) : io (array n char) := do
fh ← mk_file_handle "/dev/random" mode.read tt,
buf ← fs.read fh n,
fs.close fh,
if h : buf.size = n
then return (cast (by rw h) buf.to_array)
else io.fail "wrong number of bytes read from /dev/random"

def accum_char (w : ℕ) (c : char) : ℕ :=
c.to_nat + 256 * w

def mk_generator : io std_gen := do
x ← io.read_dev_random 8,
return $ mk_std_gen (foldl accum_char 0 $ x.to_list : ℕ)

variables {α : Type}

def run_rand (cmd : _root_.rand α) : io α :=
do g ← io.mk_generator,
   return $ (cmd.run ⟨g⟩).1

variable [random α]

def random : io α :=
io.run_rand (random.random α _)

def random_r (x y : α) (p : x ≤ y . check_range) : io (x .. y) :=
io.run_rand (random.random_r _ x y p)

def random_series : io (stream α) := do
g ← io.mk_generator,
return $ random.random_series _ _ g

def random_series_r (x y : α) (h : x ≤ y . check_range) : io (stream $ x .. y) := do
g ← io.mk_generator,
return $ random.random_series_r _ x y h g

end io

namespace tactic.interactive

meta def mk_generator : tactic std_gen := do
tactic.unsafe_run_io @io.mk_generator

meta def tactic' (α : Type u) : Type (max u 1) :=
Π (β : Type), (α → tactic β) → tactic β

meta def run_rand' {α : Type u} (cmd : rand α) (β : Type) (tac : α → tactic β)
: tactic β := do
g ← mk_generator,
tac (cmd.run ⟨g⟩).1

section random'

variables {α : Type u}
variable [random α]

meta def random' : tactic' α :=
run_rand' (random.random _ _)

meta def random_r' (x y : α) (p : x ≤ y . check_range) : tactic' (x .. y) :=
run_rand' (random.random_r _ x y p)

meta def random_series' : tactic' (stream α)
 | β cmd := do
g ← mk_generator,
cmd $ random.random_series _ std_gen g

meta def random_series_r' (x y : α) (h : x ≤ y . check_range) : tactic' (stream $ x .. y)
 | β cmd := do
g ← mk_generator,
cmd $ random.random_series_r std_gen x y h g

end random'

section random

variable {α : Type}
variable [random α]

meta def random : tactic α :=
random' _ return

meta def random_r (x y : α) (p : x ≤ y . check_range) : tactic (x .. y) :=
random_r' _ _ p _ return

meta def random_series : tactic (stream α) :=
random_series' _ return

meta def random_series_r (x y : α) (h : x ≤ y . check_range) : tactic (stream $ x .. y) :=
random_series_r' _ _ h _ return

end random

end tactic.interactive

instance : preorder bool :=
{ le := λ p q, p → q
, le_refl := by { introv h, apply h }
, le_trans := by { introv ha hb h, apply hb, apply ha h } }

namespace bool

def coerce (x y : bool) (p : x ≤ y) (i : bool) : x .. y := do
  if hx : x ≤ i ∧ i ≤ y
  then ⟨ i, hx ⟩
  else ⟨ x , le_refl x , p ⟩
open ulift
variables {gen : Type} [random_gen gen]
protected def get_random : rand_g gen bool :=
⟨ prod.map id up ∘ @rand_bool gen _ ∘ down ⟩

structure bool_generator (g : Type) :=
  (next : bool)
  (queue : ℕ × ℕ)
  (gen : g)

protected def first (g : gen) : bool_generator gen  :=
let (r,g') := random_gen.next g in
{ next := r % 2 = 1
, queue := (r / 2,30)
, gen := g' }

protected def next : bool_generator gen → bool_generator gen
 | ⟨_,(_,0),g⟩ := bool.first g
 | ⟨_,(n,k),g⟩ := ⟨(n%2 = 1),(n/2,k-1),g⟩

def random_series' (g : gen) : stream (bool_generator gen) :=
stream.iterate bool.next (bool.first g)

def random_series (g : gen) : stream bool :=
stream.map bool.bool_generator.next $ random_series' g

end bool

instance : random bool :=
{ to_has_le := by apply_instance
, random   := λ g, @bool.get_random _
, random_r := λ g _inst x y p, bool.coerce _ _ p <$> (@bool.get_random g _inst)
, random_series   := @bool.random_series
, random_series_r := λ gen _inst x y p g, stream.map (bool.coerce _ _ p) $ @bool.random_series _ _inst g }

instance (n : ℕ) : preorder (bitvec n) :=
{ le := λ x y, x.to_nat ≤ y.to_nat
, le_refl  := by { introv, apply nat.le_refl }
, le_trans := by { introv ha hb, apply nat.le_trans ha hb } }

lemma bitvec.le_def {n : ℕ} (x y : bitvec n)
: x ≤ y ↔ x.to_nat ≤ y.to_nat :=
by refl

open nat (succ one_add mod_eq_of_lt zero_lt_succ add_one succ_le_succ)

namespace stream

variable {α : Type u}

open list (length) stream (approx)

lemma length_approx
: ∀ (s : stream α) (n : ℕ), length (approx n s) = n
 | s 0 := rfl
 | s (succ n) := by simp [approx,length,one_add,length_approx]

end stream

variables {gen : Type} [random_gen gen]

def bitvec.random (n : ℕ) : rand_g gen (bitvec n) :=
⟨ λ ⟨ g ⟩,
let r := bool.random_series' g,
    v := map bool.bool_generator.next $ stream.approx n r in
have Hv : length v = n,
     by { simp [stream.length_approx _ _], },
⟨ ⟨ v, Hv ⟩ , ⟨ (r.nth $ succ n).gen ⟩ ⟩ ⟩

section coerce

parameters {i' n : ℕ}
parameters {x y : bitvec n}

parameters P' : x.to_nat ≤ y.to_nat
include P'

local infix ^ := nat.pow

lemma bitvec.interval_fits_in_word_size
: x.to_nat + i' % (1 + (y.to_nat - x.to_nat)) < 2^n :=
begin
  let x' := x.to_nat,
  let y' := y.to_nat,
  apply @lt_of_lt_of_le _ _ _ (x' + (y' - x' + 1)),
  { apply add_lt_add_left, simp,
    apply nat.mod_lt,
    rw one_add, apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    clear P' i',
    cases y with y Hy,
    unfold bitvec.to_nat vector.to_list subtype.val bitvec.bits_to_nat,
    rw [← reverse_reverse y, foldl_reverse,← Hy,← length_reverse],
    generalize : reverse y = z,
    clear x' x y' Hy y n,
    induction z with x xs,
    { rw [list.length,list.foldr,nat.pow] },
    { simp [foldr,length,one_add,pow_succ,flip,bitvec.add_lsb],
      transitivity succ (1 +
       (foldr (λ (b : bool) (a : ℕ), a + (a + cond b 1 0)) 0 xs +
          foldr (λ (b : bool) (a : ℕ), a + (a + cond b 1 0)) 0 xs)),
      { apply succ_le_succ, apply add_le_add_right,
        cases x, apply nat.zero_le, refl, },
      { simp!,
        rw [← nat.add_succ,← nat.add_succ,one_add,← nat.succ_add,mul_comm,← two_mul],
        apply nat.mul_le_mul_left,
        simp [flip,bitvec.add_lsb] at z_ih,
        apply z_ih } }, },
end
end coerce

open nat

def bitvec.coerce {n : ℕ} (x y : bitvec n) (P : x ≤ y)
  (i : bitvec n)
: (x .. y) :=
let x' := x.to_nat,
    y' := y.to_nat,
    i' := i.to_nat,
    r := i' % (y' - x' + 1) + x' in
have Hx : x ≤ bitvec.of_nat n r,
  begin
    unfold_locals r,
    simp [bitvec.le_def,bitvec.to_nat_of_nat],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    unfold_locals x' y' i',
    apply bitvec.interval_fits_in_word_size,
    apply P
  end,
have Hy : bitvec.of_nat n r ≤ y,
  begin
    unfold_locals r,
    rw [bitvec.le_def,bitvec.to_nat_of_nat,mod_eq_of_lt],
    transitivity (y' - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw ← add_one,
      apply mod_lt,
      rw add_one, apply zero_lt_succ },
    { transitivity x' + (y' - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P,nat.add_sub_cancel_left], },
    simp, apply bitvec.interval_fits_in_word_size P,
  end,
⟨ bitvec.of_nat _ r , Hx , Hy ⟩

def bitvec.random_series (n : ℕ) (g : gen) : stream (bitvec n) :=
stream.corec
(λ s, ⟨ stream.approx n s, stream.length_approx _ _ ⟩)
(stream.drop n)
(@random.random_series bool _ gen _ g)

instance random_bitvec (n : ℕ) : random (bitvec n) :=
{ to_has_le := by apply_instance
, random := λ _ inst, @bitvec.random _ inst n
, random_r := λ _ inst x y p, bitvec.coerce _ _ p <$> @bitvec.random _ inst n
, random_series := λ _ inst, @bitvec.random_series _ inst n
, random_series_r := λ _ inst x y p g, bitvec.coerce _ _ p ∘ @bitvec.random_series _ inst n g }

-- example : true :=
-- begin
-- tactic.trace "\n\n",
-- (do x ← (tactic.interactive.random : tactic (bitvec 16)),
--     tactic.trace (x : bitvec 16).to_nat),
-- (do x ← (tactic.interactive.random_series),
--     tactic.trace $ map bitvec.to_nat (stream.approx 10 x : list (bitvec 16))),
-- (do x ← (tactic.interactive.random_series_r (25 : bitvec 15) 100),
--     tactic.trace $ map (bitvec.to_nat ∘ subtype.val) (stream.approx 10 x)),
-- trivial
-- end

-- meta def main [io.interface] : io unit := do
-- print_ln "\n\n",
-- x ← (io.random : io (bitvec 16)),
-- print_ln (x : bitvec 16).to_nat,
-- x ← io.random_series,
-- print_ln $ map bitvec.to_nat (stream.approx 10 x : list (bitvec 16)),
-- x ← (io.random_series_r (25 : bitvec 15) 100),
-- print_ln $ map (bitvec.to_nat ∘ subtype.val) (stream.approx 10 x)

-- run_cmd tactic.run_io @main

open nat

lemma div_two_round_up
  (x : ℕ)
  (h₀ : 1 < x)
: (x + 1) / 2 < x :=
begin
  rw [div_lt_iff_lt_mul,norm_num.mul_bit0,mul_one,bit0],
  apply add_lt_add_left, apply h₀,
  apply of_as_true, trivial
end

def word_size : ℕ → ℕ
 | x :=
if h : 1 < x then
  have (x + 1) / 2 < x,
    from div_two_round_up _ h,
  succ $ word_size ((x + 1) / 2)
else 0

local infix ^ := nat.pow

lemma word_size_le_two_pow (n : ℕ)
: n ≤ 2^word_size n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n IH,
  by_cases h : 1 < n,
  { rw [word_size,if_pos h,nat.pow],
    cases n with n, { cases not_lt_zero _ h },
    change n < _,
    rw ← @div_lt_iff_lt_mul _ _ 2 dec_trivial,
    have h' := div_two_round_up (succ n) h,
    specialize IH ((succ n + 1) / 2) h', clear h h',
    rw [succ_add,← add_succ] at *,
    simp only [-succ_pos', add_zero] at *,
    have h : (n + 2 * 1) / 2 = n / 2 + 1 :=
       add_mul_div_left _ _ dec_trivial,
    rw [mul_one] at h,
    rw h at IH ⊢,
    apply IH },
  { rw [word_size,if_neg h,nat.pow],
    apply le_of_not_gt h }
end

namespace fin
section fin
parameter {n : ℕ}

def shift_31l : ℕ :=
by apply_normed 2^31

protected def random_aux : ℕ → ℕ → rand_g gen (fin (succ n))
 | 0 k := return $ fin.of_nat k
 | (succ n) k :=
do x ← random.next,
   random_aux n $ x + (k * shift_31l)

protected def random : rand_g gen (fin (succ n)) :=
let m := word_size n / 31 + 1 in
random_aux m 0

section coerce

parameters {i' r k : ℕ}
parameters {y : fin k}

-- def x' := x.val
-- def y' := y.val
parameters {x' : ℕ}

parameters P' : x' ≤ y.val
include P'

lemma fin.interval_fits_in_word_size
: x' + i' % (1 + (y.val - x')) < k :=
begin
  apply @lt_of_lt_of_le _ _ _ (x' + (y.val - x' + 1)),
  { apply add_lt_add_left, simp,
    apply nat.mod_lt,
    rw one_add, apply zero_lt_succ },
  { rw [← add_assoc,← nat.add_sub_assoc P',nat.add_sub_cancel_left,add_one],
    apply y.is_lt }
end
end coerce

protected def coerce {n : ℕ} (x y : fin (succ n)) (P : x ≤ y)
  (i : fin (succ n))
: (x .. y) :=
let x' := x.val,
    i' := i.val,
    r := i' % (y.val - x' + 1) + x' in
have P' : x.val ≤ y.val,
  by { rw ← le_def, apply P },
have Hx : x ≤ fin.of_nat r,
  begin
    unfold_locals r,
    simp [fin.le_def,fin.val_of_nat_eq_mod],
    rw [mod_eq_of_lt],
    { apply nat.le_add_right },
    apply fin.interval_fits_in_word_size,
    unfold_locals x',
    rw ← fin.le_def, apply P
  end,
have Hy : fin.of_nat r ≤ y,
  begin
    unfold_locals r,
    rw [fin.le_def,fin.val_of_nat_eq_mod,mod_eq_of_lt],
    transitivity (y.val - x') + x',
    { apply add_le_add_right,
      apply le_of_lt_succ,
      rw add_one,
      apply mod_lt,
      apply zero_lt_succ },
    { transitivity x' + (y.val - x'),
      apply le_of_eq, ac_refl,
      rw [← nat.add_sub_assoc P',nat.add_sub_cancel_left], },
    simp, apply fin.interval_fits_in_word_size P',
  end,
⟨ fin.of_nat r , Hx , Hy ⟩

protected def random_r (x y : fin (succ n)) (p : x ≤ y) : rand_g gen (x .. y) :=
fin.coerce _ _ p <$> fin.random

end fin
end fin

instance fin_random (n : ℕ) : random (fin (succ n)) :=
{ to_has_le := by apply_instance
, random := λ g, @fin.random _ g
, random_r := λ x y p, @fin.random_r n x y p }

open nat

def random_fin_of_pos : ∀ (n : ℕ) (h : 0 < n), random (fin n)
 | (succ n) _ := fin_random _
 | 0 h := false.elim (not_lt_zero _ h)

section
open stream

def try_bitvec_random : io unit := do
put_str_ln "",
y ← io.mk_generator,
let w := succ $ 31,
let i : bitvec w := 2,
let j : bitvec w := 10000,
print_ln (repr y),
x ← (io.random : io (bitvec w)), return x.to_nat,
x ← (io.random_r (i) j : io _), return (x.val.to_nat),
x ← (io.random_series : io (stream (bitvec w))),
    return $ map bitvec.to_nat $ approx 10 x,
x ← (io.random_series_r i j),
    return $ map (bitvec.to_nat ∘ subtype.val) $ approx 10 x,
return ()


def try_fin_random : io unit := do
put_str_ln "",
let n := by { apply_normed 2^31 },
let i : fin (succ n) := fin.of_nat 2,
let j : fin (succ n) := fin.of_nat 100000,
have dp : i ≤ j,
by { unfold_locals i j n,
     rw [fin.le_def,fin.val_of_nat,fin.val_of_nat]
     ; [ skip, apply succ_le_succ, apply succ_le_succ ]
     ; norm_num ; trivial, }, do
x ← (io.random : io (fin 10)), print_ln x.val,
x ← (io.random : io (fin (succ n))), return x,
x ← (io.random_r i j : io _), print_ln (x.val),
x ← (io.random_series : io (stream (fin (succ n)))), return $ approx 10 x,
x ← (io.random_series_r i j), return $ map subtype.val $ approx 10 x,
return ()

end

-- run_cmd do
--   tactic.timetac "fin_random:    " (tactic.unsafe_run_io @try_fin_random ),
--   tactic.timetac "bitvec_random: " (tactic.unsafe_run_io @try_bitvec_random),
--   tactic.trace "do"

-- fin_random:     46.1ms
-- bitvec_random:  785ms
