
import data.serial.basic

universes u v

open ulift

variables {α : Type u} {β : Type v}

def prod.mk' : ulift.{v} α → ulift.{u} β → (α × β)
| ⟨ x ⟩ ⟨ y ⟩ := (x,y)

open serializer serial

instance : serial2 prod.{u v} :=
by mk_serializer (prod.mk' <$> ser_field_with' ser_α prod.fst <*> ser_field_with' ser_β prod.snd)

def sum.inl' : ulift.{v} α → (α ⊕ β)
| ⟨ x ⟩ := sum.inl x

def sum.inr' : ulift.{u} β → (α ⊕ β)
| ⟨ x ⟩ := sum.inr x

def sum.encode [serial.{u} α] [serial.{v} β] : α ⊕ β → put_m.{max u v}
| (sum.inl x) := write_word 1 >> encode (up.{v} x)
| (sum.inr x) := write_word 2 >> encode (up.{u} x)

def sum.decode [serial.{u} α] [serial.{v} β] : get_m (α ⊕ β) :=
select_tag
  [ (1,sum.inl' <$> decode _),
    (2,sum.inr' <$> decode _) ]

open medium (hiding put_m put_m' get_m)

instance {α β} [serial.{u} α] [serial.{v} β] : serial (α ⊕ β) :=
{ encode := sum.encode,
  decode := sum.decode,
  correctness :=
  by { rintro ⟨w⟩; simp [sum.encode,sum.decode,map_read_write,*], refl,
       rw read_write_tag_miss, simp [map_read_write], refl, intro h, cases h, } }

def word_sz : ℕ := unsigned_sz / 2

def nat.encode : ℕ → put_m
| n :=
let r := n / word_sz,
    w := n % word_sz in
have h : 2 * w + 1 < unsigned_sz,
  by { apply @lt_of_lt_of_le _ _ _ (2 * (w + 1)), simp [mul_add], norm_num,
       transitivity 2 * word_sz,
       { apply mul_le_mul, refl,
         { apply nat.succ_le_of_lt, apply nat.mod_lt,
           norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one] },
         apply nat.zero_le, apply nat.zero_le, },
       { rw mul_comm, apply nat.div_mul_le_self } },
if Hr : 1 ≤ r then
  have h : 2 * w < unsigned_sz,
    by { transitivity; [skip, assumption], apply nat.lt_succ_self } ,
  have h'' : word_sz > 0,
    by norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one],
  have h' : r < n,
    by { apply nat.div_lt_self, rw [nat.le_div_iff_mul_le,one_mul] at Hr,
         apply lt_of_lt_of_le h'' Hr, assumption,
         norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one] },
  do write_word ⟨2 * w, h⟩,
     nat.encode r
else
  write_word ⟨2 * w + 1, h⟩

def nat.decode_aux (coef : ℕ × ℕ) (w : unsigned) : get_m (ℕ ⊕ (ℕ × ℕ)) :=
let b := w.val % 2,
    w' := w.val / 2,
    c := coef.1,
    coef' := (c * word_sz, c * w' + coef.2) in
if b = 0 then pure (sum.inr coef')
         else pure (sum.inl coef'.2)

def nat.decode : get_m ℕ :=
get_m.loop nat.decode_aux pure (1,0)

instance : serial ℕ :=
{ encode := nat.encode,
  decode := nat.decode,
  correctness :=
begin
  intro, dsimp [nat.decode],
  suffices : get_m.loop nat.decode_aux pure (1, 0) -<< nat.encode w = pure (1 * w + 0),
  { simp * },
  generalize : 0 = k,
  generalize : 1 = x,
  induction w using nat.strong_induction_on generalizing x k,
  rw [nat.encode], dsimp, split_ifs,
  { simp [nat.decode_aux], rw w_a,
    simp, congr,
    rw [nat.mul_div_right,mul_assoc,← nat.left_distrib x,add_comm,nat.mod_add_div],
    norm_num, apply nat.div_lt_self,
    { by_contradiction, revert h,
      apply not_lt_of_le, replace a := le_antisymm (le_of_not_lt a) (nat.zero_le _),
      subst w_n, norm_num [word_sz], },
    norm_num [word_sz,unsigned_sz,nat.succ_eq_add_one], },
  { simp [nat.decode_aux], rw if_neg,
    simp, dsimp [pure,read_write], congr, rw nat.add_mul_div_left,
    norm_num, replace h := le_antisymm (le_of_not_lt h) (nat.zero_le _),
    have := nat.mod_add_div w_n word_sz,
    simp [h] at this, exact this,
    { norm_num }, { norm_num } }
end }

def list.encode {α : Type u} (put : α → put_m) (xs : list α) : put_m.{u} :=
(encode (up.{u} xs.length) >> xs.mmap put >> pure punit.star : put_m' _)

def list.decode {α : Type u} (get : get_m α) : get_m.{u} (list α) :=
do n ← decode _,
   (list.iota $ down.{u} n).mmap $ λ _, get

instance : serial1 list.{u} :=
{ encode := @list.encode,
  decode := @list.decode,
  correctness :=
begin
  introsI,
  simp [list.encode,list.decode,seq_left_eq,(>>)],
  simp [bind_assoc,encode_decode_bind],
  induction w,
  { simp [nat.add_one,list.iota,mmap], refl },
  { simp [nat.add_one,list.iota,mmap,encode_decode_bind] with functor_norm,
    rw [read_write_mono (a _),read_write_mono_left w_ih], refl, }
end }

instance {p : Prop} [decidable p] : serial (plift p) :=
{ encode := λ w, (pure punit.star : put_m' _),
  decode := if h : p then pure ⟨ h ⟩ else get_m.fail,
  correctness := by { rintros ⟨ h ⟩, rw dif_pos h, refl } }
