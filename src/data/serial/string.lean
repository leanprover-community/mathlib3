
import data.serial.medium

universes u

namespace string.medium

abbreviation put_m' := medium.put_m'.{u} char
abbreviation put_m  := medium.put_m'.{u} char punit
abbreviation get_m  := medium.get_m.{u} char
export medium (hiding put_m put_m' get_m)

namespace put_m'
export medium.put_m'
end put_m'

namespace get_m
export medium.get_m
end get_m

def emit (s : string) : put_m :=
s.to_list.mmap' write_word

@[reducible] def reader := reader_t ℕ (state_t (option char) get_m)

def reader.run {α} (x : reader α) (n : ℕ) : get_m α :=
do (i,j) ← (x.run n).run none,
   guard j.is_none,
   pure i

def read_char : reader char :=
do some c ← get | ulift.down <$> monad_lift (monad_lift read_word : state_t (option char) get_m (ulift char)),
   put none,
   pure c

def unread (c : char) : reader unit :=
do none ← get | failure,
   put (some c)

def expect_char (c : char) : reader punit :=
do c' ← read_char,
   -- unread c',
   if c = c' then pure punit.star
             else failure

def expect (s : string) : reader unit :=
s.to_list.mmap' expect_char

-- def loop

def peek : reader char :=
do c ← read_char,
   c <$ unread c

protected def to_string_aux : put_m → string → string
| (put_m'.pure x) y := y
| (put_m'.write w f) y := to_string_aux (f punit.star) (y.push w)

instance : has_to_string put_m.{u} :=
⟨ λ x, string.medium.to_string_aux x "" ⟩

end string.medium
