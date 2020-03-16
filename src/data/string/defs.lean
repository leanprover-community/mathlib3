import data.list.defs

namespace string

def map_tokens (c : char) (f : list string → list string) : string → string :=
intercalate (singleton c) ∘ f ∘ split (= c)

def over_list (f : list char → list char) : string → string :=
list.as_string ∘ f ∘ string.to_list

def split_on (c : char) (s : string) : list string :=
(s.to_list.split_on c).map list.as_string

/-- Tests whether the first string is a prefix of the second string -/
def is_prefix_of (x y : string) : bool :=
x.to_list.is_prefix_of y.to_list

/-- Tests whether the first string is a suffix of the second string -/
def is_suffix_of (x y : string) : bool :=
x.to_list.is_suffix_of y.to_list

/-- `get_rest s t` returns `some r` if `s = t ++ r`.
  If `t` is not a prefix of `s`, returns `none` -/
def get_rest (s t : string) : option string :=
list.as_string <$> s.to_list.get_rest t.to_list

/-- Removes the first `n` elements from the string `s` -/
def popn (s : string) (n : nat) : string :=
(s.mk_iterator.nextn n).next_to_string

end string
