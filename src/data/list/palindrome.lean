/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/

import data.list.basic

/-!
# Palindromes

This module defines *palindromes*, lists which are equal to their reverse.

The main result is the `palindrome` inductive type, and its associated `palindrome.rec_on` induction
principle. Also provided are conversions to and from other equivalent definitions.

## References

* [Pierre Castéran, *On palindromes*][casteran]

[casteran]: https://www.labri.fr/perso/casteran/CoqArt/inductive-prop-chap/palindrome.html

## Tags

palindrome, reverse, induction
-/

open list

variables {α : Type*}

/--
`palindrome l` asserts that `l` is a palindrome. This is defined inductively:

* The empty list is a palindrome;
* A list with one element is a palindrome;
* Adding the same element to both ends of a palindrome results in a bigger palindrome.
-/
inductive palindrome : list α → Prop
| nil : palindrome []
| singleton : ∀ x, palindrome [x]
| cons_concat : ∀ x {l}, palindrome l → palindrome (x :: (l ++ [x]))

namespace palindrome

lemma reverse_eq {l : list α} (p : palindrome l) : reverse l = l :=
palindrome.rec_on p rfl (λ _, rfl) (λ x l p h, by simp [h])

lemma of_reverse_eq {l : list α} : reverse l = l → palindrome l :=
begin
  refine bidirectional_rec_on l (λ _, palindrome.nil) (λ a _, palindrome.singleton a) _,
  intros x l y hp hr,
  rw [reverse_cons, reverse_append] at hr,
  rw head_eq_of_cons_eq hr,
  have : palindrome l, from hp (append_inj_left' (tail_eq_of_cons_eq hr) rfl),
  exact palindrome.cons_concat x this
end

lemma iff_reverse_eq {l : list α} : palindrome l ↔ reverse l = l :=
iff.intro reverse_eq of_reverse_eq

lemma append_reverse (l : list α) : palindrome (l ++ reverse l) :=
by { apply of_reverse_eq, rw [reverse_append, reverse_reverse] }

instance [decidable_eq α] (l : list α) : decidable (palindrome l) :=
decidable_of_iff' _ iff_reverse_eq

end palindrome
