/-
Copyright (c) 2020 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/

import data.stream.basic
import data.list.palindrome
import data.nat.fib
open list

/-!
# Fibonacci words

This file defines Fibonacci words via repeated substitution on binary digits. We represent a word as
`list bool`, with `ff` and `tt` corresponding to `0` and `1` respectively.

## References

* [J. Berstel, Fibonacci Words – A Survey](http://www-igm.univ-mlv.fr/~berstel/Articles/1985BookOfL.pdf)
* [Wikipedia](https://en.wikipedia.org/wiki/Fibonacci_word)
-/

/-- Auxiliary function for `fibword_morph`. -/
def fibword_morph_aux : bool → list bool
| ff := [ff, tt]
| tt := [ff]

/--
Substitution function that maps a Fibonacci word to its successor. This is called a "morphism"
because it preserves the monoid structure on lists.
-/
def fibword_morph (l : list bool) : list bool := l.bind fibword_morph_aux

lemma fibword_morph_append {x y} : fibword_morph (x ++ y) = fibword_morph x ++ fibword_morph y :=
by { unfold fibword_morph, rw bind_append }

lemma fibword_morph_cons {x l} : fibword_morph (x :: l) = fibword_morph_aux x ++ fibword_morph l :=
rfl

lemma fibword_morph_nil : fibword_morph [] = [] := rfl

lemma fibword_morph_ne_nil {l} (hne : l ≠ []) : fibword_morph l ≠ [] :=
begin
  cases l with x l, { contradiction },
  cases x; contradiction
end

lemma head_fibword_morph {l : list bool} : head (fibword_morph l) = ff :=
begin
  cases l with x l, { refl },
  cases x; refl
end

lemma palindrome_tail_fibword_morph {l : list bool} (p : palindrome l) :
  palindrome (tail (fibword_morph l)) :=
begin
  refine palindrome.rec_on p palindrome.nil _ _,
  -- l = [x]
  { intros x, cases x; exact palindrome.of_reverse_eq rfl },
  -- l = [x, ..., x]
  { intros x l p h,
    unfold fibword_morph,
    rw [cons_bind, bind_append, bind_singleton],
    cases l with y l,
    -- l = [x, x]
    { cases x; { rw fibword_morph_aux, exact palindrome.of_reverse_eq rfl } },
    -- l = [x, y, ..., y, x]
    { cases x;
      { rw [fibword_morph_aux, ←fibword_morph,
            ←cons_head_tail (fibword_morph_ne_nil (cons_ne_nil y l)),
            head_fibword_morph],
        apply palindrome.of_reverse_eq,
        simp [h.reverse_eq] } } }
end

/--
To compute the $n$th Fibonacci word, apply the substitution $n$ times to the initial word $0$.
-/
def fibword : ℕ → list bool := stream.iterate fibword_morph [ff]

lemma fibword_zero : fibword 0 = [ff] := rfl

lemma fibword_one : fibword 1 = [ff, tt] := rfl

lemma fibword_succ (n : ℕ) : fibword (n + 1) = fibword_morph (fibword n) := rfl

lemma fibword_succ_succ (n : ℕ) : fibword (n + 2) = fibword (n + 1) ++ fibword n :=
begin
  induction n with n h, { refl },
  change fibword_morph (fibword (n + 2)) =
    fibword_morph (fibword (n + 1)) ++ fibword_morph (fibword n),
  rw [←fibword_morph_append, h]
end

lemma fibword_ne_nil (n : ℕ) : fibword n ≠ [] :=
nat.rec_on n (cons_ne_nil _ _) (λ n h, fibword_succ n ▸ fibword_morph_ne_nil h)

/-- The length of a Fibonacci word is a Fibonacci number. -/
theorem length_fibword (n : ℕ) : length (fibword n) = nat.fib (n + 2) :=
begin
  refine @nat.strong_rec_on _ n _,
  intros n h,
  cases n with n, { refl },
  cases n with n, { refl },
  rw [fibword_succ_succ, nat.fib_succ_succ, length_append,
      h n (show n < n + 2, by norm_num), h (n + 1) (show n + 1 < n + 2, by norm_num),
      nat.add_comm]
end

/-- Every Fibonacci word (except the first) is either $p01$ or $p10$, where $p$ is a palindrome. -/
theorem palindrome_fibword {n} (hn : 0 < n)
  : ∃ l, palindrome l ∧ (fibword n = l ++ [ff, tt] ∨ fibword n = l ++ [tt, ff]) :=
begin
  refine nat.le_rec_on hn _ _,
  { rintros n ⟨l, p, h | h⟩;
    { use fibword_morph l ++ [ff],
      split,
      { cases l,
        { exact palindrome.singleton ff },
        { rw [←cons_head_tail (fibword_morph_ne_nil (cons_ne_nil _ _)),
              head_fibword_morph],
          exact palindrome.cons_concat ff (palindrome_tail_fibword_morph p) } },
      { rw [fibword_succ, h, fibword_morph_append],
        simp [show fibword_morph [ff, tt] = [ff, tt, ff], by refl,
              show fibword_morph [tt, ff] = [ff, ff, tt], by refl] } } },
  { exact ⟨[], palindrome.nil, or.inl rfl⟩ }
end
