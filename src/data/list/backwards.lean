/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import data.list.basic

/-!
# Backwards recursors on lists
This file contains the function `list.backward_rec` which performs induction on lists by appending
elements to the end of the list instead of consing on the front.
 -/

universes u v

variable {α : Type u}

namespace list

/-- Backwards recursor on lists, inducts by appending elements to the end of the list -/
@[elab_as_eliminator]
def backwards_rec {α : Type u} {P : list α → Sort v} (hPempty : P [])
  (hPind : ∀ l x, P l → P (l ++ [x])) (l : list α) : P l :=
begin
  rw ←reverse_reverse l,
  induction l.reverse,
  { exact hPempty },
  { rw reverse_cons, exact hPind _ _ ih },
end

/-- Backwards recursor on lists, inducts by appending elements to the end of the list -/
@[elab_as_eliminator]
def backwards_rec_on {α : Type u} {P : list α → Sort v} (l : list α) (hPempty : P [])
  (hPind : ∀ l x, P l → P (l ++ [x])) : P l := backwards_rec hPempty hPind l

end list
