/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/

import data.dlist

def dlist.join {α : Type*} : list (dlist α) → dlist α
 | [] := dlist.empty
 | (x :: xs) := x ++ dlist.join xs
