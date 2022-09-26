/-
Copyright (c) 2022 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import data.finsupp.lex
import data.dfinsupp.order
import data.finsupp.to_dfinsupp

/-!
# Lexicographic order on finitely supported dependent functions
This file defines the lexicographic order on `dfinsupp`.

TODO: port `finsupp.ne_locus` and `finsupp.lex.linear_order` to `dfinsupp`.
-/

variables {ι : Type*} {α : ι → Type*}

namespace dfinsupp

section has_zero

variable [Π i, has_zero (α i)]

/-- `dfinsupp.lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.
The type synonym `lex (Π₀ i, α i)` has an order given by `dfinsupp.lex (<) (<)`.
-/
protected def lex (r : ι → ι → Prop) (s : Π i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
pi.lex r s x y

lemma _root_.finsupp.lex_eq_inv_image_dfinsupp_lex {α} [has_zero α]
  (r : ι → ι → Prop) (s : α → α → Prop) :
  finsupp.lex r s = inv_image (dfinsupp.lex r $ λ i, s) finsupp.to_dfinsupp := rfl

instance [has_lt ι] [Π i, has_lt (α i)] : has_lt (lex (Π₀ i, α i)) :=
⟨λ f g, dfinsupp.lex (<) (λ i, (<)) (of_lex f) (of_lex g)⟩

instance lex.is_strict_order [linear_order ι] [Π i, partial_order (α i)] :
  is_strict_order (lex (Π₀ i, α i)) (<) :=
let i : is_strict_order (lex (Π i, α i)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

end has_zero

-- connection between product order (has_le) and lex
-- connection between finsupp and dfinsupp
-- Add is_well_order (Π₀ i, α i) (<). (product order)
-- Future work: relation.cut_expand -> multiset.lex? Reorganize directory, hydra -> well_founded / lex

end dfinsupp
