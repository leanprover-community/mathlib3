/-
Copyright (c) 2022 Damiano Testa and Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Junyan Xu
-/
import data.dfinsupp.order
import data.dfinsupp.ne_locus

/-!
# Lexicographic order on finitely supported dependent functions
This file defines the lexicographic order on `dfinsupp`.

TODO: port `finsupp.lex.linear_order` to `dfinsupp`.
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

instance [has_lt ι] [Π i, has_lt (α i)] : has_lt (lex (Π₀ i, α i)) :=
⟨λ f g, dfinsupp.lex (<) (λ i, (<)) (of_lex f) (of_lex g)⟩

lemma lex_lt_of_lt_of_preorder [Π i, preorder (α i)] (r) [hr : is_strict_order ι r]
  {x y : Π₀ i, α i} (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
begin
  obtain ⟨hle, j, hlt⟩ := pi.lt_def.1 hlt, classical,
  obtain ⟨i, hi, hl⟩ := (x.ne_locus y).finite_to_set.well_founded_on.has_min
    {i | x i < y i} ⟨⟨j, mem_ne_locus.2 hlt.ne⟩, hlt⟩, swap 3, { exact hr },
  exact ⟨i, λ k hk, ⟨hle k, not_not.1 $ λ h,
    hl ⟨k, mem_ne_locus.2 (ne_of_not_le h).symm⟩ ((hle k).lt_of_not_le h) hk⟩, hi⟩,
end

lemma lex_lt_of_lt [Π i, partial_order (α i)] (r) [is_strict_order ι r]
  {x y : Π₀ i, α i} (hlt : x < y) : pi.lex r (λ i, (<)) x y :=
by { simp_rw [pi.lex, le_antisymm_iff], exact lex_lt_of_lt_of_preorder r hlt }

instance lex.is_strict_order [linear_order ι] [Π i, partial_order (α i)] :
  is_strict_order (lex (Π₀ i, α i)) (<) :=
let i : is_strict_order (lex (Π i, α i)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

end has_zero

end dfinsupp
