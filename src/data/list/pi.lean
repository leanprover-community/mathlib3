/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import tactic.ext
import tactic.split_ifs

/-!
# The cartesian product of lists
-/

namespace list
variables {ι : Type*} [decidable_eq ι] {α : ι → Sort*}

namespace pi
variables {i : ι} {l : list ι}

/-- Given `α : ι → Sort*`, a list `l` and a term `i`, as well as a term `a : α i` and a
function `f` such that `f j : α j` for all `i'` in `m`, `pi.cons a f` is a function `g` such
that `g i'' : α i''` for all `i''` in `i :: l`. -/
def cons (a : α i) (f : Π j ∈ l, α j) : Π j ∈ (i :: l), α j :=
λ j hj, if h : j = i then h.symm.rec a else f j (hj.resolve_left h)

@[simp] lemma cons_eta (f : Π j ∈ (i :: l), α j) :
  cons (f i (mem_cons_self _ _)) (λ j hj, f j (mem_cons_of_mem _ hj)) = f :=
by { ext j hj, dsimp [cons], split_ifs with H, { cases H, refl }, { refl } }

lemma map_cons (h : α i) (t : Π j ∈ l, α j)
  {α' : ι → Sort*} (f : ∀ ⦃j⦄, α j → α' j) :
  (λ j hj, f ((cons h t) j hj)) = cons (f h) (λ j hj, f (t j hj)) :=
by { ext j hj, dsimp [cons], split_ifs with H, { cases H, refl }, { refl }, }

lemma forall_rel_cons_ext (r : Π ⦃i⦄, α i → α i → Prop) {h₁ h₂ : α i} {t₁ t₂ : Π j ∈ l, α j}
  (hh : r h₁ h₂) (ht : ∀ (i : ι) (hi : i ∈ l), r (t₁ i hi) (t₂ i hi)) :
  ∀ j hj, r (cons h₁ t₁ j hj) (cons h₂ t₂ j hj) :=
by { intros j hj, dsimp [cons], split_ifs with H, { cases H, exact hh }, { exact ht _ _, } }

end pi

end list
