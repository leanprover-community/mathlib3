/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.vector.basic
import computability.tm_to_partrec
import data.nat.log
import data.polynomial.eval

/-!
# TODO
-/

-- Note that we use the code type defined in turing.to_partrec, since this is over lists.
-- A type of codes that works over naturals will not let us compute without exponential slowdowns.
open turing.to_partrec

/--
The time that a `turing.to_partrec.code` takes to run on a particular list, as a partial function.
For the semantics of this definition of code, see `turing.to_partrec.code.eval`.
-/
def time : turing.to_partrec.code → list ℕ →. ℕ
| code.zero'       := pure 1
| code.succ        := pure 1
| code.tail        := pure 1
| (code.cons f fs) := λ l, time f l + time fs l + pure 1
| (code.comp f g)  := λ l, time g l + ((code.eval g l) >>= time f) + pure 1
| (code.case f g)  := λ l, l.head.elim (time f l.tail) (λ y _, time g (y :: l.tail)) + pure 1
| (code.fix f)     := λ l, ((@pfun.fix ((list ℕ) × ℕ) (ℕ) $
  λ ⟨v, n⟩,
  if v.head = 0
    then ((time f v.tail).map sum.inl)
    else (prod.mk <$> f.eval v.tail <*> (time f v.tail) + pure n).map sum.inr
) ⟨l, 0⟩)

/--
Holds for codes representing total functions, where `bound` is a function upper bounding the
runtime of the code over all input lists of length `l`.
-/
def time_bound (c : turing.to_partrec.code) (bound : ℕ → ℕ) : Prop :=
∀ (l : list ℕ) (len : ℕ), ∃ t ∈ time c l, l.length ≤ len -> t ≤ bound (len)

-- TODO time_bound lemmas for all the constructors (except maybe fix)
lemma time_bound_zero' : time_bound code.zero' (id 1) :=
begin
  tidy,
end

lemma time_bound_succ : time_bound code.succ (id 1) :=
begin
  tidy,
end

lemma time_bound_tail : time_bound code.tail (id 1) :=
begin
  tidy,
end

lemma time_bound_cons (f fs : code) (b bs : ℕ → ℕ) (hb : time_bound f b) (hbs : time_bound fs bs) :
  time_bound (code.cons f fs) (b + bs + id 1) :=
begin
  rw time_bound at *,
  intros l len,
  rw time,
  rcases hb l len with ⟨t, H, ht⟩,
  rcases hbs l len with ⟨ts, Hs, hts⟩,
  use t + ts + 1,
  split,
  simp,
  apply part.add_mem_add,
  apply part.add_mem_add,
  assumption,
  assumption,
  exact part.mem_some 1,
  simp,
  exact add_le_add ht hts,
end

/-- Time bound lemma for composition.
Note that we compose the f bound with the g bound plus the identity. This is because `g` may be a
function with a very short time bound that does not read its whole input. `bg + id`, though, is
guaranteed to upper bound the length of the input to f. -/
lemma time_bound_comp (f g : code) (bf bg : ℕ → ℕ) (hbf : time_bound f bf) (hbg : time_bound g bg) :
  time_bound (code.comp f g) (bf + (bf ∘ (bg + id)) + 1) :=
begin
  rw time_bound at *,
  sorry,
end


/--
The code `c` always terminates in polynomial time.
-/
def poly_time (c : turing.to_partrec.code) : Prop :=
∃ (p : polynomial ℕ), time_bound c (λ x, p.eval x) -- Why does this work but (p.eval) doesn't?

-- TODO poly_time lemmas for all the constructors (except maybe fix)
lemma poly_time_zero' : poly_time code.zero' :=
begin
  rw poly_time,
  use polynomial.C 1,
  tidy,
end

lemma poly_time_succ : poly_time code.succ :=
begin
  rw poly_time,
  sorry,
end

lemma poly_time_tail : poly_time code.tail :=
begin
  rw poly_time,
  sorry,
end

lemma poly_time_cons (f fs : code) (hf : poly_time f) (hfs : poly_time fs) :
  poly_time (code.cons f fs) :=
begin
  rw poly_time at *,
  rcases hf with ⟨fp, fpb⟩,
  rcases hfs with ⟨fps, fpbs⟩,
  use fp + fps + 1,
  simp only [polynomial.eval_add, polynomial.eval_one],
  apply time_bound_cons,
  assumption,
  assumption,
end

lemma poly_time_comp (f g : code) (hf : poly_time f) (hg : poly_time g) :
  poly_time (code.comp f g) :=
begin
  rw poly_time at *,
  rcases hf with ⟨fp, fpb⟩,
  rcases hg with ⟨gp, gpb⟩,
  sorry,
end
