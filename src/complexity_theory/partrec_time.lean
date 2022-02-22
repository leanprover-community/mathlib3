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


/-- A code running on a list returns a value, then there is a time at which it returns -/
lemma time_dom_of_eval_dom (c : code) (l : list ℕ) (h : ((c.eval l).dom)) : (time c l).dom  :=
begin
  induction c with f fs iHf iHfs f g iHf iHg f g iHf iHg generalizing l,
  { rw time, unfold pure, },
  { rw time, unfold pure, },
  { rw time, unfold pure, },
  { cases h,
    cases h_h,
    fsplit,
    { fsplit,
      { solve_by_elim },
      solve_by_elim },
    assumption, },
  { cases h,
    fsplit,
    { fsplit,
      { solve_by_elim },
      fsplit,
      { assumption },
      solve_by_elim },
    dsimp at *,
    exact dec_trivial, },
  { cases l,
    { fsplit,
      { solve_by_elim },
      dsimp at *,
      exact dec_trivial, },
    { cases l_hd,
      { fsplit, work_on_goal 0 { solve_by_elim }, dsimp at *, exact dec_trivial, },
      { fsplit, work_on_goal 0 { solve_by_elim }, dsimp at *, exact dec_trivial, }, }, },
  { sorry,
    -- TODO note that time (fix f) is the same computation eval (fix f) with extra data tacked on.
    -- this extra data tacked on to fix doesn't affect the values of type α
    -- Prove in general that doing this doesn't affect whether or not you end up in the domain
  },
end

-- lemma eval_dom_of_time_dom_case (f g : code) (l : list ℕ) (h : ((time (code.case f g) l).dom)) :
--   ((code.case f g).eval l).dom :=
-- begin

-- end

/-- A code running on a list returns a value, then there is a time at which it returns -/
lemma eval_dom_of_time_dom (c : code) (l : list ℕ) (h : ((time c l).dom)) : (c.eval l).dom  :=
begin
  induction c with f fs iHf iHfs f g iHf iHg f g iHf iHg generalizing l,
  { -- tidy,
    sorry, },
  { -- tidy,
    sorry, },
  { -- tidy,
    sorry, },
  { -- tidy,
    sorry, },
  { -- tidy,
    sorry, },
  { cases h with h_w h_h, dsimp at *,
    cases l.head,
    simp at *,
    apply iHf,
    assumption,
    simp at *,
    apply iHg (n :: l.tail),
    exact h_w,
   },
  { sorry, },
end

/--
Holds for codes representing total functions, where `bound` is a function upper bounding the
runtime of the code over all input lists of length `l`.
-/
def time_bound (c : turing.to_partrec.code) (bound : ℕ → ℕ) : Prop :=
∀ (l : list ℕ) (len : ℕ), ∃ t ∈ time c l, l.length ≤ len -> t ≤ bound (len)

lemma total_of_time_bound (c : turing.to_partrec.code) (bound : ℕ → ℕ) (H : time_bound c bound)
  (l : list ℕ) : (c.eval l).dom :=
begin
  apply eval_dom_of_time_dom,
  unfold time_bound at H,
  replace H := H l 0,
  rw part.dom_iff_mem,
  rcases H with ⟨t, H, ht⟩,
  exact Exists.intro t H,
end


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
  intro hl,
  exact add_le_add (ht hl) (hts hl),
end

lemma output_length_bound {c : code} {l : list ℕ} (hdom : (c.eval l).dom) :
  ((c.eval l).get hdom).length ≤ l.length + ((time c l).get (time_dom_of_eval_dom c l hdom)) :=
begin
  induction c with f fs iHf iHfs f g iHf iHg f g iHf iHg,
  { tidy, },
  { tidy, },
  { tidy, rw add_assoc, exact le_self_add, },
  { rw part.dom_iff_mem at hdom,
    rcases hdom with ⟨l', hl'⟩,
    rw part.get_eq_of_mem hl',
    rw code.eval at hl',
    simp at hl',
    rcases hl' with ⟨foo1, foo2, foo3, foo4, foo5⟩,
    rw foo5,
    simp,
    have foo6 : ∃ l'', l'' ∈ fs.eval l,
      use foo3, assumption,
    rw <-part.dom_iff_mem at foo6,
    replace iHfs := iHfs foo6,
    rw part.get_eq_of_mem foo4 at iHfs,
    apply trans (nat.succ_le_succ iHfs),
    rw nat.succ_eq_add_one,
    rw add_assoc,
    simp,
    unfold time,
    simp,
    simp_rw part.add_get_eq,
    rw part.get_some,
    simp, },
  { have hgld : (g.eval l).dom,
    { tidy, },
    have gl := (g.eval l).get hgld,
    replace iHg := iHg hgld,
    rw <-gl at iHg,
    have hfld : (f.eval gl).dom,
    { tidy, },
    have fl := (f.eval gl).get hfld,
    replace iHg := iHg hgld,

    tidy,
    unfold time, sorry, },
  sorry,
  sorry,
end

/-- Time bound lemma for composition.
Note that we compose the f bound with the g bound plus the identity. This is because `g` may be a
function with a very short time bound that does not read its whole input. `bg + id`, though, is
guaranteed to upper bound the length of the input to f. -/
lemma time_bound_comp (f g : code) {bf bg : ℕ → ℕ} {mbf : monotone bf}
  (hbf : time_bound f bf) (hbg : time_bound g bg) :
  time_bound (code.comp f g) (bg + (bf ∘ (bg + id)) + 1) :=
begin
  rw time_bound at *,
  intros l len,
  rw time,
  -- use bf + bf ∘ (bg + id) + 1,
  rcases hbg l len with ⟨tg, Hg, hgt⟩,
  have g_total := total_of_time_bound g bg hbg l,
  -- have g_out := (g.eval l).get g_total,
  rcases hbf ((g.eval l).get g_total) (((g.eval l).get g_total).length) with ⟨tf, Hf, hft⟩,
  use tg + tf + 1,
  split,
  simp,
  apply part.add_mem_add,
  apply part.add_mem_add,
  assumption,
  simp,
  use ((g.eval l).get g_total),
  split,
  exact part.get_mem g_total,
  exact Hf,
  exact part.mem_some 1,
  simp,
  intro hl,
  apply add_le_add,
  apply hgt,
  assumption,
  simp at hft,
  apply trans hft,
  apply mbf,
  apply trans (output_length_bound g_total),
  rw add_comm,
  apply add_le_add,
  apply trans _ (hgt hl),
  apply le_of_eq,
  exact part.get_eq_of_mem Hg (time_dom_of_eval_dom g l g_total),
  assumption,
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
  use polynomial.C 1,
  tidy,
end

lemma poly_time_tail : poly_time code.tail :=
begin
  rw poly_time,
  use polynomial.C 1,
  tidy,
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

lemma polynomial.eval_comp' (p q : polynomial ℕ) :
  (λ x, polynomial.eval x (p.comp q) : ℕ -> ℕ)
  = ((λ (x : ℕ), polynomial.eval x p) : ℕ -> ℕ) ∘ ((λ (x : ℕ), polynomial.eval x q) : ℕ -> ℕ) :=
begin
  simp,
end

lemma monotone_eval_polynomial_nat (p : polynomial ℕ) : monotone (λ (x : ℕ), polynomial.eval x p) :=
begin
  apply polynomial.induction_on' p,
  intros p q mp mq,
  simp,
  exact monotone.add mp mq,
  intros n a,
  simp,
  refine monotone.mul _ _ _ _,
  { intros a_1 b h, refl },
  { intros a_1 b h, dsimp at *, apply pow_le_pow_of_le_left, exact zero_le a_1, assumption, },
  { intro n, exact zero_le a, },
  { intro n_1, exact zero_le (n_1 ^ n), },
end

lemma poly_time_comp (f g : code) (hf : poly_time f) (hg : poly_time g) :
  poly_time (code.comp f g) :=
begin
  rw poly_time at *,
  rcases hf with ⟨fp, fpb⟩,
  rcases hg with ⟨gp, gpb⟩,
  use gp + (fp.comp (gp + polynomial.X)) + 1,
  simp only [polynomial.eval_add, polynomial.eval_comp', polynomial.eval_X, polynomial.eval_one],
  -- have foo : λ (x : ℕ), polynomial.eval x (gp + fp.comp (gp + polynomial.X) + 1) =
  --           ((λ (x : ℕ), polynomial.eval x gp) +
  --        (λ (x : ℕ), polynomial.eval x fp) ∘ ((λ (x : ℕ), polynomial.eval x gp) + id) +
  --      1),
  -- simp
  have foo := @time_bound_comp f g (λ x, fp.eval x) (λ x, gp.eval x) _ fpb gpb,
  suffices : ((λ (x : ℕ), polynomial.eval x gp) + (λ (x : ℕ), polynomial.eval x fp) ∘ ((λ (x : ℕ), polynomial.eval x gp) + id) + 1) = (λ (x : ℕ), polynomial.eval x gp + polynomial.eval x (fp.comp (gp + polynomial.X)) + 1),
  { simp_rw <-this, exact foo, },
  clear foo,
  ext,
  simp,
  apply monotone_eval_polynomial_nat,

end
