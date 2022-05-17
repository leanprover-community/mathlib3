/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import tactic.interactive
import tactic.congrm
/-!  `congrm`: `congr` with pattern-matching -/
/-
  namespace tactic.interactive
  open tactic interactive
  setup_tactic_parser

  /--  Scans three `expr`s `e, lhs, rhs` in parallel.
  Currently, `equate_with_pattern` has three behaviours at each location:
  produce a goal, recurse, or skip.

  See the doc-string for `tactic.interactive.dap` for more details.
  -/
  meta def equate_with_pattern : expr → expr → expr → tactic unit
  | (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
    match e with
    | (expr.mvar _ _ _) := do
      el ← mk_app `eq [e0, e1],
      n ← get_unused_name "h",
      assert n el,
      rotate,
      get_local n >>= rewrite_target,
      equate_with_pattern f f0 f1
    | _ := do equate_with_pattern e e0 e1 *> equate_with_pattern f f0 f1
    end
  | _ _ _ := skip

  /--  `rev_goals` reverses the list of goals. -/
  meta def rev_goals : tactic unit :=
  do gs ← get_goals,
    set_goals gs.reverse

  /--  `congrm e` assumes that the goal is of the form `lhs = rhs`.  `congrm e` scans `e, lhs, rhs` in
  parallel.
  Assuming that the three expressions are successions of function applications, `congrm e`
  uses `e` as a pattern to decide what to do in corresponding places of `lhs` and `rhs`.

  If `e` has a meta-variable in a location, then the tactic produces a side-goal with
  the equality of the corresponding locations in `lhs, rhs`.

  Otherwise, `congrm` keeps scanning deeper into the expressions, until either the expressions finish
  or there is a mismatch between their shapes.

  *Note:* `congrm` does no check to make sure that the functions that it is matching are equal, or even
  defeq.  For instance,
  ```lean
  example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
  begin
    congrm (id _) + nat.succ _,
  end
  ```
  produces the three goals
  ```
  ⊢ 5 = 8
  ⊢ 7 = 12
  ⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
  ```
  In fact, not even the types need to match:
  ```
  example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
  begin
    let i₁ : ℤ → ℤ := sorry,
    let i₁' : ℤ → ℤ := sorry,
    let i₂ : ℤ → ℤ → ℤ := sorry,
    congrm i₂ (i₁ _) (i₁' _),
  end
  ```
  produces the same three goals as above
  ```
  ⊢ 5 = 8
  ⊢ 7 = 12
  ⊢ (nat.pred 8) * nat.succ 12 = (nat.pred 8) + nat.pred 12
  ```
  -/
  meta def congrm (arg : parse texpr) : tactic unit :=
  do ta ← to_expr arg tt ff,
    tgt ← target,
    (lhs, rhs) ← match_eq tgt,
    equate_with_pattern ta lhs rhs,
    try refl,
    rev_goals

  end tactic.interactive
-/

example {n : ℕ} : (nat.succ 5) * nat.succ 7 = (nat.succ 7) + nat.succ 1 :=
begin
  scan_with_res (id _) * nat.succ _,
  simp [*],refl,
  congrm (nat.succ _) * nat.succ _,
end

example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  congrm (id _) + nat.succ _,
end

example : (nat.pred 5) * nat.succ 7 = (nat.pred 8) + nat.pred 12 :=
begin
  let i₁ : ℤ → ℤ := sorry,
  let i₁' : ℤ → ℤ := sorry,
  let i₂ : ℤ → ℤ → ℤ := sorry,
  congrm i₂ (i₁ _) (i₁' _),
--sorry,
end
/-
#check unit

inductive arity : bool → bool
| tt := tt
| ff:= ff

#exit
| 0 :=  0 --punit.{0}
| (n+1) := 0 --unit

def arity : ℕ → Type*
| 0 := bool
| (n+1) := (λ (f : bool) (g : arity n), bool)
--/
#check unit

def j₁ : unit → unit
| _ := unit.star

def j₂ : unit → unit → unit
| _ _ := unit.star

def j₃ : unit → unit → unit → unit
| _ _ _ := unit.star

def j₄ : unit → unit → unit → unit → unit
| _ _ _ _ := unit.star

variables {X : Type*} [has_add X] [has_mul X] {a b c d l m n o p v w x y z : X} (f g h : X → X)
  (j : X → X → X → X → X)

example (lv : l = v) (mw : m = w) (nx : n = x) (oy : o = y) (pz : p = z) :
  j l (m + n) o p = j v (w + x) y z :=
begin
  dap j₄ _ (j₂ _ unit.star) _ _;
  try { assumption },
  sorry
end

example : j a (b + c) d = j x (y + z) w :=
begin
  dap j₂ (j₂ (j₂ _ _) unit.star) _;
  sorry;
  try { solve_by_elim },
end

/- fails because functions cannot be place-holders
example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  dap f (_ _) + (_ + _),
  { exact H' trivial },
  { exact H trivial },
  { exact H'' trivial },
end
-/

example {A : Type*} (j₂ : A → A → A) (j₁ : A → A) (w : A)
  (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  dap j₂ (j₁ (j₁ w)) (j₂ _ _),
  { exact H'' trivial },
  { exact H' trivial },
end


--/- desired syntax
example (H : true → a = b) (H' : true → f c = f d) : f a + f c = f b + f d :=
begin
  dap f _ + _,
  { exact H trivial },
  { exact H' trivial },
end
--/

-- desired syntax
example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → d = b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  dap f (f _) + (f _ + _),
  { exact H trivial },
  { exact H'' trivial },
  { exact H' trivial },
end

/- fails because of a typo
example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  dap f (f _) + (f _ + _),
  { exact H' trivial },
  rotate,
  { exact H trivial },
  { exact H'' trivial },
end
-/

-- desired syntax
example (H : true → a = b) (H' : true → f c = f d) : f (f a) * f c = f (f b) * f d :=
begin
  dap f (f _) * (_),
  exact H trivial,
  exact H' trivial,
end

#exit


--import tactic.move_add
--import data.polynomial.degree.lemmas
import tactic

namespace tactic.interactive
open tactic interactive
setup_tactic_parser

meta def mc_arg (prec : nat) : parser pexpr :=
parser.pexpr prec
#check expr.app
meta def decomp : expr → expr → expr → tactic unit
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do trace f, trace sformat!"e is {e}", trace target,
  if e.is_mvar then
    do el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap, -- instead of rotate, I would like to always work on the "original" goal
       ln ← get_local n,
       rewrite_target ln,
       decomp f f0 f1,
       rotate_right 1
  else decomp e e0 e1
| (expr.lam a b f e) (expr.lam a0 b0 f0 e0) (expr.lam a1 b1 f1 e1) := do trace f, trace sformat!"e is {e}", trace target,
  if e.is_mvar then
    do el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap, -- instead of rotate, I would like to always work on the "original" goal
       ln ← get_local n,
       rewrite_target ln,
       decomp f f0 f1,
       rotate_right 1
  else decomp e e0 e1
| (expr.pi a b f e) (expr.pi a0 b0 f0 e0) (expr.pi a1 b1 f1 e1) := do trace f, trace sformat!"e is {e}", trace target,
  if e.is_mvar then
    do el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap, -- instead of rotate, I would like to always work on the "original" goal
       ln ← get_local n,
       rewrite_target ln,
       decomp f f0 f1,
       rotate_right 1
  else decomp e e0 e1
| (expr.elet a b f e) (expr.elet a0 b0 f0 e0) (expr.elet a1 b1 f1 e1) := do trace "elet",trace f, trace sformat!"e is {e}", trace target,
  if e.is_mvar then
    do el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap, -- instead of rotate, I would like to always work on the "original" goal
       ln ← get_local n,
       rewrite_target ln,
       decomp f f0 f1,
       rotate_right 1
  else decomp e e0 e1
| (expr.mvar n1 n2 e) e0 e1 := do trace "mvar",
       el ← mk_app `eq [e0, e1],
       n ← get_unused_name "h",
       assert n el,
       swap, -- instead of rotate, I would like to always work on the "original" goal
       ln ← get_local n,
       rewrite_target ln,
       rotate_right 1
| _ _ _ := trace "nothing"

meta def dap (arg : parse (mc_arg tac_rbp)) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  decomp ta lhs rhs,
  any_goals (try refl)

end tactic.interactive

variables {X : Type*} [has_add X] {a b c d : X} (f g h : X → X)


-- desired syntax
example (H : true → a = b) (H' : true → f c = f d) : f a + f c = f b + f d :=
begin
  dap f _ + _,
  { exact H trivial },
  { exact H' trivial },
end

-- desired syntax
example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → d = b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  dap f (f _) + (f _ + _),
  { exact H'' trivial },
  { exact H' trivial },
  { exact H trivial },
  rotate,
end


-- desired syntax
example (H : true → a = b) (H' : true → f c = f d) : f (f a) * f c = f (f b) * f d :=
begin
  dap f (_) * (_),
  exact H' trivial,
  exact H trivial,
  rw h,
  sorry,
  exact b,
  exact c,
end

#exit










namespace tactic.interactive
open tactic interactive
setup_tactic_parser

/-
meta def arg_texpr_1 : parser (list (bool × pexpr)) :=
list.ret <$> (move_add_arg tac_rbp) <|> return []

meta def arg_texpr : parser (list (bool × pexpr)) :=
list_of (move_add_arg 0) <|> list.ret <$> (move_add_arg tac_rbp) <|> return []

meta def mca : parser pexpr :=
parser.pexpr tac_rbp

meta def pca : parser (pexpr) :=
list.ret <$> (mca tac_rbp) <|> return []
-/

meta def mc_arg (prec : nat) : parser pexpr :=
parser.pexpr prec

meta def mc_m : expr → expr → expr → tactic unit
--| `(has_add.add %%a %%b) `(has_add.add %%c %%d) `(has_add.add %%e %%f) := do trace "add",
--  --mc_m a c e,
--  mc_m b d f
| (expr.mvar n1 n2 e) f g := do trace "mvar", trace f, trace g,n ← get_unused_name,
                              fg ← mk_app `eq [f, g],
                              assert n fg, target >>= trace
--                              skip
--| (expr.lam n b e f) (expr.lam n' b' e' f') (expr.lam n'' b'' e'' f'') :=
--  do trace "lam"
--
| (expr.app f a) (expr.app g b) (expr.app h c) := do
  unify f g,
  mc_m a b c
| _ _ _ := fail "sorry, no match"

--/-
meta def ca (arg : parse (mc_arg tac_rbp)) : tactic unit :=
do tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  gl ← to_expr arg tt ff,
  trace sformat!"lhs {lhs},\nrhs {rhs},\narg,\n{gl}",
  mc_m gl lhs rhs
--/

/-
  meta def ex_match1 : expr → expr → tactic expr
  | `(has_add.add %%a %%b) `(has_add.add %%c %%d) :=
    do el ← ex_match1 a c,
      er ← ex_match1 b d,
      mk_app `has_add.add [el, er]
  | (expr.app f a) (expr.app g b) :=
    do is_def_eq f g,
      ear ← ex_match1 a b,
      mk_app `f [ear]
  | (expr.mvar n1 n2 e) ex :=
    --do n ← get_unused_name,
    mk_app `eq [e, ex] >>= return
  | _ _ := fail "sorry, not supported"
  #check expr.mvar
  meta def ex_match : expr → expr → tactic (list expr)
  | `(has_add.add %%a %%b) `(has_add.add %%c %%d) :=
    do bl ← succeeds $ unify a c,
       br ← succeeds $ unify b d,
       match bl, br with
       | tt, tt := do el ← ex_match a c,
                      er ← ex_match b d,
                      return (el ++ er)
       | tt, ff := do el ← ex_match a c,
                      er ← mk_app `eq [gl, gl],

  --    mk_app `has_add.add [el, er]
  | (expr.app f a) (expr.app g b) :=
    do is_def_eq f g,
      ear ← ex_match a b,
      mk_app `f [ear]
  | (expr.mvar n1 n2 e) ex :=
    --do n ← get_unused_name,
    mk_app `eq [e, ex] >>= return
  | _ _ := fail "sorry, not supported"
  -/
  /-
  meta def ca (arg : parse (mc_arg tac_rbp)) : tactic unit :=
  do tgt ← target,
    gl ← to_expr arg tt ff,trace gl,
    el ← mk_app `eq [gl, gl],
    exm ← ex_match el tgt,
    exm.mmap assert,


  meta def mca (arg : parse (mc_arg tac_rbp)) : tactic unit :=
  --meta def mca1 (arg : parse move_pexpr_list_or_texpr) : tactic unit :=
  do tgt ← target,
    (lhs, rhs) ← match_eq tgt,
    gl ← to_expr arg tt ff,trace gl,
    unify gl lhs,
    instantiate_mvars gl,trace gl,
    el ← mk_app `eq [gl, lhs],
    nl ← get_unused_name,
    assert nl el,
    congr,
    target >>= trace,
    er ← mk_app `eq [gl, rhs],
    nr ← get_unused_name,
    assert nr er,
    congr
    --`[congr' 1]
    --  e ← mk_app `eq [gl, gl],
  --  e1 ← mk_app `eq [tgt, e],
  --  congr
  --  `[congr' 2]

  /-
    meta def mca (arg : parse move_pexpr_list_or_texpr) : tactic unit :=
    do t ← target,
    --match t.is_eq with
    --| none := skip
    --| some (tl,tr) :=
      match arg with
      | [] := skip
      | [(bo,ar)] := do
    --pex ← parser.pexpr tac_rbp ff arg,
        gl ← to_expr ar tt ff,
        `(eq gl gl) ← t,
        e ← mk_app `eq [gl, gl],

        trace e,
        trace t,
        is_def_eq e t <|>
        unify e t
      | _ := skip
      end
    --end
  -/
-/

meta def ca1 (arg : parse (mc_arg tac_rbp)) : tactic unit :=
do tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  gl ← to_expr arg,
  el ← mk_app `eq [lhs, gl],
  n ← get_unused_name "h",
  assert n el,
  target >>= trace,
  `[congr' 1],
  er ← mk_app `eq [rhs, gl],
  m ← get_unused_name "h",
  assert m er,
  target >>= trace,
  `[congr' 1]
--  trace "unify left",
--  unify lhs gl,
--  trace "unify right",
--  unify rhs gl
  --,
  --trace sformat!"lhs {lhs},\nrhs {rhs},\narg,\n{gl}",
  --mc_m gl lhs rhs
#check list.zip_with3
meta def decomp : expr → expr → expr → tactic unit
--| `(@has_add.add %%a %%b %%c %%d) `(@has_add.add %%a0 %%b0 %%c0 %%d0) `(@has_add.add %%a1 %%b1 %%c1 %%d1) := do trace "\nadd",
--  trace a, trace b, decomp c c0 c1, decomp d d0 d1
--| `(has_add.add %%a %%b) `(has_add.add %%a0 %%b0) `(has_add.add %%a1 %%b1) :=
--  do trace "\nadd",
--  trace a, trace b--, decomp a a0 a1 --, decomp b b0 b1
--| (expr.app ((expr.app f e')) e) (expr.app ((expr.app f0 e0')) e0) (expr.app ((expr.app f1 e1')) e1) :=
--do trace "\nappapp",trace $ whnf f,trace f,trace f0,trace f1, trace e,
--  wf  ← whnf f ,
--  wf0 ← whnf f0,
--  wf1 ← whnf f1,
--  trace wf, is_def_eq wf wf0, decomp e e0 e1, decomp f f0 f1
| (expr.app f e) (expr.app f0 e0) (expr.app f1 e1) := do
  --trace "\napp",trace $ whnf f,trace f,trace f0,trace f1,
  match e.is_mvar with
  | ff := decomp e e0 e1
  | tt := do el ← mk_app `eq [e0, e1],trace el,
             n ← get_unused_name "h",
             assert n el,
             decomp f f0 f1
             end
/-
  --wf ← whnf f, wf0 ← whnf f0, wf1 ← whnf f1,
  infer_type e >>= trace,
  trace e, trace $ expr.is_mvar e,
  --trace sformat!"weak heads:\n  {wf},\n  {wf0},\n  {wf1}",
  let fargs  := f.get_app_args,
  let fargs0 := f0.get_app_args,
  let fargs1 := f1.get_app_args,
  trace sformat!"fargs, {fargs}",
  let new := list.zip_with3 decomp fargs fargs0 fargs1,
--  is_def_eq wf wf0,

  decomp f f0 f1,
  decomp e e0 e1
| (expr.mvar a b e) (expr.mvar a0 b0 e0) (expr.mvar a1 b1 e1) := do trace "\nmvar",
  trace a, trace b, trace e,
  decomp e e0 e1
| (expr.lam a b f e) (expr.lam a0 b0 f0 e0) (expr.lam a1 b1 f1 e1) := do trace "\nlam",
  trace a, trace f, trace e, decomp f f0 f1, decomp e e0 e1
| (expr.pi a b f e) (expr.pi a0 b0 f0 e0) (expr.pi a1 b1 f1 e1) := do trace "\npi", trace a, trace f, trace e,
  decomp e e0 e1, decomp f f0 f1
| (expr.elet a b f e) (expr.elet a0 b0 f0 e0) (expr.elet a1 b1 f1 e1) := do
  trace "elet", trace a, trace b, trace f, trace e,
  decomp b b0 b1, decomp e e0 e1,decomp f f0 f1
-/
| _ _ _ := trace "nothing"

meta def dap (arg : parse (mc_arg tac_rbp)) : tactic unit :=
do ta ← to_expr arg tt ff,
  tgt ← target,
  (lhs, rhs) ← match_eq tgt,
  decomp ta lhs rhs
--  trace "now the target",
--  trace "lhs",
--  decomp lhs,
--  trace "rhs",
--  decomp rhs
--  do ar ← to_expr `(%%f _ + _),

end tactic.interactive

variables {X : Type*} [has_add X] [has_mul X] {a b c d : X} (f g : X → X)

-- desired syntax
example (H : true → a = b) (H' : true → f c = f d) : f (f a) * f c = f (f b) * f d :=
begin
  dap f (_) * (_),
  exact H trivial,
  exact H' trivial,
  rw h,
  sorry,
  exact b,
  exact c,
end

#exit
  ca f _ + _,
  ca f _ + _,
--  congr,
  { exact (H' trivial) },
  rw _x,
  ca f a + _; try {refl},
  rotate,
  exact a,
  exact b,
  congr,
  { exact (H trivial) },
  sorry
end

example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  mca f (f _) + (f _ + _),
  { exact (H trivial).symm },
  { exact (H'' trivial).symm },
  { exact (H' trivial).symm },
end


example : f a = f b :=
begin
  mca1 f _,
  congr' 1,
  { congr,
    exact H trivial },
  { exact H' trivial }
end

example (H : true → a = b) (H' : true → f c = f d) : f a + f c = f b + f d :=
begin
  mca1 f _ + f _,
  congr' 1,
  { congr,
    exact H trivial },
  { exact H' trivial }
end

example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) + (f d + (c + f a)) = f (f b) + (f b + (c + f d)) :=
begin
  congr' 1,
  { congr,
    exact H trivial },
  { congr' 1,
    { exact H'' trivial },
    { exact H' trivial } }
end
