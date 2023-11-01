/-
Copyright (c) 2021 Leo Okawa Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Okawa Ericson
-/
import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

set_option pp.beta true
set_option pp.coercions true
set_option pp.generalized_field_notation false
set_option trace.check true
set_option pp.notation true
/-!
This is a compiler and proof that is translated from the second part of Concrete Semantics. http://concrete-semantics.org/

The proof consists of just the forward part of the proof presented in Concrete
Semantics, i.e. it's a partial correctness proof. It proves that the compiler is
correct for all terminating programs.

-/
/- # LoVe Library
 Copied from https://github.com/blanchette/logical_verification_2020/
 Copyright belongs to the authors of that book.
 -/
namespace LoVe
namespace rtc

inductive star {α : Sort*} (r : α → α → Prop) (a : α) : α → Prop
| refl {}    : star a
| tail {b c} : star b → r b c → star c

attribute [refl] star.refl

namespace star

variables {α : Sort*} {r : α → α → Prop} {a b c d : α}

@[trans] lemma trans (hab : star r a b) (hbc : star r b c) :
  star r a c :=
begin
  induction' hbc,
  case refl {
    assumption },
  case tail : c d hbc hcd hac {
    exact (tail (hac hab)) hcd }
end

lemma single (hab : r a b) :
  star r a b :=
refl.tail hab
end star
end rtc

def state :=
string → int

def state.update (name : string) (val : int) (s : state) : state :=
λname', if name' = name then val else s name'

notation s `{` name ` ↦ ` val `}` := state.update name val s

instance : has_emptyc state :=
{ emptyc := λ_, 0 }

export rtc
end LoVe

open LoVe

namespace bool
lemma or_intro (b : bool) : b = tt ∨ b = ff :=
begin
  cases' em (b = ff),
  {
    apply or.intro_right, exact h,
  },
  { simp at h,
    apply or.intro_left,
    exact h,
  },
end
end bool

lemma le_iff_not_lt {a b : int} :  a ≤ b -> ¬ b < a :=
begin
  intro h,
  simp,
  assumption,
end

lemma not_le_iff_lt {a b : int} :  ¬ a ≤ b -> b < a :=
begin
  intro h,
  simp * at *,
end

lemma cond_add (P) (a b : ℤ) : (cond P a (a + b) = a + (cond P 0 b)) :=
begin
  cases' P,
  { simp, },
  { simp, },
end

namespace list

lemma nth_some_append : ∀ {α : Type} {l : list α} {l' : list α} x i,
                           list.nth l i = some x → list.nth (l ++ l') i = some x :=
begin
  intros α l l' x i,
  induction' l,
  { intro h,
    exfalso,
    simp at h,
    assumption,
  },
  { intro h,
    cases' i,
    { simp at h,
      simp,
      assumption,
    },
    { simp,
      simp at h,
      exact @ih l' x i h,
    }
  }
end

lemma nth_some_append_left : ∀ {α : Type} {l : list α} {l' : list α} x i,
                           list.nth l i = some x → list.nth (l' ++ l) (i + list.length l') = some x :=
begin
  intros α l l' x i,
  induction' l',
  { intro h,
    simp,
    assumption,
  },
  { intro h,
    cases' i,
    { simp,
      simp at h,
      have ih' := @ih l x 0,
      simp at ih',
      exact ih' h,
    },
    { simp [list.nth],
      rw nat.succ_add,
      simp [list.nth],
      have ih' := @ih l x (i + 1),
      have haddeq : (i + (list.length l' + 1)) = (i + 1 + list.length l') :=
        by linarith,
      rw haddeq,
      exact ih' h,
    },
  },
end

lemma zero_le_length_add_one {α : Type}  {xs : list α} : 0 ≤ ↑(length xs) + (1 : ℤ) :=
begin
  induction' xs,
  { simp, linarith, },
  { simp, linarith, }
end

end list

section sem
/-
This big-step semantics is copied from The Hitchhiker's Guide.
Copyright belongs to the original authors.
-/
inductive aexp : Type
| N    : int → aexp
| V    : string → aexp
| Plus : aexp → aexp → aexp


@[simp] def aval : aexp → LoVe.state → int
| (aexp.N i) _ := i
| (aexp.V x) s := s x
| (aexp.Plus a b) s := (aval a s) + (aval b s)


inductive bexp : Type
| Bc : bool → bexp
| Not : bexp → bexp
| And : bexp → bexp → bexp
| Less : aexp → aexp → bexp


@[simp] def bval : bexp → LoVe.state → bool
| (bexp.Bc b) _ := b
| (bexp.Not x) s := not (bval x s)
| (bexp.And a b) s := (bval a s) ∧ (bval b s)
| (bexp.Less a b) s := (aval a s) < (aval b s)

/-!
This big-step semantics is copied from The Hitchhiker's Guide to Logical Verification.
-/
inductive stmt : Type
| skip   : stmt
| assign : string → aexp → stmt
| seq    : stmt → stmt → stmt
| ite    : bexp → stmt → stmt → stmt
| while  : bexp → stmt → stmt


infixr ` ;; ` : 90 := stmt.seq

inductive big_step : stmt × LoVe.state → LoVe.state → Prop
| skip {s} :
  big_step (stmt.skip, s) s
| assign {x a s} :
  big_step (stmt.assign x a, s) (s{x ↦ aval a s})
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
| ite_true {b : bexp} {S T s t} (hcond : bval b s)
    (hbody : big_step (S, s) t) :
  big_step (stmt.ite b S T, s) t
| ite_false {b : bexp} {S T s t} (hcond : ¬ bval b s)
    (hbody : big_step (T, s) t) :
  big_step (stmt.ite b S T, s) t
| while_true {b : bexp} {S s t u} (hcond : bval b s)
    (hbody : big_step (S, s) t)
    (hrest : big_step (stmt.while b S, t) u) :
  big_step (stmt.while b S, s) u
| while_false {b : bexp} {S s} (hcond : ¬ bval b s) :
  big_step (stmt.while b S, s) s

infix ` ⟶ ` : 110 := big_step

inductive instr : Type
| loadi   : int    → instr
| load    : string → instr
| add     :           instr
| store   : string → instr
| jmp     : int    → instr
| jmpless : int    → instr
| jmpge   : int    → instr


notation `config` := int × state × list int
notation `program` := list instr


inductive iexec :  instr → config → config → Prop
| loadi {i s stk} (n : int):
  iexec (instr.loadi n) (i,s, stk) (i + 1, s, n :: stk)
| load  {i s stk} (x : string) :
  iexec (instr.load x) (i, s, stk) (i + 1, s, s x :: stk)
| add   {i s stk a b} :
  iexec instr.add (i, s, a :: b :: stk) (i + 1, s, (a + b) :: stk)
| store {i s stk a} (x : string) :
  iexec (instr.store x) (i, s, a :: stk) (i + 1, s{x ↦ a}, stk)
| jmp {i s stk} (n : int) :
  iexec (instr.jmp n) (i,s, stk) (i + 1 + n, s, stk)
| jmpless_true {i s stk a b} (n : int) (hcond : b < a):
  iexec (instr.jmpless n) (i,s , a :: b :: stk) (i + 1 + n, s, stk)
| jmpless_false {i s stk a b} (n : int) (hcond : ¬ b < a):
  iexec (instr.jmpless n) (i, s, a :: b :: stk) (i + 1, s, stk)
| jmpge_true {i s stk a b} (n : int) (hcond : b ≥ a):
  iexec (instr.jmpge n) (i,s , a :: b :: stk) (i + 1 + n, s, stk)
| jmpge_false {i s stk a b} (n : int) (hcond : ¬ b ≥ a):
  iexec (instr.jmpge n) (i, s, a :: b :: stk) (i + 1, s, stk)


inductive exec1 : program → config → config → Prop
| exec1 {p s stk c' x} {n : ℕ}
        (hnth : list.nth p n = some x )
        (hiexec : iexec x
                        (n, s, stk)
                        c'):
  exec1 p (n, s, stk) c'

reserve infixl `⊢`:70

reserve infixr ` ⇒* ` : 40
reserve infixr ` ⟹ ` : 40

notation p ` ⊢ ` c ` ⇒* ` :100 c'  := (star (exec1 p) c c')
notation p ` ⊢ ` c ` ⟹ ` :100 c'  := exec1 p c c'

lemma exec1_append {p p' : program } {c c' : config}: (p ⊢ c ⟹ c') → ((p ++ p') ⊢ c ⟹ c') :=
begin
  intro h,
  cases' h,
  apply exec1.exec1 (@list.nth_some_append instr p p' x n hnth),
  {
    assumption,
  }
end

lemma relocate_instruction {x i i' s  stk} {s' : LoVe.state} {stk' : list int} (n) :
      iexec x (i + n, s, stk) (i' + n, s', stk') ↔ iexec x (i, s, stk) (i', s', stk')
:=
begin
  split,
  { intro h,
    cases' h,
    any_goals {
      have hi : i + 1 = i' := by linarith,
      rw ← hi,
    },
    any_goals {
      have hi : i + 1 + n_1 = i' :=
            by linarith,
      rw ← hi,
    },
    {
      apply iexec.loadi,
    },
    {
      apply iexec.load,
    },
    {
      apply iexec.add,
    },
    {
      apply iexec.store,
    },
    {
      apply iexec.jmp,
    },
    {
      apply @iexec.jmpless_true i s stk a b n_1 hcond,
    },
    {
      apply @iexec.jmpless_false i s stk a b n_1 hcond,
    },
    {
      apply @iexec.jmpge_true i s stk a b n_1 hcond,
    },
    {
      apply @iexec.jmpge_false i s stk a b n_1 hcond,
    }
  },
  { intro h,
    have tmp_add : i + 1 + n = (i + n) + 1 := by linarith,
    cases' h,
    {
      rw tmp_add,
      apply iexec.loadi,
    },
    {
      rw tmp_add,
      apply iexec.load,
    },
    {
      rw tmp_add,
      apply iexec.add,
    },
    {
      rw tmp_add,
      apply iexec.store,
    },
    {
      have tmp_add : i + 1 + n_1 + n = ((i + n) + 1) + n_1 := by linarith,
      rw tmp_add,
      apply iexec.jmp,
    },
    {
      have tmp_add : i + 1 + n_1 + n = ((i + n) + 1) + n_1 := by linarith,
      rw tmp_add,
      apply iexec.jmpless_true n_1 hcond,
    },
    {
      rw tmp_add,
      apply iexec.jmpless_false n_1 hcond,
    },
    {
      have tmp_add : i + 1 + n_1 + n = ((i + n) + 1) + n_1 := by linarith,
      rw tmp_add,
      apply iexec.jmpge_true n_1 hcond,
    },
    {
      rw tmp_add,
      apply iexec.jmpge_false n_1 hcond,
    },

  },
end

lemma exec1_append_left {p p' : program} { s s' : LoVe.state }
                        {stk stk' : list int} {i i' : int} :
      (p ⊢ (i, s, stk) ⟹ (i', s', stk' )) →
        (p' ++ p ) ⊢ (i + list.length p', s, stk) ⟹
                     (i' + list.length p', s', stk') :=
begin
  intro h,
  cases' h,
  apply exec1.exec1 (@list.nth_some_append_left instr p p' x n hnth),
  apply (iff.elim_right (@relocate_instruction x n i' s stk s' stk' (list.length p'))),
  assumption,
end

lemma exec_append_right {p c c'} (p') :
      (p ⊢  c ⇒* c') → (p ++ p' ) ⊢ c ⇒* c' :=
begin
  intro h,
  cases' c with i s,
  cases' s with s stk,
  cases' c' with i' s',
  cases' s' with s' stk',
  induction' h,
  { apply star.refl, },
  { have h_2 : exec1 (p ++ p') b (i', s', stk') := exec1_append h_1,
    cases' h,
    { exact star.tail (star.refl) (h_2), },
    { have h_3' : exec1 (p ++ p') b b_1 :=  exec1_append h_3,
      clear h_3,
      rename h_3' h_3,
      cases' b_1 with bi bs,
      cases' bs with bs bstk,
      have ih' :_ := @ih p' bi bs bstk,
      have tmp : (bi, bs, bstk) = (bi, bs, bstk) := by refl,
      have ih'' :_ := ih' tmp,
      have tmp' :_ := star.tail ih'' h_2,
      assumption,
    },
  },
end

lemma exec_append_left {p s s' stk stk'} (p') {i i' : int} :
      (p ⊢ (i, s, stk) ⇒* (i', s', stk' )) →
        (p' ++ p ) ⊢ (i +  p'.length, s, stk) ⇒*
                     (i' + p'.length, s', stk') :=
begin
  intro h,
  induction' h,
  { apply star.refl, },
  {
    cases' b with bi bs,
    cases' bs with bs bstk,
    have tmp: (bi, bs, bstk) = (bi, bs, bstk) := by refl,
    have ih' := @ih bs bstk p' bi,
    clear ih,
    have tmp' := ih' tmp,
    apply star.tail,
    { exact tmp', },
    { exact exec1_append_left h_1
    }
  },
end

def aexp.repr : aexp → string
| (aexp.N n) := "N " ++ (repr n)
| (aexp.V x) := "V " ++ (repr x)
| (aexp.Plus a b) := (aexp.repr a) ++ (aexp.repr b)
instance : has_repr aexp := ⟨aexp.repr⟩

def bexp.repr : bexp → string
| (bexp.Bc b) := "Bc " ++ repr b
| (bexp.Not b) := "Not" ++ bexp.repr b
| (bexp.And a b) := (bexp.repr a ) ++ " ∧ " ++ (bexp.repr b )
| (bexp.Less a b) := (repr a ) ++ " < " ++ (repr b )
instance : has_repr bexp := ⟨bexp.repr⟩

def instr.repr : instr → string
| (instr.loadi n) := "loadi " ++ repr n
| (instr.load x) := "load " ++ repr x
| (instr.add) := "add"
| (instr.store x) := "store " ++ repr x
| (instr.jmp n) := "jmp " ++ repr n
| (instr.jmpless n) := "jmpless " ++ repr n
| (instr.jmpge n) := "jmpge " ++ repr n

instance : has_repr instr := ⟨instr.repr⟩


end sem



namespace acomp

@[simp] def acomp : aexp → program
| (aexp.N i) := [instr.loadi i]
| (aexp.V x) := [instr.load x]
| (aexp.Plus a b) := (acomp a) ++ (acomp b) ++ [instr.add]



lemma correct {a s stk}  :
              (acomp a) ⊢ (0, s, stk) ⇒*
                         ↑(list.length (acomp a),
                           s,
                           (aval a s) :: stk) :=
begin
  induction' a,
  case aexp.N : n {
    show (acomp (aexp.N n)) ⊢
          (0, s, stk) ⇒*
          (↑(acomp (aexp.N n)).length,
           s,
           aval (aexp.N n) s :: stk),
    -- star.single takes an element of a relation ⟹ and creates the
    -- corresponding element of ⇒*
    exact star.single (exec1.exec1 (begin simp end) (iexec.loadi _)),
  },
  case aexp.V : x {
    show (acomp (aexp.V x)) ⊢
          (0, s, stk) ⇒*
          (↑(acomp (aexp.V x)).length,
           s,
           aval (aexp.V x) s :: stk),
    exact star.single (exec1.exec1 (begin simp end) (iexec.load _)),
  },
  case aexp.Plus {
    show (acomp (aexp.Plus a a_1)) ⊢
              (0, s, stk) ⇒*
              (↑(list.length (acomp (aexp.Plus a a_1))),
               s,
               aval (aexp.Plus a a_1) s :: stk),
    simp,
    -- Run the program through the first arithmetic sub-expression
    -- Apppend so that we get the full program instead of just one
    -- sub-expression
    have h_run_a : (acomp a ++ (acomp a_1 ++ [instr.add])) ⊢
                        (0, s, stk) ⇒*
                        (↑(list.length (acomp a)),
                         s,
                         aval a s :: stk)
      := exec_append_right (acomp a_1 ++ [instr.add]) (@ih_a s stk),
    clear ih_a,
    -- Run the program through the second arithmetic
    -- sub-expression
    have h_run_a_1 : (acomp a_1) ⊢
                          (0, s, aval a s :: stk) ⇒*
                          (↑(list.length (acomp a_1)),
                           s,
                           aval a_1 s :: aval a s :: stk)
      := @ih_a_1 s ((aval a s) :: stk),
    clear ih_a_1,
    -- apppend so that we get the full program instead of just one
    -- sub-expression
    have h_run_a_1' : (acomp a ++ acomp a_1 ++ [instr.add]) ⊢
                           (0 + ↑(list.length (acomp a)),
                            s,
                            aval a s :: stk) ⇒*
                           (↑(list.length (acomp a_1)) +
                             ↑(list.length (acomp a)),
                            s,
                            aval a_1 s :: aval a s :: stk)
      := exec_append_right [instr.add]
                           (exec_append_left (acomp a)  h_run_a_1),
    simp at h_run_a_1',

    -- Use transitivity to construct an evaluation of the first
    -- two sub-expressions
    have h_run_a_and_a_1 := star.trans h_run_a h_run_a_1',
    clear h_run_a h_run_a_1 h_run_a_1',

    -- There is only one instruction left, instr.add. We can
    -- therefore construct the final star with h_run_a_1' and a
    -- new [instr.add] ⊢ _ ⟹ _

    --for that we need one hnth
    have hnth : list.nth ((acomp a ++ (acomp a_1 ++ [instr.add])))
                         ((acomp a_1).length +
                          (acomp a).length)
                = some instr.add :=
    begin
      rw list.nth_append_right,
      simp,
      simp,
    end,
    -- and a hiexec
    have hiexec  :=
      @iexec.add (↑(acomp a_1).length + ↑(acomp a).length)
                 s stk (aval a_1 s) (aval a s),
    have hexec1_add := exec1.exec1 hnth hiexec,
    -- rearrange some additions so they match with the goal
    abel at h_run_a_and_a_1,
    abel at hexec1_add,
    abel,
    -- Use transitivity to construct an evaluation of the
    -- whole program
    exact star.trans h_run_a_and_a_1 (star.single hexec1_add),
  }
end


end acomp

namespace bcomp
@[simp] def bcomp : bexp → bool → int → program
| (bexp.Bc v) f n := cond (v = f) [instr.jmp n] []
| (bexp.Not b) f n := bcomp b (!f) n
| (bexp.And b₁ b₂) f n :=
  let cb₂ := bcomp b₂ f n in
  let m := cond f (↑cb₂.length) (↑cb₂.length + n) in
  let cb₁ := bcomp b₁ ff m in
  cb₁ ++ cb₂
| (bexp.Less a₁ a₂) f n :=
  (acomp.acomp a₁) ++ (acomp.acomp a₂) ++ (cond f
                                                [instr.jmpless n]
                                                [instr.jmpge n])

#eval ( bcomp (bexp.And (bexp.Less (aexp.V "x") (aexp.V "y")) (bexp.Bc true)) false 3)
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Pattern.20matching.20with.20dependent.20types/near/211204742

@[simp] def bcomp_len  : bexp → bool → ℤ → ℕ
| (bexp.Bc v) f n := cond (v = f) 1 0
| (bexp.Not b) f n := bcomp_len b (!f) n
| (bexp.And b₁ b₂) f n :=
  let cb₂ := bcomp_len b₂ f n in
  let m := cond f (↑cb₂) (↑cb₂ + n) in
  let cb₁ := bcomp_len b₁ false m in
  cb₁ + cb₂
| (bexp.Less a₁ a₂) f n :=
  (acomp.acomp a₁).length + (acomp.acomp a₂).length + 1

lemma bcomp_len_eq_bcomp_len_n { b f n n' } : (bcomp_len b f n) = (bcomp_len b f n') :=
begin
  induction' b,
  all_goals {
    simp,
  },
  {
    exact ih,
  },
  {
    rw @ih_b_1 f n n',
    rw @ih_b ff (cond f ↑(bcomp_len b_1 f n') (↑(bcomp_len b_1 f n') + n))
                (cond f ↑(bcomp_len b_1 f n') (↑(bcomp_len b_1 f n') + n')),
  },
end

lemma bcomp_len_eq_length_bcomp {b f n } : (bcomp_len b f n) = (bcomp b f n).length :=
begin
  induction' b,
  {
    show bcomp_len (bexp.Bc b) f n = list.length (bcomp (bexp.Bc b) f n),
    simp,
    cases' b,
    all_goals {
      cases' f,
      all_goals {
        simp,
      },
    },
  },
  {
    show bcomp_len (bexp.Not b) f n = list.length (bcomp (bexp.Not b) f n),
    simp,
    exact @ih (!f) n,
  },
  {
    show bcomp_len (bexp.And b b_1) f n = list.length (bcomp (bexp.And b b_1) f n),
    simp,
    cases' f ,
    {
      simp,
      rw ← @ih_b_1 ff n,
      rw ← @ih_b ff (↑(bcomp_len b_1 ff n) + n),
    },
    {
      simp,
      rw ← @ih_b_1 tt n,
      rw ← @ih_b ff ↑(bcomp_len b_1 tt n),
    },
  },
  {
    show bcomp_len (bexp.Less x x_1) f n = list.length (bcomp (bexp.Less x x_1) f n),
    simp,
    cases' f,
    all_goals {
      simp,
      refl,
    },
  },
end

-- The length of a jump doesn't change how many instructions are generated by bcomp
lemma length_bcomp_eq_length_bcomp {b f n}  (n') : (bcomp b f n).length = (bcomp b f n').length :=
begin
  rw ← bcomp_len_eq_length_bcomp,
  rw ← bcomp_len_eq_length_bcomp,
  exact bcomp_len_eq_bcomp_len_n,
end

-- Useful for normalizing `length (bcomp b f n)` for all values of n
@[simp] lemma length_bcomp_eq_length_bcomp_zero {b f n} :
              (bcomp b f n).length = (bcomp b f 0).length :=
by apply length_bcomp_eq_length_bcomp



lemma correct { b f s stk } {n : ℤ} (hpos : 0 ≤ n) :
              (bcomp b f n) ⊢
                   (0, s, stk) ⇒*
                   (↑(bcomp b f n).length + (cond (bval b s = f) n 0),
                    s, stk) :=
begin
  simp,
  induction' b,
  case bexp.Bc {
    show (bcomp (bexp.Bc b) f n) ⊢
              (0, s, stk) ⇒*
              (↑(list.length (bcomp (bexp.Bc b) f 0)) +
                 ite (bval (bexp.Bc b) s = f)
                     n
                     0,
               s,
               stk),

    cases' (em (b = f)),
    {
      simp [h],
      show [instr.jmp n] ⊢ (0, s, stk) ⇒* (1 + n, s, stk),
      exact star.single (@exec1.exec1 [instr.jmp n] s stk (_) _ _
                         (by simp)
                         (@iexec.jmp 0 s stk n)),
    },
    {
      simp,
      show (ite (b = f) [instr.jmp n] list.nil) ⊢
                        (0, s, stk) ⇒*
                        (↑((ite (b = f)
                                [instr.jmp 0]
                                list.nil).length) +
                            ite (b = f)
                                n
                                0,
                        s,
                        stk),
      rw ← ite_not,
      simp [h],
    }
  },
  case bexp.Not {
    simp,
    have ih' : (bcomp b (!f) n) ⊢
               (0, s, stk) ⇒*
               (↑(bcomp b (!f) 0).length +
                 ite (bval b s = !f)
                     n
                     0,
                s,
                stk)
         := @ih (!f) s stk n hpos,
    -- We know that hpos : 0 ≤ n, therefore n must be a ℕ
    cases' n,
    case int.of_nat {
      clear hpos,
      simp at ih',
      simp,
      cases f,
      repeat {
        simp,
        simp at ih',
        exact ih',
      },
    },
    case neg_succ_of_nat {
      simp at hpos, contradiction,
    },
  },
  case bexp.And {
  show (bcomp (b.And b_1) f n) ⊢
        (0, s, stk) ⇒*
        (↑(bcomp (b.And b_1) f 0).length +
                 ite (bval (b.And b_1) s = f)
                     n
                     0,
         s,
         stk),
    -- We know that hpos : 0 ≤ n, therefore n must be a ℕ
    cases' n,
    {
      have ih_b' : (bcomp b ff (↑((bcomp b_1 f ↑n).length) + cond f 0 ↑n)) ⊢
                    (0, s, stk) ⇒*
                    (↑(bcomp b ff 0).length +
                      ite (bval b s = ff)
                          (↑(bcomp b_1 f ↑n).length + cond f 0 ↑n)
                          0,
                     s,
                     stk)
      := @ih_b ff s stk ((bcomp b_1 f n).length + (cond f 0 n))
      (begin
        -- show  0 ≤ ↑((bcomp b_1 f ↑n).length) + cond f 0 ↑n,
        cases' f,
        {
          simp,
          norm_cast,
          simp,
        },
        {simp,}
      end),
      have ih_b_1' := @ih_b_1 f s stk n hpos,
      clear ih_b,
      clear ih_b_1,
      simp [bcomp] at *,
      -- There are many terms on the form (list.length (bcomp b ff n)) for
      -- different values of n. The value of those terms do not depend on n so
      -- we can simplify with `length_bcomp_eq_length_bcomp_zero` and call them
      -- with the same name.
      generalize h_lenb : (list.length (bcomp b ff 0)) = lenb,
      generalize h_lenb' : (list.length (bcomp b_1 f 0)) = lenb_1,
      have ih_b'' := exec_append_right (bcomp b_1 f ↑n) ih_b',
      clear ih_b',
      rw cond_add f lenb_1 n,
      rw [h_lenb, h_lenb'] at *,
      apply star.trans ih_b'',
      cases' bool.or_intro (bval b s) with hbval_eq_tt hbval_eq_ff,
      {
        simp [hbval_eq_tt],
        cases' f,
        {
          simp [hbval_eq_tt],
          have ih_b_1'' := exec_append_left (bcomp b ff (↑lenb_1 + ↑n)) ih_b_1',
          simp [hbval_eq_tt] at ih_b_1'',
          rw [h_lenb', h_lenb] at *,
          nth_rewrite 0 [add_assoc],
          nth_rewrite 1 [add_comm],
          exact ih_b_1'',
        },
        {
          simp [hbval_eq_tt],
          have ih_b_1'' := exec_append_left (bcomp b ff (↑lenb_1 )) ih_b_1',
          simp [hbval_eq_tt] at ih_b_1'',
          rw [h_lenb', h_lenb] at *,
          nth_rewrite 0 [add_assoc],
          nth_rewrite 0 [add_comm],
          apply ih_b_1'',
        }
      },
      {
        simp [hbval_eq_ff],
        have ih_b_1'' := exec_append_left (bcomp b ff (↑lenb_1 + cond f 0 ↑n)) ih_b_1',
        simp at ih_b_1'',
        rw [h_lenb, h_lenb'] at ih_b_1'',
        cases' f,
        {
          simp,
          nth_rewrite 0 add_assoc,
        },
        {
          simp,
        }
      }
    },
    {
      exfalso, simp at hpos, assumption,
    }
  },
  {
    cases' n,
    {
      simp, clear hpos,
      have hx := exec_append_right (acomp.acomp x_1) (@acomp.correct x s stk),
      have hx_1 := exec_append_left (acomp.acomp x) (@acomp.correct x_1 s ((aval x s) :: stk)),
      simp at hx_1,
      have tmp := exec_append_right (cond f [instr.jmpless ↑n] [instr.jmpge ↑n]) (star.trans hx hx_1),
      rw list.append_assoc at tmp,
      apply star.trans tmp,
      rw add_assoc,
      nth_rewrite 1 add_comm,
      apply exec_append_left (acomp.acomp x),
      rw ← (int.zero_add ↑(list.length (acomp.acomp x_1))),
      nth_rewrite 2 [add_comm],
      nth_rewrite 1 [int.zero_add],
      rw add_assoc,
      nth_rewrite 2 [add_comm],
      rw ← add_assoc,
      apply exec_append_left (acomp.acomp x_1),
      cases' f,
      {
        simp,
        apply star.single,
        apply @exec1.exec1 _ _ _ _ (instr.jmpge n) _,
        { simp },
        {
          cases' em (aval x_1 s ≤ aval x s),
          {
            simp [h],
            {
              apply iexec.jmpge_true,
              { simp, exact h },
            },
          },
          {
            simp [h],
            {
              apply iexec.jmpge_false,
              { simp, simp at h, exact h },
            },
          }
        }
      },
      {
        simp,
        apply star.single,
        apply @exec1.exec1 _ _ _ _ (instr.jmpless n) _,
        { simp },
        {
          cases' em (aval x_1 s ≤ aval x s),
          {
            simp [le_iff_not_lt h],
            {
              apply iexec.jmpless_false,
              { simp, exact h },
            },
          },
          {
            simp [not_le_iff_lt h],
            {
              apply iexec.jmpless_true,
              {exact not_le_iff_lt h},
            },
          }
        }
      }
    },
    {
      exfalso, simp at hpos, exact hpos,
    }
  },
end

end bcomp

@[simp] def ccomp : stmt → program
| (stmt.skip)        := []
| (stmt.assign x a)  := (acomp.acomp a) ++ [instr.store x]
| (stmt.seq a b)     := (ccomp a) ++ (ccomp b)
| (stmt.ite b c₁ c₂) :=
  let cc₁ := ccomp c₁ in
  let cc₂ := ccomp c₂ in
  let cb  := bcomp.bcomp b ff (( list.length cc₁ ) + 1)
  in cb ++ cc₁ ++ [instr.jmp (list.length cc₂)] ++ cc₂
| (stmt.while b c) :=
  let cc           := ccomp c in
  let cb           := bcomp.bcomp b ff (list.length cc + 1)
  in cb ++ cc ++ [instr.jmp (- (list.length cb + list.length cc + 1) )]

#eval ccomp (stmt.ite (bexp.Less (aexp.V "u") (aexp.N 1)) (stmt.assign "u" (aexp.Plus (aexp.V "u") (aexp.N 1))) (stmt.assign "v" (aexp.V "u")))

lemma coe_bool_implies_eq_tt {b : bool} : ((↑b) : Prop) → b = tt :=
begin
{
  intro hb,
  cases' b,
  { simp, simp at hb, assumption, },
  { refl, }
}
end

lemma coe_not_bool_implies_eq_ff {b : bool} : ((¬ ↑b) : Prop) → b = ff :=
begin
{
  intro hb,
  cases' b,
  { simp, },
  {simp at hb, exfalso, assumption,   }
}
end

theorem correct {c s t stk} :
  (c, s) ⟶ t → (ccomp c) ⊢
                 (0, s, stk) ⇒*
                 (↑(ccomp c).length, t, stk) :=
begin
  intro hbig,
  induction' hbig,
  case big_step.skip {
    apply star.refl,
  },
  case big_step.assign {
    simp,
    have h_exec_a : (acomp.acomp a) ⊢ (0, t, stk) ⇒*
                                     (↑(acomp.acomp a).length,
                                      t,
                                      aval a t :: stk)
         := @acomp.correct a t stk,
    have h_exec_store :[instr.store x] ⊢ (↑0, t, aval a t :: stk) ⇒*
                                         (1, t{x ↦ aval a t}, stk)
    :=
      star.single (@exec1.exec1 [instr.store x]
                                t
                                (aval a t :: stk)
                                (1, t{x ↦ aval a t}, stk) _  0
                                (by simp )
                                (iexec.store x)),
    have h_exec_a' : (acomp.acomp a ++ [instr.store x]) ⊢
                      (0, t, stk) ⇒*
                      (↑((acomp.acomp a).length),
                       t,
                       aval a t :: stk)
    := exec_append_right [instr.store x] h_exec_a,
    have h_exec_store' : (acomp.acomp a ++ [instr.store x]) ⊢
                          (↑0 + ↑((acomp.acomp a).length),
                           t,
                           aval a t :: stk) ⇒*
                          (1 + ↑((acomp.acomp a).length), t{x ↦ aval a t}, stk)
    := exec_append_left (acomp.acomp a) h_exec_store,
    simp at h_exec_store',
    rw add_comm at h_exec_store',
    exact star.trans h_exec_a' h_exec_store',
  },
  case big_step.seq {
    simp,
    have ih :(ccomp S ++ ccomp T) ⊢ (0, s, stk) ⇒* (↑((ccomp S).length), t, stk)
         := exec_append_right (ccomp T) (@ih_hbig stk),
    have ih1 : (ccomp S ++ ccomp T) ⊢
               (0 + ↑(ccomp S).length, t, stk) ⇒*
               (↑(ccomp T).length + ↑(ccomp S).length,
                t_1, stk)
          := exec_append_left (ccomp S) (@ih_hbig_1 stk),
    simp at ih1,
    rw add_comm at ih1,
    exact star.trans ih ih1,
  },
  case big_step.ite_true {
    show (ccomp (stmt.ite b S T)) ⊢
         (0, s, stk) ⇒*
         (↑((ccomp (stmt.ite b S T)).length),
          t, stk),
    simp,
    have hS : (ccomp S) ⊢ (0, s, stk) ⇒* (↑((ccomp S).length), t, stk)
         := @ih stk,
    have hbool : (bcomp.bcomp b ff (↑((ccomp S).length) + 1)) ⊢
                 (0, s, stk) ⇒*
                 (↑((bcomp.bcomp b ff 0).length),
                  s,
                  stk)
     :=
     begin
        have tmp := @bcomp.correct b ff s stk ((ccomp S).length + 1)
                         (list.zero_le_length_add_one),
        have hcond' : bval b s = tt
            := coe_bool_implies_eq_tt hcond,
        simp [hcond, hcond'] at tmp,
        exact tmp,
     end,
    have hexec_bool : (bcomp.bcomp b ff
                              (1 + ↑((ccomp S).length)) ++
                               (ccomp S ++
                                instr.jmp ↑((ccomp T).length) :: ccomp T)) ⊢
                 (0, s, stk) ⇒*
                 (↑((bcomp.bcomp b ff 0).length), s, stk)
    :=
    begin
      have tmp := exec_append_right (instr.jmp ↑(list.length (ccomp T))
                                     :: ccomp T)
                                    (exec_append_right (ccomp S) hbool),
      rw list.append_assoc at tmp,
      abel at tmp,
      exact tmp,
    end,
    have hexec_S : (bcomp.bcomp b ff (1 + ↑(ccomp S).length) ++
                   (ccomp S ++ instr.jmp ↑((ccomp T).length) :: ccomp T)) ⊢
                  (↑(bcomp.bcomp b ff 0).length, s, stk) ⇒*
                  (↑(ccomp S).length + ↑(bcomp.bcomp b ff 0).length,
                   t, stk)

    :=
    begin
      have tmp := exec_append_right (instr.jmp ↑(list.length (ccomp T)) :: ccomp T)
                   (exec_append_left (bcomp.bcomp b ff (↑(list.length (ccomp S)) + 1))
                                     (@ih stk)),
      simp at tmp,
      abel at tmp,
      exact tmp,
    end,
    have hjmp : [instr.jmp ↑((ccomp T).length)] ⊢
                (↑0, t, stk) ⇒*
                (1 + ↑((ccomp T).length), t, stk)
    := star.single
         (@exec1.exec1 [instr.jmp (ccomp T).length] t stk
                       (1 + (ccomp T).length, t, stk)
                       (instr.jmp (ccomp T).length)
                       0 (by simp)
                       (iexec.jmp (ccomp T).length)),

    have hexec_jmp : (bcomp.bcomp b ff (1 + ↑((ccomp S).length)) ++
                       (ccomp S ++ instr.jmp ↑((ccomp T).length) :: ccomp T))
                      ⊢
                      (↑((ccomp S).length) + ↑((bcomp.bcomp b ff 0).length),
                       t, stk)
                      ⇒*
                      (1 + (↑(ccomp S).length +
                        (↑(ccomp T).length +
                         ↑(bcomp.bcomp b ff 0).length)),
                       t, stk)
    :=
    begin
      have tmp :=
           exec_append_left (bcomp.bcomp b ff
                                         (↑(list.length (ccomp S)) + 1) ++
                                           (ccomp S))
                                         (exec_append_right (ccomp T) hjmp ),
      simp at tmp,
      abel at tmp,
      exact tmp,
    end,
    abel,
    exact star.trans (star.trans hexec_bool hexec_S) hexec_jmp,
  },
  case big_step.ite_false {
    simp,
    have hbool : (bcomp.bcomp b ff (1 + ↑((ccomp S).length))) ⊢
                 (0, s, stk) ⇒*
                 (1 + (↑((ccomp S).length) + ↑((bcomp.bcomp b ff 0).length)),
                  s, stk)
    :=
    begin
      have tmp := @bcomp.correct b ff s stk ((ccomp S).length + 1)
                                 (list.zero_le_length_add_one),
      have hcond' := coe_not_bool_implies_eq_ff hcond,
      simp [hcond, hcond'] at tmp,
      abel at tmp,
      exact tmp,
    end,
    have hexec_bool : (bcomp.bcomp b ff (1 + ↑((ccomp S).length)) ++
                        (ccomp S ++ instr.jmp ↑((ccomp T).length) :: ccomp T))
                      ⊢
                      (0, s, stk) ⇒*
                      (1 + (↑((ccomp S).length) + ↑((bcomp.bcomp b ff 0).length)),
                      s, stk)
    :=
    begin
      have tmp := exec_append_right (instr.jmp ↑(list.length (ccomp T)) :: ccomp T)
                    (exec_append_right (ccomp S) hbool),
      rw list.append_assoc at tmp,
      exact tmp,
    end,
    have hS : (ccomp T) ⊢ (0, s, stk) ⇒*
                         (↑((ccomp T).length), t, stk)
        := @ih stk,
    have hexec_S : (bcomp.bcomp b ff (1 + ↑(ccomp S).length) ++
                    (ccomp S ++
                     instr.jmp ↑((ccomp T).length) :: ccomp T))
                   ⊢
                   (1 + (↑((ccomp S).length) + ↑((bcomp.bcomp b ff 0).length)),
                    s, stk)
                   ⇒*
                   (1 + (↑(ccomp S).length
                         + (↑(ccomp T).length + ↑(bcomp.bcomp b ff 0).length)),
                    t, stk)
    :=
    begin
      have tmp :=
           exec_append_left ((bcomp.bcomp b ff (↑(list.length (ccomp S)) + 1))
                              ++ (ccomp S) ++ [instr.jmp ↑(list.length (ccomp T))])
                            hS,
      simp at tmp,
      abel at tmp,
      exact tmp,
    end,
    abel,
    exact star.trans hexec_bool hexec_S,
  },
  case big_step.while_true {
    rename hbig hbig_S,
    rename hbig_1 hbig_while_b,
    rename ih_hbig ih_exec_S,
    rename ih_hbig_1 ih_exec_while_b,
    simp [hcond, coe_bool_implies_eq_tt hcond] at ih_exec_while_b,
    simp,
    set n := (-(1 : ℤ) + (-↑(list.length (ccomp S))
                          + -↑(list.length (bcomp.bcomp b ff 0))))
        with hn,
    have hexec_b : (bcomp.bcomp b ff (↑(ccomp S).length + 1)) ⊢
                    (0, s, stk) ⇒*
                    (↑(bcomp.bcomp b ff 0).length,
                     s,
                     stk)
         :=
    begin
         have tmp := @bcomp.correct b ff s stk (↑(list.length (ccomp S)) + 1)
                                    (list.zero_le_length_add_one),
         simp [hcond, coe_bool_implies_eq_tt hcond] at tmp,
         exact tmp,
    end ,
    have hexec_b' :
    (bcomp.bcomp b ff (↑((ccomp S).length) + 1) ++
          (ccomp S ++ [instr.jmp n])) ⊢
            (0, s, stk) ⇒*
            (↑((bcomp.bcomp b ff 0).length), s, stk)
    := exec_append_right ((ccomp S ++ [instr.jmp n]))
                  hexec_b,
    abel at hexec_b',
    clear hexec_b,
    have hexec_S : (bcomp.bcomp b ff (1 + ↑(ccomp S).length) ++
                    (ccomp S ++ [instr.jmp n]))
                    ⊢
                    (↑(bcomp.bcomp b ff 0).length,
                     s,
                     stk) ⇒*
                    (↑(ccomp S).length + ↑(bcomp.bcomp b ff 0).length,
                     t,
                     stk)
         := begin
            have tmp := exec_append_left (bcomp.bcomp b ff (↑(list.length (ccomp S)) + 1))
                        (exec_append_right [instr.jmp n]
                        (@ih_exec_S stk)),
            simp [hcond, coe_bool_implies_eq_tt hcond] at tmp,
            abel at tmp,
            exact tmp,
            end,
    clear ih_exec_S,
    have hexec_jmp : (bcomp.bcomp b ff (1 + ↑(ccomp S).length) ++
                      (ccomp S ++ [instr.jmp n]))
                      ⊢
                      (↑(ccomp S).length + ↑(bcomp.bcomp b ff 0).length,
                       t,
                       stk) ⇒*
                      (0, t, stk)
                      :=
         begin
         have tmp := star.single
                         (@exec1.exec1 [instr.jmp n]
                                       t stk _
                                       (instr.jmp n)
                                       0 (by simp)
                                       (iexec.jmp n)),
         have tmp' := exec_append_left (bcomp.bcomp b ff (↑(list.length (ccomp S)) + 1) ++ ccomp S) tmp,
         simp at tmp',
         abel at tmp',
         exact tmp'
         end,
    have hexec_b_S := star.trans hexec_b' hexec_S,
    clear hexec_b' hexec_S,
    abel,
    have h_exec_b_S_jmp := star.trans hexec_b_S hexec_jmp,
    abel at ih_exec_while_b,
    exact star.trans h_exec_b_S_jmp (@ih_exec_while_b stk),
  },
  case big_step.while_false {
    simp,
    have hexec_b : (bcomp.bcomp b ff (↑((ccomp S).length) + 1)) ⊢
                    (0, t, stk) ⇒*
                    (↑(bcomp.bcomp b ff (↑((ccomp S).length) + 1)).length +
                        cond (to_bool (bval b t = ff))
                             (↑((ccomp S).length) + 1)
                             0,
                     t,
                     stk)
        := @bcomp.correct b ff t stk (↑(list.length (ccomp S)) + 1)
                                     (list.zero_le_length_add_one),
    simp [hcond, coe_not_bool_implies_eq_ff hcond] at hexec_b,
    let n : ℤ := -1 + (-↑(list.length (ccomp S)) + -↑(list.length (bcomp.bcomp b ff 0))),
    exact exec_append_right (ccomp S ++ [instr.jmp n])
                            hexec_b,
  },
end
