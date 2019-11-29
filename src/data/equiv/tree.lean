
/-
Copyright (c) 2019 E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: E.W.Ayers.
-/
import data.equiv.encodable data.equiv.list data.tree
universe u

namespace lisp

section defs

/-- A lisp-like expression. -/
inductive xp (α : Type u)
| CN : α → xp
| AP : xp → xp → xp
instance {α} [inhabited α]: inhabited (xp α) := ⟨xp.CN $ inhabited.default α⟩

/-- A token in the language expressions are unparsed to. -/
inductive token (α : Type u)
| OB {} : token   -- open paren
| CB {} : token   -- close paren
| X  : α → token -- data

meta instance {α : Type u} [has_to_format α] : has_to_format (token α) :=
⟨λ t, match t with |token.OB := "(" | token.CB := ")" | (token.X a) := to_fmt a end⟩

/-- State of a mini-parser. -/
inductive state (α : Type u) : Type u
| A : list (xp α) → state           -- expecting a `X`
| B : (xp α) → list (xp α) → state -- expecting a `)` or `(`
| F {} : state                       -- failure state

end defs

variables {α : Type u}

local notation ` str ` := list (token α)

open token lisp.xp state list

def paren : str → str := λ s, OB :: (s ++ [CB])

def step : state α → token α → state α
| (A s) (X n)       := B (CN n) s
| (B f s) OB        := A (f :: s)
| (B a (f :: s)) CB := B (AP f a) s
| _ _ := F

def out_xp : state α → option (xp α)
| (B e []) := some e
| _ := none

def unparse :  (xp α) → list (token α)
| (CN n) := [X n]
| (AP f a) := unparse f ++ paren (unparse a)

local notation ` run ` := foldl step
def parse : list (token α) → option (xp α) := out_xp ∘ foldl step (A [])

/-- `wf e ts` means that ts parses to e. -/
inductive wf : xp α → str → Prop
| cn {a} : wf (CN a) [X a]
| ap {f fl a al} : wf f fl → wf a al → wf (AP f a) (fl ++ paren al)

lemma unparse_is_wf : ∀ e : xp α, wf e $ unparse e :=
begin intro e, induction e, apply wf.cn, simp [unparse], apply wf.ap; assumption end

@[simp] lemma run_F_is_F : ∀ ts : str, run F ts = F :=
begin intro ts, induction ts with t ts ht, refl, induction t, repeat {simp[ht,step]} end

@[simp] lemma elim_step_1 {s} {n : α} :step (A s) (X n) = B (CN n) s := by refl

@[simp] lemma elim_step_2 {s} {f : xp α} :step (B f s) OB = A (f :: s) :=
begin induction s, refl, refl end

@[simp] lemma elim_step_3 {s} {f a : xp α} :step (B a (f :: s)) CB = B (AP f a) s := by refl

@[simp] lemma run_elim_of_wf : ∀ e {ts : str}, wf e ts → ∀ s, run (A s) ts = B e s :=
begin
  intros e ts hw,
  induction hw with n f sf a sa wf wa hf ha,
    refine λ s, rfl,
  intro s,
  simp [hf, ha, paren, step]
end

lemma out_xp_inj : ∀ {s} {e : xp α}, out_xp s = some e ↔ s = B e [] :=
begin
  intros s e,
  split,
    induction s with a b c d; simp [out_xp],
      induction c with x y z,
      intro h,
      refine ⟨option.no_confusion h id,rfl⟩,
      intro h,
      simp [out_xp] at h, cases h,
  intro h, rw h, simp [out_xp]
end

lemma parse_unparse_aux_1 :
  ∀ {ts : str} {e}, wf e ts → ∀ {ts₂ s}, run (A s) (ts ++ ts₂) = run (B e s) ts₂ :=
begin
  intros ts hw,
  induction hw with n l ls r rs wl wr hl hr,
    intros,
    simp [step, parse, out_xp],
    rw run_elim_of_wf, assumption,
  intros w ts₂ s, simp,
  rw run_elim_of_wf, apply w
end

lemma parse_unparse_aux_2 :
  ∀ {a} {ts : str}, wf a ts → ∀ {f s}, run (A $ f :: s) ts = B a (f::s) :=
begin
  intros a ts hw,
  induction hw with n l ls r rs wl wr hl hr,
    simp,
  simp [hl,hr, paren],
end

lemma parse_unparse [inhabited α] : ∀ {e : xp α}, parse (unparse e) = some e :=
begin
  intro e,
  induction e with n f a hf ha,
  refl,
  have h₁, apply unparse_is_wf f,
  have h₂, apply unparse_is_wf a,
  simp [unparse],
  apply out_xp_inj.2,
  have h₃ : run _ _ = run (B (option.iget (parse _)) _) _,
    apply parse_unparse_aux_1,
  rw hf, apply h₁,
  rw [h₃, hf],
  simp [paren, step],
  rw parse_unparse_aux_2 h₂,
  simp [step],
  apply_instance,
end

open encodable

variables [encodable α]

def token.encode : token α → nat
| (X n) := (encode n) + 2
| OB := 0
| CB := 1

def token.decode : nat → option (token α)
| 0 := some OB
| 1 := some CB
| (n+2) :=  X <$> (@encodable.decode _ _ n)

def token.dec_enc : ∀ t : token α, token.decode (token.encode t) = some t :=
begin
  intro t, cases t, refl, refl,
  simp [token.encode, token.decode],
  refine encodable.encodek t
end

instance token.encodable : encodable (token α) := {encode := token.encode, decode :=
token.decode, encodek := token.dec_enc}

instance token.str : encodable str := by apply_instance

instance token.xp [inhabited α]: encodable (xp α) :=
encodable.of_left_injection unparse parse $ λ e, parse_unparse

end lisp

namespace tree

open lisp lisp.xp option

variables {α : Type u}

instance : inhabited (tree α) := ⟨nil⟩

private def enc : tree α → lisp.xp (option α)
| tree.nil := CN none
| (tree.node a l r) := AP (AP (CN (some a)) (enc l)) (enc r)

private def dec : xp (option α) → option (tree α)
| (xp.CN none) := some tree.nil
| (AP (AP (CN (some a)) (l)) (r)) := tree.node a (iget $ dec l) (iget $ dec r)
| _ := none

private def dec_enc : ∀ {t : tree α}, dec (enc t) = some t :=
begin intro t, induction t with a l r hl hr, refl, simp [enc, dec, hl,hr], refl  end

instance [encodable α] : encodable (tree α) :=
encodable.of_left_injection enc dec $ λ t, dec_enc

end tree
