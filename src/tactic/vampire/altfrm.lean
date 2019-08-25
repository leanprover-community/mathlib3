import tactic.omega

universe u 

variables {α β : Type}

def rl  (α : Type) : Type := list α → Prop
def fn  (α : Type) : Type := list α → α
def rls (α : Type) : Type := nat → rl α
def fns (α : Type) : Type := nat → fn α
def vas (α : Type) : Type := nat → α

@[derive decidable_eq]
inductive xtrm : bool → Type 
| vr   : nat → xtrm ff
| fn   : nat → xtrm tt → xtrm ff
| nil  : xtrm tt 
| cons : xtrm ff → xtrm tt → xtrm tt 

def xtrm.size : ∀ {b : bool}, xtrm b → nat
| ff (xtrm.vr k)      := 0
| ff (xtrm.fn k ts)   := ts.size + 1
| tt xtrm.nil         := 0
| tt (xtrm.cons t ts) := t.size + ts.size + 1

@[reducible] def trm  := xtrm ff
@[reducible] def trms := xtrm tt

local notation `#` := xtrm.vr
local notation `$` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts

open nat

lemma size_tail_lt_size_cons {t : trm} {ts : trms} : 
  (xtrm.size ts) < xtrm.size (xtrm.cons t ts) :=  
by { apply lt_of_lt_of_le (lt_succ_self _),
     unfold xtrm.size,
     rw add_assoc, 
     apply nat.le_add_left }

namespace trms 

def mem (t : trm) : trms → Prop
| []*        := false
| (s ::* ts) := t = s ∨ mem ts
using_well_founded {
  dec_tac := `[ apply size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

instance has_mem : has_mem trm trms := ⟨mem⟩ 

lemma mem_cons_iff (t s : trm) (ts : trms) : 
  t ∈ (s ::* ts) ↔ t = s ∨ t ∈ ts := iff.refl _

end trms

lemma lt_size_fn {k : nat} :
  ∀ {ts : trms} {s : trm}, 
  s ∈ ts → xtrm.size s < xtrm.size ($ k ts)  
| []*        := by rintros _ ⟨_⟩
| (t ::* ts) := 
  by { intros s h0,
       rw trms.mem_cons_iff at h0, cases h0,
       { subst h0, unfold xtrm.size, 
         repeat {rw [add_assoc]},
         apply lt_trans (lt_succ_self _),
         rw @add_lt_add_iff_left _ _ _ 1 _,
         apply succ_lt_succ (zero_lt_succ _) },
       apply lt_trans (@lt_size_fn ts _ h0), 
       apply succ_lt_succ,
       apply size_tail_lt_size_cons }

def trm.rec {C : trm → Sort u} 
  (h0 : ∀ k : nat, C (# k)) 
  (h1 : ∀ k : nat, ∀ ts : trms, 
    (∀ t : trm, t ∈ ts → C t) → C ($ k ts)) : 
  ∀ t : trm, C t 
| (# k)    := h0 _
| ($ k ts) := by { apply h1, intros s h2, apply trm.rec }
using_well_founded {
  dec_tac := `[ apply lt_size_fn, assumption ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}