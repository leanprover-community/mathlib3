/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import computability.encoding
import computability.turing_machine
import data.polynomial.basic
import data.polynomial.eval

namespace tm2
section

/-structure tm2 :=
 {K : Type}
 [K_decidable_eq : decidable_eq K] -- Index type of stacks
 (k₀ k₁ : K) -- input and output stack
 (Γ : K → Type) -- Type of stack elements
 (Λ : Type)
 [Λ_inhabited : inhabited Λ]
 (σ : Type)
 [σ_inhabited : inhabited σ]
 (M : tm2.machine Γ Λ σ)
-/

parameters {K : Type} [decidable_eq K] -- Index type of stacks
parameters (k₀ k₁ : K) -- input and output stack
parameters (Γ : K → Type) -- Type of stack elements
parameters (Λ : Type) [inhabited Λ]
parameters (σ : Type) [inhabited σ]

def stmt' := turing.TM2.stmt Γ Λ σ
def cfg' := turing.TM2.cfg Γ Λ σ

def machine := Λ → stmt'

set_option pp.proofs true

def init_list (s : list (Γ k₀)) : cfg' :=
{ l := option.some (default Λ),
  var := default σ,
  stk := λ k, dite (k = k₀) (λ h, begin rw h, exact s, end) (λ _,[]) }

def halt_list (s : list (Γ k₁)) : cfg':=
{ l := option.none,
  var := default σ,
  stk := λ k, dite (k = k₁) (λ h, begin rw h, exact s end) (λ _,[]) }

namespace option
@[simp] def bind_function {α β : Type*} (f : α → option β) : option α → option β :=
λ a, option.bind a f
end option

namespace turing
/-def evals_to {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ): Prop :=
∃ n, roption.of_option ((option.bind_function f)^[n] a) = b

def evals_to_in_time {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ) (m : ℕ) : Prop :=
∃ n ≤ m, roption.of_option ((option.bind_function f)^[n] a) = b-/

structure evals_to {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ) :=
(steps : ℕ)
(evals_in_steps : roption.of_option ((option.bind_function f)^[steps] a) = b)

structure evals_to_in_time {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ) (m : ℕ) extends evals_to f a b :=
(steps_le_m : steps ≤ m)

-- TODO: evals_to is refl, trans (and in fact the closure of the graph of f under reflexivity and transitivity).
end turing

def tm_outputs (tm : machine) (l : list (Γ k₀)) (l' : roption (list (Γ k₁))) :=
turing.evals_to (turing.TM2.step tm) (init_list l) ((roption.map halt_list) l')

def tm_outputs_in_time (tm : machine) (l : list (Γ k₀)) (l' : roption (list (Γ k₁))) (m : ℕ) :=
turing.evals_to_in_time (turing.TM2.step tm) (init_list l) ((roption.map halt_list) l') m

lemma tm_outputs_in_time.to_tm_outputs (tm : machine) (l : list (Γ k₀)) (l' : roption (list (Γ k₁))) (m : ℕ) :
tm_outputs_in_time tm l l' m → tm_outputs tm l l' :=
begin
  sorry,
end

private structure computable_by_tm_aux (f : list (Γ k₀) →. list (Γ k₁)) :=
( tm: machine )
( outputs_f: ∀ (l : list (Γ k₀)), (f l ≠ none) → tm_outputs tm l (f l) )

private structure computable_by_tm_in_time_aux (f : list (Γ k₀) →. list (Γ k₁)) :=
( tm: machine )
( time: ℕ → ℕ )
( proof: ∀ (l : list (Γ k₀)), (f l ≠ none) → tm_outputs_in_time tm l (f l) (time (sizeof l)) )

private structure computable_by_tm_in_poly_time_aux (f : list (Γ k₀) →. list (Γ k₁)) :=
( tm: machine )
( time: polynomial ℕ )
( proof: ∀ (l : list (Γ k₀)), (f l ≠ none) → tm_outputs_in_time tm l (f l) (time.eval (sizeof l)) )

lemma computable_by_tm_in_time_aux.to_computable_by_tm_aux (f : list (Γ k₀) →. list (Γ k₁)) :
computable_by_tm_in_time_aux f → computable_by_tm_aux f :=
begin
  sorry,
end

lemma computable_by_tm_in_poly_time_aux.to_computable_by_tm_in_time_aux (f : list (Γ k₀) →. list (Γ k₁)) :
computable_by_tm_in_poly_time_aux f → computable_by_tm_in_time_aux f :=
begin
  sorry,
end

section
parameters ( σ_fin : fintype σ)
parameters ( Γk₀_fin : fintype (Γ k₀))

def computable_by_tm (f : list (Γ k₀) →. list (Γ k₁)) := computable_by_tm_aux f
def computable_by_tm_in_time (f : list (Γ k₀) →. list (Γ k₁)) := computable_by_tm_in_time_aux f
def computable_by_tm_in_poly_time (f : list (Γ k₀) →. list (Γ k₁)) := computable_by_tm_in_poly_time_aux f

end
end
end tm2

structure fin_tm2 :=
 {K : Type}
 [K_decidable_eq : decidable_eq K] -- Index type of stacks
 (k₀ k₁ : K) -- input and output stack
 (Γ : K → Type) -- Type of stack elements
 (Λ : Type)
 [Λ_inhabited : inhabited Λ]
 (σ : Type)
 [σ_inhabited : inhabited σ]
 [σ_fin : fintype σ]
 [Γk₀_fin : fintype (Γ k₀)]
 (M : tm2.machine Γ Λ σ)

def tm_2_outputs_list {Γ Γ' : Type} (tm : fin_tm2) (l : list Γ) (l' : roption (list Γ'))
  (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ') : Type :=
@tm2.tm_outputs tm.K tm.K_decidable_eq tm.k₀ tm.k₁ tm.Γ tm.Λ tm.Λ_inhabited tm.σ tm.σ_inhabited tm.M begin rw hi, exact l end begin rw ho, exact l' end

def tm_2_outputs_list_in_time {Γ Γ' : Type} (tm : fin_tm2) (l : list Γ) (l' : roption (list Γ'))
  (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ') (m : ℕ): Type :=
@tm2.tm_outputs_in_time tm.K tm.K_decidable_eq tm.k₀ tm.k₁ tm.Γ tm.Λ tm.Λ_inhabited tm.σ tm.σ_inhabited tm.M begin rw hi, exact l end begin rw ho, exact l' end m

def computable_by_tm_2_list {Γ Γ' : Type} (f : list Γ →. list Γ') : Prop :=
∃ (tm : fin_tm2) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ'), ∀ l, (f l ≠ none) → tm_2_outputs_list tm l (f l) hi ho

def computable_by_tm_2_list_in_poly_time {Γ Γ' : Type} (f : list Γ →. list Γ') : Prop :=
∃ (tm : fin_tm2) (hi : tm.Γ tm.k₀ = Γ) (ho : tm.Γ tm.k₁ = Γ') (p : polynomial ℕ), ∀ l, (f l ≠ none) → tm_2_outputs_list_in_time tm l (f l) hi ho (p.eval (sizeof l))

--attribute [class] fin_encoding

def computable_by_tm_2 {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) : Prop := --
∃ (tm : fin_tm2) (hi : tm.Γ tm.k₀ = ea.Γ) (ho : tm.Γ tm.k₁ = eb.Γ), ∀ a, tm_2_outputs_list tm (ea.encode a) (roption.some (eb.encode (f a))) hi ho

def computable_by_tm_2_in_poly_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) : Prop := --
∃ (tm : fin_tm2) (hi : tm.Γ tm.k₀ = ea.Γ) (ho : tm.Γ tm.k₁ = eb.Γ) (p : polynomial ℕ), ∀ a, tm_2_outputs_list_in_time tm (ea.encode a) (roption.some (eb.encode (f a))) hi ho (p.eval (sizeof (ea.encode a)))
--@computable_by_tm_2_list ea.Γ eb.Γ (λ l, (option.map eb.encode) ((option.map f) (ea.decode l)))

open turing.TM2.stmt

def id_computer (α : Type) (ea : fin_encoding α) : fin_tm2 :=
{ K := fin 1,
  K_decidable_eq := fin.decidable_eq 1,
  k₀ := 0,
  k₁ := 0,
  Γ := λ _, ea.Γ,
  Λ := fin 1,
  Λ_inhabited := unique.inhabited,
  σ := fin 1,
  σ_inhabited := unique.inhabited,
  σ_fin := unique.fintype,
  Γk₀_fin := ea.Γ_fin,
  M := λ _, halt }

open tm2

def id_computable (α : Type) (ea : fin_encoding α) : @computable_by_tm_2 α α ea ea (id: α → α) := begin
  let tr := id_computer α ea,
  use tr,
  use rfl,
  use rfl,
  intro a,
  simp,
  suffices h' : turing.TM2.step tr.M = (λ c, begin
    cases c.l,
    exact none,
    exact some (turing.TM2.cfg.mk none c.var c.stk)
  end ),
  {
    simp [h'],
    use 1,
    simp,
    split,
  },
  funext,
  cases x,
  cases x_l;
  simp,
  have h : (tr.M x_l) = halt := rfl,
  conv in (tr.M x_l) {rw h},
  simp,
end

#check @computable_by_tm_2 _
#check @id_computable _ _

def id_computable_in_poly_time {α : Type} (ea : fin_encoding α) : @computable_by_tm_2_in_poly_time α α ea ea (id: α → α) := begin
  let tr := id_computer α ea,
  use tr,
  use rfl,
  use rfl,
  use 1,
  intro a,
  simp,
  suffices h' : turing.TM2.step tr.M = (λ c, begin
    cases c.l,
    exact none,
    exact some (turing.TM2.cfg.mk none c.var c.stk)
  end ),
  {
    simp [h'],
    use 1,
    simp,
    split,
    trivial,
    split,
  },
  funext,
  cases x,
  cases x_l;
  simp,
  have h : (tr.M x_l) = halt := rfl,
  conv in (tr.M x_l) {rw h},
  simp,
end
