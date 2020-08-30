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

parameters {K : Type} [decidable_eq K] -- Index type of stacks
parameters (k₀ k₁ : K) -- input and output stack
parameters (Γ : K → Type) -- Type of stack elements
parameters (Λ : Type) (main : Λ)
parameters (σ : Type) (initial_state : σ)

def stmt' := turing.TM2.stmt Γ Λ σ
def cfg' := turing.TM2.cfg Γ Λ σ

def machine := Λ → stmt'
end
end tm2

structure fin_tm2 :=
 {K : Type}
 [K_decidable_eq : decidable_eq K] -- Index type of stacks
 (k₀ k₁ : K) -- input and output stack
 (Γ : K → Type) -- Type of stack elements
 (Λ : Type)
 (main : Λ)
 (σ : Type)
 (initial_state : σ)
 [σ_fin : fintype σ]
 [Γk₀_fin : fintype (Γ k₀)]
 (M : tm2.machine Γ Λ σ)

namespace fin_tm2
def cfg (tm : fin_tm2 ) : Type := @tm2.cfg' tm.K tm.K_decidable_eq tm.Γ tm.Λ tm.σ

def step (tm : fin_tm2 ) : tm.cfg → option tm.cfg := @turing.TM2.step tm.K tm.K_decidable_eq tm.Γ tm.Λ tm.σ tm.M
end fin_tm2

def init_list (tm : fin_tm2) (s : list (tm.Γ tm.k₀)) : tm.cfg :=
{ l := option.some tm.main,
  var := tm.initial_state,
  stk := λ k, @dite (k = tm.k₀) (tm.K_decidable_eq k tm.k₀) (list (tm.Γ k)) (λ h, begin rw h, exact s, end) (λ _,[]) }

def halt_list (tm : fin_tm2) (s : list (tm.Γ tm.k₁)) : tm.cfg :=
{ l := option.none,
  var := tm.initial_state,
  stk := λ k, @dite (k = tm.k₁) (tm.K_decidable_eq k tm.k₁) (list (tm.Γ k)) (λ h, begin rw h, exact s, end) (λ _,[]) }
  --stk := have decidable_eq tm.K := tm.K_decidable_eq, λ k, dite (k = tm.k₁) (λ h, begin rw h, exact s end) (λ _,[]) }

namespace option
@[simp] def bind_function {α β : Type*} (f : α → option β) : option α → option β :=
λ a, option.bind a f
end option

structure evals_to {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ) :=
(steps : ℕ)
(evals_in_steps : roption.of_option ((option.bind_function f)^[steps] a) = b)

structure evals_to_in_time {σ : Type*} (f : σ → option σ) (a : σ) (b : roption σ) (m : ℕ) extends evals_to f a b :=
(steps_le_m : steps ≤ m)

-- TODO: evals_to is refl, trans (and in fact the closure of the graph of f under reflexivity and transitivity).

def tm2_outputs (tm : fin_tm2) (l : list (tm.Γ tm.k₀)) (l' : roption (list (tm.Γ tm.k₁))) :=
evals_to tm.step (init_list tm l) ((roption.map (halt_list tm)) l')

def tm2_outputs_in_time (tm : fin_tm2) (l : list (tm.Γ tm.k₀)) (l' : roption (list (tm.Γ tm.k₁))) (m : ℕ) :=
evals_to_in_time tm.step (init_list tm l) ((roption.map (halt_list tm)) l') m

lemma tm2_outputs_in_time.to_tm2_outputs (tm : fin_tm2) (l : list (tm.Γ tm.k₀)) (l' : roption (list (tm.Γ tm.k₁))) (m : ℕ) :
tm2_outputs_in_time tm l l' m → tm2_outputs tm l l' :=
begin
  sorry,
end

structure computable_by_tm2_aux (Γ₀ Γ₁ : Type) :=
( tm : fin_tm2 )
( input_alphabet : tm.Γ tm.k₀ = Γ₀ )
( output_alphabet : tm.Γ tm.k₁ = Γ₁ )

structure computable_by_tm2_list {Γ₀ Γ₁ : Type} (f : list Γ₀ →. list Γ₁) extends computable_by_tm2_aux Γ₀ Γ₁ :=
( outputs_f : ∀ (l : list Γ₀), (f l ≠ none) → tm2_outputs tm begin rw input_alphabet, exact l, end begin rw output_alphabet, exact (f l), end )

structure computable_by_tm2_in_time_list {Γ₀ Γ₁ : Type} (f : list Γ₀ →. list Γ₁) extends computable_by_tm2_aux Γ₀ Γ₁ :=
( time: ℕ → ℕ )
( outputs_f : ∀ (l : list Γ₀), (f l ≠ none) → tm2_outputs_in_time tm begin rw input_alphabet, exact l, end begin rw output_alphabet, exact (f l), end (time l.length) )

structure computable_by_tm2_in_poly_time_list {Γ₀ Γ₁ : Type} (f : list Γ₀ →. list Γ₁) extends computable_by_tm2_aux Γ₀ Γ₁ :=
( time: polynomial ℕ )
( outputs_f : ∀ (l : list Γ₀), (f l ≠ none) → tm2_outputs_in_time tm begin rw input_alphabet, exact l, end begin rw output_alphabet, exact (f l), end (time.eval l.length) )

example (p : polynomial ℕ) : ℕ → ℕ := λ x, p.eval x

lemma computable_by_tm2_in_time_list.to_computable_by_tm2_list {Γ₀ Γ₁ : Type} (f : list Γ₀ →. list Γ₁) :
computable_by_tm2_in_time_list f → computable_by_tm2_list f :=
begin
  sorry,
end

lemma computable_by_tm2_in_poly_time_list.to_computable_by_tm2_in_time_list {Γ₀ Γ₁ : Type} (f : list Γ₀ →. list Γ₁) :
computable_by_tm2_in_poly_time_list f → computable_by_tm2_in_time_list f :=
begin
  sorry,
end

structure computable_by_tm2 {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends computable_by_tm2_aux ea.Γ eb.Γ :=
(outputs_f : ∀ a, tm2_outputs tm begin rw input_alphabet, exact ea.encode a end begin rw output_alphabet, exact roption.some (eb.encode (f a)) end )

structure computable_by_tm2_in_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends computable_by_tm2_aux ea.Γ eb.Γ :=
( time: ℕ → ℕ )
( outputs_f : ∀ a, tm2_outputs_in_time tm begin rw input_alphabet, exact ea.encode a end begin rw output_alphabet, exact roption.some (eb.encode (f a)) end (time (ea.encode a).length) )

structure computable_by_tm2_in_poly_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) extends computable_by_tm2_aux ea.Γ eb.Γ :=
( time: polynomial ℕ )
( outputs_f : ∀ a, tm2_outputs_in_time tm begin rw input_alphabet, exact ea.encode a end begin rw output_alphabet, exact roption.some (eb.encode (f a)) end (time.eval (ea.encode a).length) )

lemma computable_by_tm2_in_time.to_computable_by_tm2 {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) :
computable_by_tm2_in_time ea eb f → computable_by_tm2 ea eb f :=
begin
  sorry,
end

lemma computable_by_tm2_in_poly_time.to_computable_by_tm2_in_time {α β : Type} (ea : fin_encoding α) (eb : fin_encoding β) (f : α → β) :
computable_by_tm2_in_poly_time ea eb f → computable_by_tm2_in_time ea eb f :=
begin
  sorry,
end

open turing.TM2.stmt

def id_computer (α : Type) (ea : fin_encoding α) : fin_tm2 :=
{ K := fin 1,
  K_decidable_eq := fin.decidable_eq 1,
  k₀ := 0,
  k₁ := 0,
  Γ := λ _, ea.Γ,
  Λ := fin 1,
  main := 0,
  σ := fin 1,
  σ_inhabited := unique.inhabited,
  σ_fin := unique.fintype,
  Γk₀_fin := ea.Γ_fin,
  M := λ _, halt }

open tm2

def id_computable (α : Type) (ea : fin_encoding α) : @computable_by_tm2 α α ea ea (id: α → α) := begin
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

#check @computable_by_tm2 _
#check @id_computable _ _

def id_computable_in_poly_time {α : Type} (ea : fin_encoding α) : @computable_by_tm2_in_poly_time α α ea ea (id: α → α) := begin
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
