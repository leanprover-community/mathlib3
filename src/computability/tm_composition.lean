/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent.
-/

import computability.encoding
import computability.tm_computable
import computability.fsum
import data.list.basic

namespace turing

namespace composition
noncomputable theory

section computer
open turing.TM2
open turing.TM2.stmt
open fsum

parameters (tm₂ tm₁ : fin_tm2) (hΓ : tm₂.Γ tm₂.k₀ = tm₁.Γ tm₁.k₁)
instance dK₁ : _ := tm₁.K_decidable_eq
instance dK₂ : _ := tm₂.K_decidable_eq
instance dK : _ := fsum.decidable_eq_fsum tm₂.k₀ tm₁.k₁
-- instance temp : fintype (fintype (fsum tm₂.k₀ tm₁.k₁)) := sorry
-- instance temp' : fintype (fintype (tm₂.Λ ⊕ tm₁.Λ)) := sorry

private def embed_tm₂_stmt : fin_tm2.stmt tm₂ →
stmt (elim _ _ tm₂.Γ tm₁.Γ hΓ) (tm₂.Λ ⊕ tm₁.Λ) (fsum tm₂.initial_state tm₁.initial_state)
| (push k f q) := push (inl' k) (extendl' f) (embed_tm₂_stmt q)
| (peek k f q) := peek (inl' k) (extendl' (λ s g, inl' (f s g))) (embed_tm₂_stmt q)
| (pop k f q) := pop (inl' k) (extendl' (λ s g, inl' (f s g))) (embed_tm₂_stmt q)
| (load f q) := load (extendl' (inl' ∘ f)) (embed_tm₂_stmt q)
| (branch f q r) := branch (extendl' f) (embed_tm₂_stmt q) (embed_tm₂_stmt r)
| (goto f) := goto (extendl' (sum.inl ∘ f))
| (halt) := halt

private def embed_tm₁_stmt : fin_tm2.stmt tm₁ →
stmt (elim _ _ tm₂.Γ tm₁.Γ hΓ) (tm₂.Λ ⊕ tm₁.Λ) (fsum tm₂.initial_state tm₁.initial_state)
| (push k f q) := push (inr' k) (extendr' f) (embed_tm₁_stmt q)
| (peek k f q) := peek (inr' k) (extendr' (λ s g, inr' (f s g))) (embed_tm₁_stmt q)
| (pop k f q) := pop (inr' k) (extendr' (λ s g, inr' (f s g))) (embed_tm₁_stmt q)
| (load f q) := load (extendr' (inr' ∘ f)) (embed_tm₁_stmt q)
| (branch f q r) := branch (extendr' f) (embed_tm₁_stmt q) (embed_tm₁_stmt r)
| (goto f) := goto (extendr' (sum.inr ∘ f))
| (halt) := goto (λ s, sum.inl tm₂.main )

-- class findeq (α : Type*) := ( fin : fintype α ) ( deq : decidable_eq α )

def computer : fin_tm2 := {
  K := fsum tm₂.k₀ tm₁.k₁,
  K_decidable_eq := dK,
  K_fin := @fsum.fintype_fsum _ _ _ _ tm₂.K_fin tm₁.K_fin tm₂.K_decidable_eq tm₁.K_decidable_eq,
  k₀ := inr' tm₁.k₀,
  k₁ := inl' tm₂.k₁,
  Γ := elim _ _ tm₂.Γ tm₁.Γ hΓ,
  Λ := tm₂.Λ ⊕ tm₁.Λ,
  main := sum.inr tm₁.main,
  Λ_fin := @sum.fintype tm₂.Λ tm₁.Λ tm₂.Λ_fin tm₁.Λ_fin,
  σ := fsum tm₂.initial_state tm₁.initial_state,
  initial_state := inr' tm₁.initial_state,
  σ_fin := @fsum.fintype_fsum _ _ _ _ tm₂.σ_fin tm₁.σ_fin (classical.dec_eq tm₂.σ) (classical.dec_eq tm₁.σ), -- Horror!
  Γk₀_fin := tm₁.Γk₀_fin,
  M := sum.elim (embed_tm₂_stmt ∘ tm₂.M) (embed_tm₁_stmt ∘ tm₁.M)
}

def embed_tm₁_cfg (c : fin_tm2.cfg tm₁): fin_tm2.cfg computer := {
  l := (option.map sum.inr) c.l,
  var := inr' c.var,
  stk := begin
    let h := elimr_prod tm₂.k₀ tm₁.k₁ (λ k, @list.nil (tm₂.Γ k)) c.stk,
    rw elimr_eq_elim tm₂.k₀ tm₁.k₁ tm₂.Γ tm₁.Γ hΓ at h,
    exact h,
  end
}

def embed_tm₂_cfg (c : fin_tm2.cfg tm₂): fin_tm2.cfg computer := {
  l := (option.map sum.inl) c.l,
  var := inl' c.var,
  stk := begin
    let h := eliml_prod tm₂.k₀ tm₁.k₁ c.stk (λ k, @list.nil (tm₁.Γ k)),
    rw eliml_eq_elim tm₂.k₀ tm₁.k₁ tm₂.Γ tm₁.Γ hΓ at h,
    exact h,
  end
}

end computer

open computability

lemma center_stack {α β γ : Type} (eα : fin_encoding α) (eβ : fin_encoding β) (eγ : fin_encoding γ)
(g : β → γ) (f : α → β) (hg : tm2_computable eβ eγ g) (hf : tm2_computable eα eβ f) :
hg.to_tm2_computable_aux.tm.Γ hg.to_tm2_computable_aux.tm.k₀ = hf.to_tm2_computable_aux.tm.Γ hf.to_tm2_computable_aux.tm.k₁ :=
begin

end

theorem X {α β γ : Type} (eα : fin_encoding α) (eβ : fin_encoding β) (eγ : fin_encoding γ)
(g : β → γ) (f : α → β) (hg : tm2_computable eβ eγ g) (hf : tm2_computable eα eβ f) :
tm2_computable eα eγ (g ∘ f) := {
  tm := computer hg.tm hf.tm begin end, -- !!!
  input_alphabet := hf.input_alphabet,
  output_alphabet := hg.output_alphabet,
  outputs_fun := λ a, {
    steps := (hg.outputs_fun (f a)).steps + (hf.outputs_fun a).steps,
    evals_in_steps := begin
      --suffices h : ((flip bind f)^[(hg.outputs_fun (f a)).steps] a) = some (f a)

      let tm₁ := hf.tm,
      let tm₂ := hg.tm,
      have hΓ : tm₂.Γ tm₂.k₀ = tm₁.Γ tm₁.k₁ := sorry,
      let tm := computer tm₂ tm₁ hΓ,
      let alph1 := hf.input_alphabet,
      let alph2 := hf.output_alphabet,
      let alph3 := hg.output_alphabet,

      /-have hΓ' : hf.to_computable_by_tm2_aux.tm.Γ hf.to_computable_by_tm2_aux.tm.k₁ = tm.Γ tm.k₁ :=
      begin
        change tm₁.Γ tm₁.k₁ = tm.Γ tm.k₁,
        -- have fsum.elim tm₂.Γ tm₁.Γ hΓ (fsum.inl tm₂.k₁) = tm.Γ tm.k₁,

        --change fsum.elim hg.tm.Γ hf.tm.Γ sorry
        --exact fsum.elim_inl hf.tm.Γ _ _ tm.k₁,
      end-/
      let la := (list.map alph1.inv_fun (eα.encode a)),
      let lb := (list.map alph2.inv_fun (eβ.encode (f a))),
      let lc := (list.map alph3.inv_fun (eγ.encode ((g ∘ f) a))),

      have h : evals_to tm.step (init_list tm la) ((option.map (halt_list tm)) (some lb)),
      sorry,
      --evals_to tm.step (init_list tm l) ((option.map (halt_list tm)) l')
    end
}}


--lemma X (l : list (computer.Γ computer.k₀)) (l' : option (list (computer.Γ computer.k₁))) (o₂ : tm2_outputs tm₂ l l' )
--(l : list (tm.Γ tm.k₀)) (l' : option (list (tm.Γ tm.k₁))) :=

end composition
end turing
