/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

 `vampire` uses proof output from Vampire discharge first-order goals.
-/

import system.io
import data.num.basic
import tactic.vampire.arifix
import tactic.vampire.reify
import tactic.vampire.proof_alt

universe u

variable {α : Type}

open tactic list

namespace vampire

local notation `#`     := term₂.var
local notation a `&` b := term₂.app a b

local notation `⟪` b `,` a `⟫` := form₂.lit b a
local notation p `∨₂` q        := form₂.bin tt p q
local notation p `∧₂` q        := form₂.bin ff p q
local notation `∃₂`            := form₂.qua tt
local notation `∀₂`            := form₂.qua ff

def dequantify : form₂ → form₂
| (form₂.lit b t)   := form₂.lit b t
| (form₂.bin b p q) := form₂.bin b p q
| (form₂.qua b p)   := dequantify p

def cnf : form₂ → mat
| (form₂.lit b t)  := [[(b, t)]]
| (p ∨₂ q) :=
  (list.product (cnf p) (cnf q)).map
    (λ x, append x.fst x.snd)
| (p ∧₂ q) := (cnf p) ++ (cnf q)
| (form₂.qua _ _) := []

def ex_count_core : form₂ → nat
| (form₂.lit _ _)   := 0
| (form₂.bin _ _ _) := 0
| (∀₂ p)            := ex_count_core p
| (∃₂ p)            := ex_count_core p + 1

@[reducible] def ex_count (p : form₂) : nat :=
ex_count_core $ prenexify $ swap_all ff p

def clausify (p : form₂) : mat :=
cnf $ form₂.neg $ dequantify $ prenexify $ swap_all ff p

#exit
lemma of_proof (k : nat) (m : mat) (c : cla) :


#exit
def tas (α : Type u) (k : nat) (p : form₂) : Prop :=
  ∀ M : model α, ∃ v : nat → α, p.holds (fmodel α k M v)

-- lemma tas_of_proof [inhabited α] (p : form₂) :
--    proof (ex_count_core p) (cnf (dequantify p).neg) [] →
--    tas α (ex_count_core p) p := sorry

#exit
--
-- lemma fam_of_tas_zero :
--   ∀ {p : form₂}, foq tt p → p.QF tt →
--   tas α (ex_count_core p) p → fam α p := sorry
--
-- lemma fam_of_tas :
--   ∀ p : form₂, foq tt p → p.QDF ff →
--   tas α (ex_count_core p) p → fam α p
-- | (form₂.lit b a)   := fam_of_tas_zero
-- | (form₂.bin b p q) := fam_of_tas_zero
-- | (form₂.qua tt p)  :=
--   by { intros h0 h1 h2,
--        apply fam_of_tas_zero h0 _ h2,
--        refine ⟨rfl, h1.right (λ h3, by cases h3)⟩ }
-- | (form₂.qua ff p)  :=
--   begin
--     intros h0 h1 h2 M x,
--     have foo := fam_of_tas p h0.right (h1.left rfl), -- (h1.left rfl) h2)
--     apply foo,
--   end
  -- λ h0 h1 h2, (fam_fa _ _).elim_right
  --   (fam_of_tas p h0.right (h1.left rfl) h2)

-- #exit
--

lemma arifix_of_proof (α : Type) [inhabited α] (p : form₂) :
  foq tt p → proof (ex_count p) (clausify p) [] →
  arifix (model.default α) p :=
begin
  intros h0 hρ,
  apply arifix_of_holds h0,
  rw ← (@swap_all_eqv α _ ff _ h0 (model.default α)),
  rw ← (@prenexify_eqv α _ _ (model.default α)),
  have h1 : foq tt (prenexify (swap_all ff p)),
  { apply foq_prenexify,
    apply foq_swap_all _ h0 },
  have h2 : form₂.QDF ff (prenexify (swap_all ff p)),
  { apply QDF_prenexify,
    apply QN_swap_all },

  -- apply (@id (fam α p) _),
  -- apply (forall_congr (@swap_all_eqv α _ ff _ h0)).elim_left,
  -- apply (forall_congr (@prenexify_eqv α _ _)).elim_left,


  -- apply fam_of_tas _ h1 h2,
  -- apply @tas_of_proof α _ (prenexify $ swap_all ff p) hρ,
end

end vampire
