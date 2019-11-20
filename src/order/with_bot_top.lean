import order.conditionally_complete_lattice

open lattice

open_locale classical

/- with_top -/

noncomputable instance with_top.conditionally_complete_lattice.has_Sup
  {α : Type*} [conditionally_complete_lattice α] : has_Sup (with_top α) :=
⟨λ S, if ⊤ ∈ S then ⊤ else
      let So := (coe ⁻¹' S : set α) in
      if bdd_above So then ↑(Sup So) else ⊤⟩

instance with_top.conditionally_complete_lattice.has_Inf
  {α : Type*} [conditionally_complete_lattice α] : has_Inf (with_top α) :=
⟨λ S, ↑(Inf (coe ⁻¹' S) : α)⟩

noncomputable instance {α : Type*} [conditionally_complete_lattice α] :
  conditionally_complete_lattice (with_top α) :=
{ le_cSup := λ S a hS haS,
    let So := (coe ⁻¹' S : set α) in
    show a ≤ (ite (⊤ ∈ S) ⊤ (ite (bdd_above So) ↑(Sup So) ⊤)),
    begin split_ifs,
    { exact le_top},
    { cases a, contradiction, exact with_top.some_le_some.2 (le_cSup h_1 haS)},
    { exact le_top},
    end,
  cSup_le := λ S a hS haS,
    let So := (coe ⁻¹' S : set α) in
    begin dsimp, sorry end,
  cInf_le := sorry,
  le_cInf := sorry,
  ..with_top.lattice,
  ..with_top.conditionally_complete_lattice.has_Sup,
  ..with_top.conditionally_complete_lattice.has_Inf
}


-- note: there does not seem to be a conditionally_complete_lattice_bot

-- we now embark on the construction of complete_lattice (with_bot (with_top α))
-- for a conditionally complete lattice α

namespace with_bot_top

instance (α : Type*) : has_coe α (with_bot (with_top α)) := ⟨some ∘ some⟩

variables {α : Type*} [preorder α]

instance with_bot_top.with_top_coe : has_coe (with_top α) (with_bot (with_top α)) := ⟨some⟩
@[simp, elim_cast] protected lemma coe_le {x y : α} :
  (x : with_bot (with_top α) ) ≤ (y : with_bot (with_top α)) ↔ x ≤ y :=
by { unfold_coes, simp [has_le.le, preorder.le],
 }
@[simp, elim_cast] protected lemma coe_lt {x y : α} :
  (x : with_bot (with_top α)) < (y : with_bot (with_top α)) ↔ x < y :=
by { unfold_coes, norm_num }
@[simp, elim_cast] protected lemma coe_inj {x y : α} :
  (x : with_bot (with_top α)) = (y : with_bot (with_top α)) ↔ x = y :=
by { unfold_coes, simp [option.some_inj] }

variable [bounded_lattice α]

instance : bounded_lattice (with_bot (with_top α)) :=
{..with_bot.lattice, ..with_bot.order_bot, ..with_bot.order_top}

end with_bot_top

namespace lattice.conditionally_complete_lattice

open_locale classical

noncomputable instance {α : Type*} [conditionally_complete_lattice α] :
  has_Sup (with_bot (with_top α)) :=
⟨λ S,
  let Soc : set (with_top α) := coe ⁻¹' S in
  if h1 : Soc = ∅ then ⊥ else
  if h2 : ⊤ ∈ Soc then ⊤ else
  let Soo : set α := coe ⁻¹' Soc in
  if bdd_above Soo then ↑(Sup Soo) else ⊤⟩

#exit
noncomputable instance {α : Type*} [conditionally_complete_lattice α] :
  has_Inf (with_bot (with_top α)) :=
⟨λ S,
  if ⊥ ∈ S then ⊥ else
  let Soc : set (with_top α) := coe ⁻¹' S in
  if ¬bdd_below Soc then ⊥ else
  ↑(Inf Soc) else ⊥

--example : has_Inf (with_bot (with_top α)) := by apply_instance

/-- Adding a bot and a top to a conditionally complete lattice gives a complete lattice -/
instance {α : Type*} [conditionally_complete_lattice α]: complete_lattice (with_bot (with_top α)) := sorry

end lattice.conditionally_complete_lattice
