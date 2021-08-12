import tactic.alias

variables (α : Type*)

-- TODO: it would be better to split this up into bits to talk about
-- * tarski absolute geometry
-- * tarski dimensionless geometry
-- * tarski 3d geometry
class tarski :=
(betw : α → α → α → Prop)
(cong : α → α → α → α → Prop)
(cong_pseudo_refl : ∀ A B, cong A B B A)
(cong_inner_trans : ∀ {A B C D E F}, cong A B C D → cong A B E F → cong C D E F)
(cong_identity : ∀ {A B C}, cong A B C C → A = B)
(segment_construction : ∀ A B C D, ∃ E, betw A B E ∧ cong B E C D)
(five_segment : ∀ {A A' B B' C C' D D'},
  cong A B A' B' → cong B C B' C' → cong A D A' D' → cong B D B' D' →
  betw A B C → betw A' B' C' → A ≠ B → cong C D C' D')
(betw_identity : ∀ {A B}, betw A B A → A = B)
(inner_pasch : ∀ {A B C P Q}, betw A P C → betw B Q C → ∃ X, betw P X B ∧ betw Q X A)
(lower_dim {} : ∃ A B C, ¬betw A B C ∧ ¬betw B C A ∧ ¬betw C A B)
(upper_dim : ∀ {A B C P Q}, P ≠ Q → cong A B A Q → cong B P B Q → cong C P C Q →
  betw A B C ∨ betw B C A ∨ betw C A B)
(euclid : ∀ {A B C D T}, betw A D T → betw B D C → A ≠ D →
  ∃ X Y, betw A B X ∧ betw A C Y ∧ betw X T Y)

alias tarski.cong_inner_trans ← tarski.cong.inner_trans
alias tarski.cong_pseudo_refl ← tarski.cong.pseudo_refl
alias tarski.cong_identity ← tarski.cong.identity
alias tarski.betw_identity ← tarski.betw.identity
