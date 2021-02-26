import tactic.interactive
import tactic.ext
import tactic.tauto
import data.set.default
import data.finset.default

/-- tactic.tautology cannot deduce P b from (∀ b, P b ∧ Q b),
  but it can from (∀ b, P b) ∧ (∀ b, Q b). -/
lemma forall_and_iff_forall_and_forall {β} {P Q : β → Prop} :
  (∀ b, P b ∧ Q b) ↔ (∀ b, P b) ∧ ∀ b, Q b :=
iff.intro 
  (λ h1 : (∀ b, P b ∧ Q b), and.intro (λ b, (h1 b).left) (λ b, (h1 b).right)) 
  (λ h1 : (∀ b, P b) ∧ (∀ b, Q b), (λ b, and.intro (h1.left b) (h1.right b))) 
 
meta def set_tauth (classical_op:bool) : tactic unit :=
do tactic.ext1 [],
do lemmas ← simp_lemmas.mk_default,
do lemmas' ← simp_lemmas.add_simp lemmas `forall_and_iff_forall_and_forall,
do tactic.simp_all lemmas' [],
do tactic.tautology  {classical := classical_op}

/-- Prove tautological equality of two sets, using intuitionistic logic. -/
meta def set_taut : tactic unit := set_tauth ff

/-- Prove tautological equality of two sets, using classical logic. -/
meta def set_taut' : tactic unit := set_tauth tt

