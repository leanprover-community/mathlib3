/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.rel.lattice tactic.basic

/-!
# Closures of relations

## Main definitions

We define three closures of a relation `r : rel α α`:

* `refl_trans_gen` : reflexive transitive closure
* `refl_gen` : reflexive closure
* `trans_gen` : transitive closure

We also provide various constructors for these closures (e.g., `head`,
`tail`), different induction principles, and some lemmas converting,
e.g., from `refl_gen` to `refl_trans_gen`.
-/

universes u v

namespace rel

variables {α : Type u} {β : Type v} (r : rel α α) {a b c d : α}

/-- `refl_trans_gen r`: reflexive transitive closure of `r` -/
inductive refl_trans_gen (a : α) : α → Prop
| refl {} : refl_trans_gen a
| tail {b c} : refl_trans_gen b → r b c → refl_trans_gen c

attribute [refl] refl_trans_gen.refl

run_cmd tactic.mk_iff_of_inductive_prop `rel.refl_trans_gen `rel.refl_trans_gen.cases_tail_iff

/-- `refl_gen r`: reflexive closure of `r` -/
inductive refl_gen (a : α) : α → Prop
| refl {} : refl_gen a
| single {b} : r a b → refl_gen b

run_cmd tactic.mk_iff_of_inductive_prop `rel.refl_gen `rel.refl_gen_iff

attribute [refl] refl_gen.refl

/-- `trans_gen r`: transitive closure of `r` -/
inductive trans_gen (a : α) : α → Prop
| single {b} : r a b → trans_gen b
| tail {b c} : trans_gen b → r b c → trans_gen c

run_cmd tactic.mk_iff_of_inductive_prop `rel.trans_gen `rel.trans_gen_iff

variable {r}

lemma refl_gen.to_refl_trans_gen : ∀{a b}, refl_gen r a b → refl_trans_gen r a b
| a _ refl_gen.refl := by refl
| a b (refl_gen.single h) := refl_trans_gen.tail refl_trans_gen.refl h

namespace refl_trans_gen

@[trans] lemma trans (hab : refl_trans_gen r a b) (hbc : refl_trans_gen r b c) :
  refl_trans_gen r a c :=
begin
  induction hbc,
  case refl_trans_gen.refl { assumption },
  case refl_trans_gen.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma single (hab : r a b) : refl_trans_gen r a b :=
refl.tail hab

lemma head (hab : r a b) (hbc : refl_trans_gen r b c) : refl_trans_gen r a c :=
begin
  induction hbc,
  case refl_trans_gen.refl { exact refl.tail hab },
  case refl_trans_gen.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma cases_tail : refl_trans_gen r a b → b = a ∨ (∃c, refl_trans_gen r a c ∧ r c b) :=
(cases_tail_iff r a b).1

lemma head_induction_on
  {P : ∀(a:α), refl_trans_gen r a b → Prop}
  {a : α} (h : refl_trans_gen r a b)
  (refl : P b refl)
  (head : ∀{a c} (h' : r a c) (h : refl_trans_gen r c b), P c h → P a (h.head h')) :
  P a h :=
begin
  induction h generalizing P,
  case refl_trans_gen.refl { exact refl },
  case refl_trans_gen.tail : b c hab hbc ih {
    apply ih,
    show P b _, from head hbc _ refl,
    show ∀a a', r a a' → refl_trans_gen r a' b → P a' _ → P a _, from assume a a' hab hbc, head hab _
  }
end

lemma trans_induction_on
  {P : ∀{a b : α}, refl_trans_gen r a b → Prop}
  {a b : α} (h : refl_trans_gen r a b)
  (ih₁ : ∀a, @P a a refl)
  (ih₂ : ∀{a b} (h : r a b), P (single h))
  (ih₃ : ∀{a b c} (h₁ : refl_trans_gen r a b) (h₂ : refl_trans_gen r b c), P h₁ → P h₂ → P (h₁.trans h₂)) :
  P h :=
begin
  induction h,
  case refl_trans_gen.refl { exact ih₁ a },
  case refl_trans_gen.tail : b c hab hbc ih { exact ih₃ hab (single hbc) ih (ih₂ hbc) }
end

lemma cases_head (h : refl_trans_gen r a b) : a = b ∨ (∃c, r a c ∧ refl_trans_gen r c b) :=
begin
  induction h using rel.refl_trans_gen.head_induction_on,
  { left, refl },
  { right, existsi _, split; assumption }
end

lemma cases_head_iff : refl_trans_gen r a b ↔ a = b ∨ (∃c, r a c ∧ refl_trans_gen r c b) :=
begin
  split,
  { exact cases_head },
  { assume h,
    rcases h with rfl | ⟨c, hac, hcb⟩,
    { refl },
    { exact head hac hcb } }
end

lemma total_of_right_unique (U : r.right_unique)
  (ab : refl_trans_gen r a b) (ac : refl_trans_gen r a c) :
  refl_trans_gen r b c ∨ refl_trans_gen r c b :=
begin
  induction ab with b d ab bd IH,
  { exact or.inl ac },
  { rcases IH with IH | IH,
    { rcases cases_head IH with rfl | ⟨e, be, ec⟩,
      { exact or.inr (single bd) },
      { cases U bd be, exact or.inl ec } },
    { exact or.inr (IH.tail bd) } }
end

end refl_trans_gen

namespace trans_gen

lemma to_refl {a b} (h : trans_gen r a b) : refl_trans_gen r a b :=
begin
  induction h with b h b c _ bc ab,
  exact refl_trans_gen.single h,
  exact refl_trans_gen.tail ab bc
end

@[trans] lemma trans_left (hab : trans_gen r a b) (hbc : refl_trans_gen r b c) : trans_gen r a c :=
begin
  induction hbc,
  case refl_trans_gen.refl : c hab { assumption },
  case refl_trans_gen.tail : c d hbc hcd hac { exact hac.tail hcd }
end

@[trans] lemma trans (hab : trans_gen r a b) (hbc : trans_gen r b c) : trans_gen r a c :=
trans_left hab hbc.to_refl

lemma head' (hab : r a b) (hbc : refl_trans_gen r b c) : trans_gen r a c :=
trans_left (single hab) hbc

lemma tail' (hab : refl_trans_gen r a b) (hbc : r b c) : trans_gen r a c :=
begin
  induction hab generalizing c,
  case refl_trans_gen.refl : c hac { exact single hac },
  case refl_trans_gen.tail : d b hab hdb IH { exact tail (IH hdb) hbc }
end

@[trans] lemma trans_right (hab : refl_trans_gen r a b) (hbc : trans_gen r b c) : trans_gen r a c :=
begin
  induction hbc,
  case trans_gen.single : c hbc { exact tail' hab hbc },
  case trans_gen.tail : c d hbc hcd hac { exact hac.tail hcd }
end

lemma head (hab : r a b) (hbc : trans_gen r b c) : trans_gen r a c :=
head' hab hbc.to_refl

lemma tail'_iff : trans_gen r a c ↔ ∃ b, refl_trans_gen r a b ∧ r b c :=
begin
  refine ⟨λ h, _, λ ⟨b, hab, hbc⟩, tail' hab hbc⟩,
  cases h with _ hac b _ hab hbc,
  { exact ⟨_, by refl, hac⟩ },
  { exact ⟨_, hab.to_refl, hbc⟩ }
end

lemma head'_iff : trans_gen r a c ↔ ∃ b, r a b ∧ refl_trans_gen r b c :=
begin
  refine ⟨λ h, _, λ ⟨b, hab, hbc⟩, head' hab hbc⟩,
  induction h,
  case trans_gen.single : c hac { exact ⟨_, hac, by refl⟩ },
  case trans_gen.tail : b c hab hbc IH {
    rcases IH with ⟨d, had, hdb⟩, exact ⟨_, had, hdb.tail hbc⟩ }
end

end trans_gen

section refl_trans_gen
open refl_trans_gen

lemma refl_trans_gen_iff_eq (h : ∀b, ¬ r a b) : refl_trans_gen r a b ↔ b = a :=
by rw [cases_head_iff]; simp [h, eq_comm]

lemma refl_trans_gen_iff_eq_or_trans_gen :
  refl_trans_gen r a b ↔ b = a ∨ trans_gen r a b :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { cases h with c _ hac hcb,
    { exact or.inl rfl },
    { exact or.inr (trans_gen.tail' hac hcb) } },
  { rcases h with rfl | h, {refl}, {exact h.to_refl} }
end

lemma refl_trans_gen_lift {p : rel β β} (f : α → β)
  (h : (r ⟹ p).diag f) : ((refl_trans_gen r) ⟹  (refl_trans_gen p)).diag f :=
assume a b hab,
hab.trans_induction_on
  (assume a, refl)
  (assume a b h', refl_trans_gen.single $ h h')
  (assume a b c _ _, trans)

lemma refl_trans_gen_mono : monotone (@refl_trans_gen α) :=
λ r p h, refl_trans_gen_lift id h

lemma refl_trans_gen_eq_self (refl : reflexive r) (trans : transitive r) :
  refl_trans_gen r = r :=
funext $ λ a, funext $ λ b, propext $
⟨λ h, begin
  induction h with b c h₁ h₂ IH, {apply refl},
  exact trans IH h₂,
end, single⟩

lemma reflexive_refl_trans_gen : reflexive (refl_trans_gen r) :=
assume a, refl

lemma transitive_refl_trans_gen : transitive (refl_trans_gen r) :=
assume a b c, trans

lemma refl_trans_gen_idem :
  refl_trans_gen (refl_trans_gen r) = refl_trans_gen r :=
refl_trans_gen_eq_self reflexive_refl_trans_gen transitive_refl_trans_gen

lemma refl_trans_gen_lift' {p : rel β β} (f : α → β)
  (h : (r ⟹ (refl_trans_gen p)).diag f) : ((refl_trans_gen r) ⟹ (refl_trans_gen p)).diag f :=
λ a b hab, by simpa [refl_trans_gen_idem] using refl_trans_gen_lift f h hab

lemma refl_trans_gen_closed {p : rel α α} :
  (r ≤ refl_trans_gen p) → (refl_trans_gen r ≤ refl_trans_gen p) :=
refl_trans_gen_lift' id

end refl_trans_gen

/-- Two elements `x, y` are related by `r.join`, if there exists an element `z` such that
both `x` and `y` are related to `z` by `r`. -/
def join (r : rel α β) : rel α α := r.conv.comp r

section join
open refl_trans_gen refl_gen

lemma church_rosser
  (h : r.conv.join ≤ rel.comp (rel.conv $ refl_trans_gen r) (refl_gen r)) :
  (rel.conv (refl_trans_gen r)).join ≤ join (refl_trans_gen r) :=
begin
  rintros b c ⟨a, hac, hab⟩,
  induction hab,
  case refl_trans_gen.refl { exact ⟨c, refl, hac⟩ },
  case refl_trans_gen.tail : d e had hde ih {
    clear hac had a,
    rcases ih with ⟨b, hcb, hdb⟩,
    have : ∃a, refl_trans_gen r e a ∧ refl_gen r b a,
    { clear hcb, induction hdb,
      case refl_trans_gen.refl { exact ⟨e, refl, refl_gen.single hde⟩ },
      case refl_trans_gen.tail : f b hdf hfb ih {
        rcases ih with ⟨a, hea, hfa⟩,
        cases hfa with _ hfa,
        { exact ⟨b, hea.tail hfb, refl_gen.refl⟩ },
        { rcases h _ _ ⟨_, hfa, hfb⟩ with ⟨c, hac, hbc⟩,
          exact ⟨c, hea.trans hac, hbc⟩ } } },
    rcases this with ⟨a, hea, hba⟩, cases hba with _ hba,
    { exact ⟨b, hcb, hea⟩ },
    { exact ⟨a, hcb.tail hba, hea⟩ } }
end

lemma join_of_single (h : reflexive r) (hab : r a b) : join r a b :=
⟨b, h b, hab⟩

lemma symmetric_join : symmetric (join r) :=
assume a b ⟨c, hbc, hac⟩, ⟨c, hac, hbc⟩

lemma reflexive_join (h : reflexive r) : reflexive (join r) :=
assume a, ⟨a, h a, h a⟩

lemma transitive_join (ht : transitive r) (h : r.conv.join ≤ r.join) :
  transitive (join r) :=
assume a b c ⟨x, hbx, hax⟩ ⟨y, hcy, hby⟩,
let ⟨z, hyz, hxz⟩ := h x y ⟨b, hby, hbx⟩ in
⟨z, ht hcy hyz, ht hax hxz⟩

lemma equivalence_join (hr : reflexive r)  (ht : transitive r) (h : r.conv.join ≤ r.join) :
  equivalence (join r) :=
⟨reflexive_join hr, symmetric_join, transitive_join ht h⟩

lemma equivalence_join_refl_trans_gen
  (h : r.conv.join ≤ rel.comp (rel.conv $ refl_trans_gen r) (refl_gen r)) :
  equivalence (join (refl_trans_gen r)) :=
equivalence_join reflexive_refl_trans_gen transitive_refl_trans_gen (church_rosser h)

lemma join_of_transitive_symmetric {r' : rel α α} (ht : transitive r) (hs : symmetric r) :
  r' ≤ r → join r' ≤ r :=
assume h a b ⟨c, hbc, hac⟩, ht (h _ _ hac) (hs $ h _ _ hbc)

lemma join_of_equivalence {r' : rel α α} (hr : equivalence r) : r' ≤ r → join r' ≤ r :=
join_of_transitive_symmetric hr.2.2 hr.2.1

lemma refl_trans_gen_of_transitive_reflexive {r' : rel α α} (hr : reflexive r) (ht : transitive r) :
  r' ≤ r → refl_trans_gen r' ≤ r :=
begin
  intros h a b h',
  induction h' with b c hab hbc ih,
  { exact hr _ },
  { exact ht ih (h _ _ hbc) }
end

lemma refl_trans_gen_of_equivalence {r' : rel α α} (hr : equivalence r) :
  r' ≤ r → refl_trans_gen r' ≤ r :=
refl_trans_gen_of_transitive_reflexive hr.1 hr.2.2

end join

section eqv_gen

lemma eqv_gen_iff_of_equivalence (h : equivalence r) : eqv_gen r a b ↔ r a b :=
iff.intro
  begin
    assume h,
    induction h,
    case eqv_gen.rel { assumption },
    case eqv_gen.refl { exact h.1 _ },
    case eqv_gen.symm { apply h.2.1, assumption },
    case eqv_gen.trans : a b c _ _ hab hbc {  exact h.2.2 hab hbc }
  end
  (eqv_gen.rel a b)

lemma eqv_gen_mono : monotone (@eqv_gen α) :=
begin
  intros r p hrp a b h,
  induction h,
  case eqv_gen.rel : a b h { exact eqv_gen.rel _ _ (hrp _ _ h) },
  case eqv_gen.refl : { exact eqv_gen.refl _ },
  case eqv_gen.symm : a b h ih { exact eqv_gen.symm _ _ ih },
  case eqv_gen.trans : a b c ih1 ih2 hab hbc { exact eqv_gen.trans _ _ _ hab hbc }
end

end eqv_gen

end rel
