/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.hint

/-!

# Intuitionistic tautology (`itauto`) decision procedure

The `itauto` tactic will prove any intuitionistic tautology. It implements the well known
`G4ip` algorithm: <http://www.cs.cmu.edu/~crary/317-f20/homeworks/g4ip.pdf>

## Tags

propositional logic, intuitionistic logic, decision procedure
-/

namespace tactic
namespace itauto

/-- Different propositional constructors that are variants of "and" for the purposes of the
theorem prover. -/
@[derive [has_reflect, decidable_eq]]
inductive and_kind | and | iff | eq

instance : inhabited and_kind := ⟨and_kind.and⟩

/-- A reified inductive type for propositional logic. -/
@[derive [has_reflect, decidable_eq]]
inductive prop : Type
| var : ℕ → prop            -- propositional atoms P_i
| true : prop               -- ⊤
| false : prop              -- ⊥
| and : and_kind → prop → prop → prop  -- p ∧ q, p ↔ q, p = q
| or : prop → prop → prop   -- p ∨ q
| imp : prop → prop → prop  -- p → q

instance : inhabited prop := ⟨prop.true⟩

/-- Given the contents of an `and` variant, return the two conjuncts. -/
def and_kind.sides : and_kind → prop → prop → prop × prop
| and_kind.and A B := (A, B)
| _ A B := (A.imp B, B.imp A)

/-- Debugging printer for propositions. -/
meta def prop.to_format : prop → format
| (prop.var i) := format!"v{i}"
| prop.true := format!"⊤"
| prop.false := format!"⊥"
| (prop.and and_kind.and p q) := format!"({p.to_format} ∧ {q.to_format})"
| (prop.and and_kind.iff p q) := format!"({p.to_format} ↔ {q.to_format})"
| (prop.and and_kind.eq p q) := format!"({p.to_format} = {q.to_format})"
| (prop.or p q) := format!"({p.to_format} ∨ {q.to_format})"
| (prop.imp p q) := format!"({p.to_format} → {q.to_format})"

meta instance : has_to_format prop := ⟨prop.to_format⟩

section
open ordering

/-- A comparator for `and_kind`. (There should really be a derive handler for this.) -/
def and_kind.cmp (p q : and_kind) : ordering :=
by { cases p; cases q, exacts [eq, lt, lt, gt, eq, lt, gt, gt, eq] }

/-- A comparator for propositions. (There should really be a derive handler for this.) -/
def prop.cmp (p q : prop) : ordering :=
begin
  induction p with _ ap _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ _ _ p₁ p₂ generalizing q; cases q,
  case var var { exact cmp p q },
  case true true { exact eq },
  case false false { exact eq },
  case and and : aq q₁ q₂ { exact (ap.cmp aq).or_else ((p₁ q₁).or_else (p₂ q₂)) },
  case or or : q₁ q₂ { exact (p₁ q₁).or_else (p₂ q₂) },
  case imp imp : q₁ q₂ { exact (p₁ q₁).or_else (p₂ q₂) },
  exacts [lt, lt, lt, lt, lt,
          gt, lt, lt, lt, lt,
          gt, gt, lt, lt, lt,
          gt, gt, gt, lt, lt,
          gt, gt, gt, gt, lt,
          gt, gt, gt, gt, gt]
end

instance : has_lt prop := ⟨λ p q, p.cmp q = lt⟩

instance : decidable_rel (@has_lt.lt prop _) := λ _ _, ordering.decidable_eq _ _

end

/-- A reified inductive proof type for intuitionistic propositional logic. -/
@[derive has_reflect]
inductive proof
-- (n: A) ⊢ A
| hyp (n : name) : proof
-- ⊢ ⊤
| triv : proof
-- (p: ⊥) ⊢ A
| exfalso' (A : prop) (p : proof) : proof
-- (p: (x: A) ⊢ B) ⊢ A → B
| intro (x : name) (A : prop) (p : proof) : proof
-- ak = and:  (p: A ∧ B) ⊢ A
-- ak = iff:  (p: A ↔ B) ⊢ A → B
-- ak = eq:  (p: A = B) ⊢ A → B
| and_left (ak : and_kind) (p : proof) : proof
-- ak = and:  (p: A ∧ B) ⊢ B
-- ak = iff:  (p: A ↔ B) ⊢ B → A
-- ak = eq:  (p: A = B) ⊢ B → A
| and_right (ak : and_kind) (p : proof) : proof
-- ak = and:  (p₁: A) (p₂: B) ⊢ A ∧ B
-- ak = iff:  (p₁: A → B) (p₁: B → A) ⊢ A ↔ B
-- ak = eq:  (p₁: A → B) (p₁: B → A) ⊢ A = B
| and_intro (ak : and_kind) (p₁ p₂ : proof) : proof
-- ak = and:  (p: A ∧ B → C) ⊢ A → B → C
-- ak = iff:  (p: (A ↔ B) → C) ⊢ (A → B) → (B → A) → C
-- ak = eq:  (p: (A = B) → C) ⊢ (A → B) → (B → A) → C
| curry (ak : and_kind) (A B : prop) (p : proof) : proof
-- This is a partial application of curry.
-- ak = and:  (p: A ∧ B → C) (q : A) ⊢ B → C
-- ak = iff:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C
-- ak = eq:  (p: (A ↔ B) → C) (q: A → B) ⊢ (B → A) → C
| curry₂ (ak : and_kind) (B : prop) (p q : proof) : proof
-- (p: A → B) (q: A) ⊢ B
| app' : proof → proof → proof
-- (p: A ∨ B → C) |- A → C
| or_imp_left (A B : prop) (p : proof) : proof
-- (p: A ∨ B → C) |- B → C
| or_imp_right (A B : prop) (p : proof) : proof
-- (p: A) |- A ∨ B
| or_inl (B : prop) (p : proof) : proof
-- (p: B) |- A ∨ B
| or_inr (A : prop) (p : proof) : proof
-- (p: B) |- A ∨ B
-- (p₁: A ∨ B) (p₂: (x: A) |- C) (p₃: (x: B) |- C) |- C
| or_elim (A B : prop) (p₁ : proof) (x : name) (p₂ p₃ : proof) : proof
-- The variable x here names the variable that will be used in the elaborated proof
-- (p: ((x:A) → B) → C) |- B → C
| imp_imp_simp (x : name) (A B : prop) (p : proof) : proof

instance : inhabited proof := ⟨proof.triv⟩

/-- Debugging printer for proof objects. -/
meta def proof.to_format : proof → format
| (proof.hyp i) := to_fmt i
| proof.triv := "triv"
| (proof.exfalso' _ p) := format!"(exfalso {p.to_format})"
| (proof.intro x A p) := format!"(λ ({x} : {A.to_format}), {p.to_format})"
| (proof.and_left _ p) := format!"{p.to_format} .1"
| (proof.and_right _ p) := format!"{p.to_format} .2"
| (proof.and_intro _ p q) := format!"⟨{p.to_format}, {q.to_format}⟩"
| (proof.curry _ _ _ p) := format!"(curry {p.to_format})"
| (proof.curry₂ _ _ p q) := format!"(curry {p.to_format} {q.to_format})"
| (proof.app' p q) := format!"({p.to_format} {q.to_format})"
| (proof.or_imp_left _ _ p) := format!"(or_imp_left {p.to_format})"
| (proof.or_imp_right _ _ p) := format!"(or_imp_right {p.to_format})"
| (proof.or_inl _ p) := format!"(or.inl {p.to_format})"
| (proof.or_inr _ p) := format!"(or.inr {p.to_format})"
| (proof.or_elim _ _ p x q r) :=
  format!"({p.to_format}.elim (λ {x}, {q.to_format}) (λ {x}, {r.to_format})"
| (proof.imp_imp_simp _ _ _ p) := format!"(imp_imp_simp {p.to_format})"

meta instance : has_to_format proof := ⟨proof.to_format⟩

/-- A variant on `proof.exfalso'` that performs opportunistic simplification. -/
meta def proof.exfalso : prop → proof → proof
| prop.false p := p
| A p := proof.exfalso' A p

/-- A variant on `proof.app'` that performs opportunistic simplification.
(This doesn't do full normalization because we don't want the proof size to blow up.) -/
meta def proof.app : proof → proof → proof
| (proof.curry ak _ B p) q := proof.curry₂ ak B p q
| (proof.curry₂ ak _ p q) r := p.app (q.and_intro ak r)
| (proof.or_imp_left _ B p) q := p.app (q.or_inl B)
| (proof.or_imp_right A _ p) q := p.app (q.or_inr A)
| (proof.imp_imp_simp x A _ p) q := p.app (proof.intro x A q)
| p q := p.app' q

/-- A typechecker for the `proof` type. This is not used by the tactic but can be used for
debugging. -/
meta def proof.check : name_map prop → proof → option prop
| Γ (proof.hyp i) := Γ.find i
| Γ proof.triv := some prop.true
| Γ (proof.exfalso' A p) := guard (p.check Γ = some prop.false) $> A
| Γ (proof.intro x A p) := do B ← p.check (Γ.insert x A), pure (prop.imp A B)
| Γ (proof.and_left ak p) := do
  prop.and ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).1
| Γ (proof.and_right ak p) := do
  prop.and ak' A B ← p.check Γ | none,
  guard (ak = ak') $> (ak.sides A B).2
| Γ (proof.and_intro and_kind.and p q) := do
  A ← p.check Γ, B ← q.check Γ,
  pure (A.and and_kind.and B)
| Γ (proof.and_intro ak p q) := do
  prop.imp A B ← p.check Γ | none,
  C ← q.check Γ, guard (C = prop.imp B A) $> (A.and ak B)
| Γ (proof.curry ak A' B' p) := do
  prop.imp (prop.and ak' A B) C ← p.check Γ | none,
  guard (ak = ak' ∧ ak.sides A B = (A', B')) $> (A'.imp $ B'.imp C)
| Γ (proof.curry₂ ak B' p q) := do
  prop.imp (prop.and ak' A B) C ← p.check Γ | none,
  A' ← q.check Γ, guard (ak = ak' ∧ ak.sides A B = (A', B')) $> (B'.imp C)
| Γ (proof.app' p q) := do prop.imp A B ← p.check Γ | none, A' ← q.check Γ, guard (A = A') $> B
| Γ (proof.or_imp_left A B p) := do
  prop.imp (prop.or A' B') C ← p.check Γ | none,
  guard (A = A' ∧ B = B') $> (A.imp C)
| Γ (proof.or_imp_right A B p) := do
  prop.imp (prop.or A' B') C ← p.check Γ | none,
  guard (A = A' ∧ B = B') $> (B.imp C)
| Γ (proof.or_inl B p) := do A ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_inr A p) := do B ← p.check Γ | none, pure (A.or B)
| Γ (proof.or_elim A' B' p x q r) := do
  prop.or A B ← p.check Γ | none,
  C ← q.check (Γ.insert x A),
  C' ← r.check (Γ.insert x B),
  guard (A = A' ∧ B = B' ∧ C = C') $> C
| Γ (proof.imp_imp_simp x A B p) := do
  prop.imp (prop.imp A' B') C ← p.check Γ | none,
  guard (A = A' ∧ B = B') $> (B.imp C)

/-- Get a new name in the pattern `h0, h1, h2, ...` -/
@[inline] meta def fresh_name {m} [monad m] : state_t ℕ m name :=
⟨λ n, pure (mk_simple_name ("h" ++ to_string n), n+1)⟩

/-- The context during proof search is a map from propositions to proof values. -/
meta def context := native.rb_map prop proof

/-- Debug printer for the context. -/
meta def context.to_format (Γ : context) : format :=
Γ.fold "" $ λ P p f, P.to_format ++ " := " ++ p.to_format ++ ",\n" ++ f

meta instance : has_to_format context := ⟨context.to_format⟩

/-- Insert a proposition and its proof into the context, as in `have : A := p`. This will eagerly
apply all level 1 rules on the spot, which are rules that don't split the goal and are validity
preserving: specifically, we drop `⊤` and `A → ⊤` hypotheses, close the goal if we find a `⊥`
hypothesis, split all conjunctions, and also simplify `⊥ → A` (drop), `⊤ → A` (simplify to `A`),
`A ∧ B → C` (curry to `A → B → C`) and `A ∨ B → C` (rewrite to `(A → C) ∧ (B → C)` and split). -/
meta def context.add : prop → proof → context → except (prop → proof) context
| prop.true p Γ := pure Γ
| prop.false p Γ := except.error (λ A, proof.exfalso A p)
| (prop.and ak A B) p Γ := do
  let (A, B) := ak.sides A B,
  Γ ← Γ.add A (p.and_left ak),
  Γ.add B (p.and_right ak)
| (prop.imp prop.false A) p Γ := pure Γ
| (prop.imp prop.true A) p Γ := Γ.add A (p.app proof.triv)
| (prop.imp (prop.and ak A B) C) p Γ :=
  let (A, B) := ak.sides A B in
  Γ.add (prop.imp A (B.imp C)) (p.curry ak A B)
| (prop.imp (prop.or A B) C) p Γ := do
  Γ ← Γ.add (A.imp C) (p.or_imp_left A B),
  Γ.add (B.imp C) (p.or_imp_right A B)
| (prop.imp A prop.true) p Γ := pure Γ
| A p Γ := pure (Γ.insert A p)

/-- Add `A` to the context `Γ` with proof `p`. This version of `context.add` takes a continuation
and a target proposition `B`, so that in the case that `⊥` is found we can skip the continuation
and just prove `B` outright. -/
@[inline] meta def context.with_add {m} [monad m] (Γ : context) (A : prop) (p : proof)
  (B : prop) (f : context → prop → m proof) : m proof :=
match Γ.add A p with
| except.ok Γ_A := f Γ_A B
| except.error p := pure (p B)
end

/-- The search phase, which deals with the level 3 rules, which are rules that are not validity
preserving and so require proof search. One obvious one is the or-introduction rule: we prove
`A ∨ B` by proving `A` or `B`, and we might have to try one and backtrack.

There are two rules dealing with implication in this category: `p, p -> C ⊢ B` where `p` is an
atom (which is safe if we can find it but often requires the right search to expose the `p`
assumption), and `(A₁ → A₂) → C ⊢ B`. We decompose the double implication into two subgoals: one to
prove `A₁ → A₂`, which can be written `A₂ → C, A₁ ⊢ A₂` (where we used `A₁` to simplify
`(A₁ → A₂) → C`), and one to use the consequent, `C ⊢ B`. The search here is that there are
potentially many implications to split like this, and we have to try all of them if we want to be
complete. -/
meta def search (prove : context → prop → state_t ℕ option proof) :
  prop → context → state_t ℕ option proof
| B Γ := match Γ.find B with
  | some p := pure p
  | none := match B with
    | prop.or B₁ B₂ := proof.or_inl B₂ <$> prove Γ B₁ <|> proof.or_inr B₁ <$> prove Γ B₂
    | _ := ⟨λ n, Γ.fold none $ λ A p r, r <|> match A with
      | prop.imp A' C := match Γ.find A' with
        | some q := (context.with_add (Γ.erase A) C (p.app q) B prove).1 n
        | none := match A' with
          | prop.imp A₁ A₂ :=
            (do {
              let Γ : context := Γ.erase A,
              a ← fresh_name,
              p₁ ← Γ.with_add A₁ (proof.hyp a) A₂ $ λ Γ_A₁ A₂,
                Γ_A₁.with_add (prop.imp A₂ C) (proof.imp_imp_simp a A₁ A₂ p) A₂ prove,
              Γ.with_add C (p.app (proof.intro a A₁ p₁)) B prove
            } : state_t ℕ option proof).1 n
          | _ := none
          end
        end
      | _ := none
      end⟩
    end
  end

/-- The main prover. This receives a context of proven or assumed lemmas and a target proposition,
and returns a proof or `none` (with state for the fresh variable generator).
The intuitionistic logic rules are separated into three groups:

* level 1: No splitting, validity preserving: apply whenever you can.
  Left rules in `context.add`, right rules in `prove`
* level 2: Splitting rules, validity preserving: apply after level 1 rules. Done in `prove`
* level 3: Splitting rules, not validity preserving: apply only if nothing else applies.
  Done in `search`

The level 1 rules on the right of the turnstile are `Γ ⊢ ⊤` and `Γ ⊢ A → B`, these are easy to
handle. The rule `Γ ⊢ A ∧ B` is a level 2 rule, also handled here. If none of these apply, we try
the level 2 rule `A ∨ B ⊢ C` by searching the context and splitting all ors we find. Finally, if
we don't make any more progress, we go to the search phase.
-/
meta def prove : context → prop → state_t ℕ option proof
| Γ prop.true := pure proof.triv
| Γ (prop.imp A B) := do
  a ← fresh_name,
  proof.intro a A <$> Γ.with_add A (proof.hyp a) B prove
| Γ (prop.and ak A B) := do
  let (A, B) := ak.sides A B,
  p ← prove Γ A,
  q ← prove Γ B,
  pure (p.and_intro ak q)
| Γ B := Γ.fold (search prove B) (λ A p IH Γ,
    match A with
    | prop.or A₁ A₂ := do
      let Γ : context := Γ.erase A,
      a ← fresh_name,
      p₁ ← Γ.with_add A₁ (proof.hyp a) B (λ Γ _, IH Γ),
      p₂ ← Γ.with_add A₂ (proof.hyp a) B (λ Γ _, IH Γ),
      pure (proof.or_elim A₁ A₂ p a p₁ p₂)
    | _ := IH Γ
    end) Γ

/-- Reifies an atomic or otherwise unrecognized proposition. If it is defeq to a proposition we
have already allocated, we reuse it, otherwise we name it with a new index. -/
meta def reify_atom (atoms : ref (buffer expr)) (e : expr) : tactic prop := do
  vec ← read_ref atoms,
  o ← try_core $ vec.iterate failure (λ i e' r,
    r <|> (is_def_eq e e' >> pure i.1)),
  match o with
  | none := write_ref atoms (vec.push_back e) $> prop.var vec.size
  | some i := pure $ prop.var i
  end

/-- Reify an `expr` into a `prop`, allocating anything non-propositional as an atom in the
`atoms` list. -/
meta def reify (atoms : ref (buffer expr)) : expr → tactic prop
| `(true) := pure prop.true
| `(false) := pure prop.false
| `(¬ %%a) := flip prop.imp prop.false <$> reify a
| `(%%a ∧ %%b) := prop.and and_kind.and <$> reify a <*> reify b
| `(%%a ∨ %%b) := prop.or <$> reify a <*> reify b
| `(%%a ↔ %%b) := prop.and and_kind.iff <$> reify a <*> reify b
| `(@eq Prop %%a %%b) := prop.and and_kind.eq <$> reify a <*> reify b
| `(@ne Prop %%a %%b) := do a ← reify a, b ← reify b, pure $ (a.and and_kind.eq b).imp prop.false
| e@`(%%a → %%b) :=
  if b.has_var then reify_atom atoms e else prop.imp <$> reify a <*> reify b
| e := reify_atom atoms e

/-- Once we have a proof object, we have to apply it to the goal. (Some of these cases are a bit
annoying because `applyc` gets the arguments wrong sometimes so we have to use `to_expr` instead.)
-/
meta def apply_proof : name_map expr → proof → tactic unit
| Γ (proof.hyp n) := do e ← Γ.find n, exact e
| Γ proof.triv := triv
| Γ (proof.exfalso' A p) := do
  t ← mk_mvar, to_expr ``(false.elim %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.intro x A p) := do e ← intro_core x, apply_proof (Γ.insert x e) p
| Γ (proof.and_left and_kind.and p) := do
  t ← mk_mvar, to_expr ``(and.left %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_left and_kind.iff p) := do
  t ← mk_mvar, to_expr ``(iff.mp %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_left and_kind.eq p) := do
  t ← mk_mvar, to_expr ``(cast %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.and p) := do
  t ← mk_mvar, to_expr ``(and.right %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.iff p) := do
  t ← mk_mvar, to_expr ``(iff.mpr %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_right and_kind.eq p) := do
  t ← mk_mvar, to_expr ``(cast (eq.symm %%t)) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.and_intro and_kind.and p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(and.intro %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.and_intro and_kind.iff p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(iff.intro %%t₁ %%t₂) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.and_intro and_kind.eq p q) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, to_expr ``(propext (iff.intro %%t₁ %%t₂)) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::gs), apply_proof Γ p >> apply_proof Γ q
| Γ (proof.curry ak A B p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (proof.curry₂ ak B p (proof.hyp n))
| Γ (proof.curry₂ ak B p q) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (q.and_intro ak (proof.hyp n)))
| Γ (proof.app' p q) := do
  A ← mk_meta_var (expr.sort level.zero),
  B ← mk_meta_var (expr.sort level.zero),
  g₁ ← mk_meta_var `((%%A : Prop) → (%%B : Prop)),
  g₂ ← mk_meta_var A,
  g :: gs ← get_goals,
  unify (g₁ g₂) g,
  set_goals (g₁::g₂::gs) >> apply_proof Γ p >> apply_proof Γ q
| Γ (proof.or_imp_left A B p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app $ (proof.hyp n).or_inl B)
| Γ (proof.or_imp_right A B p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app $ (proof.hyp n).or_inr A)
| Γ (proof.or_inl _ p) := do
  t ← mk_mvar, to_expr ``(or.inl %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.or_inr _ p) := do
  t ← mk_mvar, to_expr ``(or.inr %%t) tt ff >>= exact,
  gs ← get_goals, set_goals (t::gs), apply_proof Γ p
| Γ (proof.or_elim A B p x p₁ p₂) := do
  t₁ ← mk_mvar, t₂ ← mk_mvar, t₃ ← mk_mvar, to_expr ``(or.elim %%t₁ %%t₂ %%t₃) tt ff >>= exact,
  gs ← get_goals, set_goals (t₁::t₂::t₃::gs), apply_proof Γ p,
  e ← intro_core x, apply_proof (Γ.insert x e) p₁,
  e ← intro_core x, apply_proof (Γ.insert x e) p₂
| Γ (proof.imp_imp_simp x A B p) := do
  e ← intro_core `_, let n := e.local_uniq_name,
  apply_proof (Γ.insert n e) (p.app (proof.intro x A (proof.hyp n)))

end itauto

namespace interactive

open itauto

/-- A decision procedure for intuitionistic propositional logic. Unlike `finish` and `tauto!` this
tactic never uses the law of excluded middle, and the proof search is tailored for this use case.

```lean
example (p : Prop) : ¬ (p ↔ ¬ p) := by itauto
```
-/
meta def itauto : tactic unit :=
using_new_ref mk_buffer $ λ atoms,
using_new_ref mk_name_map $ λ hs, do
  t ← target,
  t ← mcond (is_prop t) (reify atoms t) (tactic.exfalso $> prop.false),
  hyps ← local_context,
  Γ ← hyps.mfoldl
    (λ (Γ : except (prop → proof) context) h, do
      e ← infer_type h,
      mcond (is_prop e)
        (do A ← reify atoms e,
          let n := h.local_pp_name,
          read_ref hs >>= λ Γ, write_ref hs (Γ.insert n h),
          pure (Γ >>= λ Γ', Γ'.add A (proof.hyp n)))
        (pure Γ))
    (except.ok (native.rb_map.mk _ _)),
  let o := state_t.run (match Γ with
  | except.ok Γ := prove Γ t
  | except.error p := pure (p t)
  end) 0,
  match o with
  | none := fail "itauto failed"
  | some (p, _) := do hs ← read_ref hs, apply_proof hs p
  end

add_hint_tactic "itauto"

add_tactic_doc
{ name       := "itauto",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.itauto],
  tags       := ["logic", "propositional logic", "intuitionistic logic", "decision procedure"] }

end interactive
end tactic
