/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Resolution proofs.
-/

import tactic.vampire.cnf

universes u v

variable {α : Type u}

open list

namespace vampire

local notation `&`     := term.sym
local notation a `&` b := term.app a b
local notation a `#` k := term.vpp a k

inductive proof (m : mat) : cla → Type
| hyp (k : nat) : proof (m.nth k)
| res (t : term) (c d : cla) :
  proof ((ff, t) :: c) →
  proof ((tt, t) :: d) →
  proof (c ++ d)
| rot (k : nat) (c : cla) :
  proof c → proof (c.rot k)
| sub (μ : mappings) (c : cla) :
  proof c → proof (c.subst μ)
| con (l : lit) (c : cla) :
  proof (l :: l :: c) → proof (l :: c)

lemma fav_of_proof
  (M : model α) (m : mat) (h0 : m.fav M) :
  ∀ c : cla, proof m c → c.fav M :=
begin
  intros c π, induction π with
    k
    t c1 c2 π1 π2 h1 h2
    k d π h1
    μ d π h1
    l d π h1,
  { unfold mat.nth,
    cases h1 : list.nth m k;
    unfold option.get_or_else; intro v,
    { cases classical.em (lit.holds M v (tt, & 0)),
      { refine ⟨_, or.inr (or.inl rfl), h⟩ },
      refine ⟨_, or.inl rfl, h⟩ },
    apply h0,
    apply list.mem_iff_nth.elim_right,
    refine ⟨_, h1⟩ },
  { intro v,
    apply exists_mem_append.elim_right,
    rcases (h1 v) with ⟨s, hs1 | hs1, hs2⟩,
    { rcases (h2 v) with ⟨r, hr1 | hr1, hr2⟩,
      { subst hs1, subst hr1,
        cases hs2 hr2 },
      right, refine ⟨_, hr1, hr2⟩ },
    left, refine ⟨_, hs1, hs2⟩ },
  { intro v,
    rcases h1 v with ⟨t, ht1, ht2⟩,
    refine ⟨t, _, ht2⟩,
    apply mem_rot _ ht1 },
  { intro v,
    rw cla.holds_subst,
    apply h1 },
  intro v,
  rcases (h1 v) with ⟨t, h2 | h2 | h2, h3⟩;
  refine ⟨_, _, h3⟩,
  { left, exact h2 },
  { left, exact h2 },
  right, exact h2
end

lemma tas_of_proof [inhabited α] (p : form) :
  proof (cnf p.neg) [] → p.tas α :=
begin
  rintros h0 M,
  apply classical.by_contradiction,
  rw not_exists, intro h3,
  rcases (fav_of_proof M _ _ _ h0
    (vas.default α)) with ⟨_, ⟨_⟩, _⟩,
  intro v, apply holds_cnf_of_holds,
  rw form.holds_neg, apply h3,
end

end vampire
