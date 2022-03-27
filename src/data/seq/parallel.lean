/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Parallel computation of a computable sequence of computations by
a diagonal enumeration.
The important theorems of this operation are proven as
terminates_parallel and exists_of_mem_parallel.
(This operation is nondeterministic in the sense that it does not
honor sequence equivalence (irrelevance of computation time).)
-/
import data.seq.wseq
universes u v

namespace computation
open wseq
variables {α : Type u} {β : Type v}

def parallel.aux2 : list (computation α) → α ⊕ list (computation α) :=
list.foldr (λc o, match o with
| sum.inl a  := sum.inl a
| sum.inr ls := rmap (λ c', c' :: ls) (destruct c)
end) (sum.inr [])

def parallel.aux1 : list (computation α) × wseq (computation α) →
  α ⊕ list (computation α) × wseq (computation α)
| (l, S) := rmap (λ l', match seq.destruct S with
  | none := (l', nil)
  | some (none, S') := (l', S')
  | some (some c, S') := (c::l', S')
  end) (parallel.aux2 l)

/-- Parallel computation of an infinite stream of computations,
  taking the first result -/
def parallel (S : wseq (computation α)) : computation α :=
corec parallel.aux1 ([], S)

theorem terminates_parallel.aux : ∀ {l : list (computation α)} {S c},
  c ∈ l → terminates c → terminates (corec parallel.aux1 (l, S)) :=
begin
  have lem1 : ∀ l S, (∃ (a : α), parallel.aux2 l = sum.inl a) →
    terminates (corec parallel.aux1 (l, S)),
  { intros l S e, cases e with a e,
    have this : corec parallel.aux1 (l, S) = return a,
    { apply destruct_eq_ret, simp [parallel.aux1], rw e, simp [rmap] },
    rw this, apply_instance },
  intros l S c m T, revert l S,
  apply @terminates_rec_on _ _ c T _ _,
  { intros a l S m, apply lem1,
    induction l with c l IH generalizing m; simp at m, { contradiction },
    cases m with e m,
    { rw ←e, simp [parallel.aux2],
      cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a' ls,
      exacts [⟨a', rfl⟩, ⟨a, rfl⟩] },
    { cases IH m with a' e,
      simp [parallel.aux2], simp [parallel.aux2] at e,
      rw e, exact ⟨a', rfl⟩ } },
  { intros s IH l S m,
    have H1 : ∀ l', parallel.aux2 l = sum.inr l' → s ∈ l',
    { induction l with c l IH' generalizing m;
      intros l' e'; simp at m, { contradiction },
      cases m with e m; simp [parallel.aux2] at e',
      { rw ←e at e',
        cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a' ls;
        injection e' with e', rw ←e', simp },
      { induction e : list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a' ls;
        rw e at e', { contradiction },
        have := IH' m _ e,
        simp [parallel.aux2] at e',
        cases destruct c; injection e' with h',
        rw ←h', simp [this] } },
    induction h : parallel.aux2 l with a l',
    { exact lem1 _ _ ⟨a, h⟩ },
    { have H2 : corec parallel.aux1 (l, S) = think _,
      { apply destruct_eq_think,
        simp [parallel.aux1],
        rw h, simp [rmap] },
      rw H2, apply @computation.think_terminates _ _ _,
      have := H1 _ h,
      rcases seq.destruct S with _ | ⟨_|c, S'⟩;
      simp [parallel.aux1]; apply IH; simp [this] } }
end

theorem terminates_parallel {S : wseq (computation α)}
   {c} (h : c ∈ S) [T : terminates c] : terminates (parallel S) :=
suffices ∀ n (l : list (computation α)) S c,
  c ∈ l ∨ some (some c) = seq.nth S n →
  terminates c → terminates (corec parallel.aux1 (l, S)),
from let ⟨n, h⟩ := h in this n [] S c (or.inr h) T,
begin
  intro n, induction n with n IH; intros l S c o T,
  { cases o with a a, { exact terminates_parallel.aux a T },
    have H : seq.destruct S = some (some c, _),
    { unfold seq.destruct functor.map, rw ← a, simp },
    induction h : parallel.aux2 l with a l';
    have C : corec parallel.aux1 (l, S) = _,
    { apply destruct_eq_ret, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, resetI, apply_instance },
    { apply destruct_eq_think, simp [parallel.aux1], rw [h, H], simp [rmap] },
    { rw C, apply @computation.think_terminates _ _ _,
      apply terminates_parallel.aux _ T, simp } },
  { cases o with a a, { exact terminates_parallel.aux a T },
    induction h : parallel.aux2 l with a l';
    have C : corec parallel.aux1 (l, S) = _,
    { apply destruct_eq_ret, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, resetI, apply_instance },
    { apply destruct_eq_think, simp [parallel.aux1], rw [h], simp [rmap] },
    { rw C, apply @computation.think_terminates _ _ _,
      have TT : ∀ l', terminates (corec parallel.aux1 (l', S.tail)),
      { intro, apply IH _ _ _ (or.inr _) T, rw a, cases S with f al, refl },
      induction e : seq.nth S 0 with o,
      { have D : seq.destruct S = none,
        { dsimp [seq.destruct], rw e, refl },
        rw D, simp [parallel.aux1], have TT := TT l',
        rwa [seq.destruct_eq_nil D, seq.tail_nil] at TT },
      { have D : seq.destruct S = some (o, S.tail),
        { dsimp [seq.destruct], rw e, refl },
        rw D, cases o with c; simp [parallel.aux1, TT] } } }
end

theorem exists_of_mem_parallel {S : wseq (computation α)}
   {a} (h : a ∈ parallel S) : ∃ c ∈ S, a ∈ c :=
suffices ∀ C, a ∈ C → ∀ (l : list (computation α)) S,
  corec parallel.aux1 (l, S) = C → ∃ c, (c ∈ l ∨ c ∈ S) ∧ a ∈ c,
from let ⟨c, h1, h2⟩ := this _ h [] S rfl in ⟨c, h1.resolve_left id, h2⟩,
begin
  let F : list (computation α) → α ⊕ list (computation α) → Prop,
  { intros l a, cases a with a l',
    exact ∃ c ∈ l, a ∈ c,
    exact ∀ a', (∃ c ∈ l', a' ∈ c) → (∃ c ∈ l, a' ∈ c) },
  have lem1 : ∀ (l : list (computation α)), F l (parallel.aux2 l),
  { intro l, induction l with c l IH; simp [parallel.aux2],
    { intros a h, rcases h with ⟨c, hn, _⟩,
      exact false.elim hn },
    { simp [parallel.aux2] at IH,
      cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l with a ls;
      simp [parallel.aux2],
      { rcases IH with ⟨c', cl, ac⟩,
        refine ⟨c', or.inr cl, ac⟩ },
      { induction h : destruct c with a c'; simp [rmap],
        { refine ⟨c, list.mem_cons_self _ _, _⟩,
          rw destruct_eq_ret h,
          apply ret_mem },
        { intros a' h, rcases h with ⟨d, dm, ad⟩,
          simp at dm, cases dm with e dl,
          { rw e at ad, refine ⟨c, list.mem_cons_self _ _, _⟩,
            rw destruct_eq_think h,
            exact think_mem ad },
          { cases IH a' ⟨d, dl, ad⟩ with d dm, cases dm with dm ad,
            exact ⟨d, or.inr dm, ad⟩ } } } } },
  intros C aC, refine mem_rec_on aC _ (λ C' IH, _);
  intros l S e; have e' := congr_arg destruct e; have := lem1 l;
  simp [parallel.aux1] at e'; cases parallel.aux2 l with a' l'; injection e' with h',
  { rw h' at this, rcases this with ⟨c, cl, ac⟩,
    exact ⟨c, or.inl cl, ac⟩ },
  { induction e : seq.destruct S with a; rw e at h',
    { exact let ⟨d, o, ad⟩ := IH _ _ h',
        ⟨c, cl, ac⟩ := this a ⟨d, o.resolve_right (not_mem_nil _), ad⟩ in
      ⟨c, or.inl cl, ac⟩ },
    { cases a with o S', cases o with c; simp [parallel.aux1] at h';
      rcases IH _ _ h' with ⟨d, dl | dS', ad⟩,
      { exact let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩ },
      { refine ⟨d, or.inr _, ad⟩,
        rw seq.destruct_eq_cons e,
        exact seq.mem_cons_of_mem _ dS' },
      { simp at dl, cases dl with dc dl,
        { rw dc at ad, refine ⟨c, or.inr _, ad⟩,
          rw seq.destruct_eq_cons e,
          apply seq.mem_cons },
        { exact let ⟨c, cl, ac⟩ := this a ⟨d, dl, ad⟩ in ⟨c, or.inl cl, ac⟩ } },
      { refine ⟨d, or.inr _, ad⟩,
        rw seq.destruct_eq_cons e,
        exact seq.mem_cons_of_mem _ dS' } } }
end

theorem map_parallel (f : α → β) (S) : map f (parallel S) = parallel (S.map (map f)) :=
begin
  refine eq_of_bisim (λ c1 c2, ∃ l S,
    c1 = map f (corec parallel.aux1 (l, S)) ∧
    c2 = corec parallel.aux1 (l.map (map f), S.map (map f))) _ ⟨[], S, rfl, rfl⟩,
  intros c1 c2 h, exact match c1, c2, h with ._, ._, ⟨l, S, rfl, rfl⟩ := begin
    clear _match,
    have : parallel.aux2 (l.map (map f)) = lmap f (rmap (list.map (map f)) (parallel.aux2 l)),
    { simp [parallel.aux2],
      induction l with c l IH; simp, rw [IH],
      cases list.foldr parallel.aux2._match_1 (sum.inr list.nil) l; simp [parallel.aux2],
      cases destruct c; simp },
    simp [parallel.aux1], rw this, cases parallel.aux2 l with a l'; simp,
    apply S.cases_on _ (λ c S, _) (λ S, _); simp; simp [parallel.aux1];
    exact ⟨_, _, rfl, rfl⟩
  end end
end

theorem parallel_empty (S : wseq (computation α)) (h : S.head ~> none) :
parallel S = empty _ :=
eq_empty_of_not_terminates $ λ ⟨⟨a, m⟩⟩,
let ⟨c, cs, ac⟩ := exists_of_mem_parallel m,
    ⟨n, nm⟩ := exists_nth_of_mem cs,
    ⟨c', h'⟩ := head_some_of_nth_some nm in by injection h h'

-- The reason this isn't trivial from exists_of_mem_parallel is because it eliminates to Sort
def parallel_rec {S : wseq (computation α)} (C : α → Sort v)
  (H : ∀ s ∈ S, ∀ a ∈ s, C a) {a} (h : a ∈ parallel S) : C a :=
begin
  let T : wseq (computation (α × computation α)) :=
    S.map (λc, c.map (λ a, (a, c))),
  have : S = T.map (map (λ c, c.1)),
  { rw [←wseq.map_comp], refine (wseq.map_id _).symm.trans (congr_arg (λ f, wseq.map f S) _),
    funext c, dsimp [id, function.comp], rw [←map_comp], exact (map_id _).symm },
  have pe := congr_arg parallel this, rw ←map_parallel at pe,
  have h' := h, rw pe at h',
  haveI : terminates (parallel T) := (terminates_map_iff _ _).1 ⟨⟨_, h'⟩⟩,
  induction e : get (parallel T) with a' c,
  have : a ∈ c ∧ c ∈ S,
  { rcases exists_of_mem_map h' with ⟨d, dT, cd⟩,
    rw get_eq_of_mem _ dT at e, cases e, dsimp at cd, cases cd,
    rcases exists_of_mem_parallel dT with ⟨d', dT', ad'⟩,
    rcases wseq.exists_of_mem_map dT' with ⟨c', cs', e'⟩,
    rw ←e' at ad',
    rcases exists_of_mem_map ad' with ⟨a', ac', e'⟩, injection e' with i1 i2,
    constructor, rwa [i1, i2] at ac', rwa i2 at cs' },
  cases this with ac cs, apply H _ cs _ ac
end

theorem parallel_promises {S : wseq (computation α)} {a}
  (H : ∀ s ∈ S, s ~> a) : parallel S ~> a :=
λ a' ma', let ⟨c, cs, ac⟩ := exists_of_mem_parallel ma' in H _ cs ac

theorem mem_parallel {S : wseq (computation α)} {a}
  (H : ∀ s ∈ S, s ~> a) {c} (cs : c ∈ S) (ac : a ∈ c) : a ∈ parallel S :=
by haveI := terminates_of_mem ac; haveI := terminates_parallel cs;
   exact mem_of_promises _ (parallel_promises H)

theorem parallel_congr_lem {S T : wseq (computation α)} {a}
  (H : S.lift_rel equiv T) : (∀ s ∈ S, s ~> a) ↔ (∀ t ∈ T, t ~> a) :=
⟨λ h1 t tT, let ⟨s, sS, se⟩ := wseq.exists_of_lift_rel_right H tT in
  (promises_congr se _).1 (h1 _ sS),
λ h2 s sS, let ⟨t, tT, se⟩ := wseq.exists_of_lift_rel_left H sS in
  (promises_congr se _).2 (h2 _ tT)⟩

-- The parallel operation is only deterministic when all computation paths lead to the same value
theorem parallel_congr_left {S T : wseq (computation α)} {a}
  (h1 : ∀ s ∈ S, s ~> a) (H : S.lift_rel equiv T) : parallel S ~ parallel T :=
let h2 := (parallel_congr_lem H).1 h1 in
λ a', ⟨λh, by have aa := parallel_promises h1 h; rw ←aa; rw ←aa at h; exact
  let ⟨s, sS, as⟩ := exists_of_mem_parallel h,
      ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_left H sS,
      aT := (st _).1 as in mem_parallel h2 tT aT,
λh, by have aa := parallel_promises h2 h; rw ←aa; rw ←aa at h; exact
  let ⟨s, sS, as⟩ := exists_of_mem_parallel h,
      ⟨t, tT, st⟩ := wseq.exists_of_lift_rel_right H sS,
      aT := (st _).2 as in mem_parallel h1 tT aT⟩

theorem parallel_congr_right {S T : wseq (computation α)} {a}
  (h2 : ∀ t ∈ T, t ~> a) (H : S.lift_rel equiv T) : parallel S ~ parallel T :=
parallel_congr_left ((parallel_congr_lem H).2 h2) H

end computation
