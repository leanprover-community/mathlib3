/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

More partial recursive functions using a universal program;
Rice's theorem and the halting problem.
-/
import data.computability.partrec_code

open encodable denumerable

namespace nat.partrec
open computable roption

theorem merge' {f g}
  (hf : nat.partrec f) (hg : nat.partrec g) :
  ∃ h, nat.partrec h ∧ ∀ a,
    (∀ x ∈ h a, x ∈ f a ∨ x ∈ g a) ∧
    ((h a).dom ↔ (f a).dom ∨ (g a).dom) :=
begin
  rcases code.exists_code.1 hf with ⟨cf, rfl⟩,
  rcases code.exists_code.1 hg with ⟨cg, rfl⟩,
  have : nat.partrec (λ n,
    (nat.rfind_opt (λ k, cf.evaln k n <|> cg.evaln k n))) :=
  partrec.nat_iff.1 (partrec.rfind_opt $
    primrec.option_orelse.to_comp.comp
      (code.evaln_prim.to_comp.comp $ (snd.pair (const cf)).pair fst)
      (code.evaln_prim.to_comp.comp $ (snd.pair (const cg)).pair fst)),
  refine ⟨_, this, λ n, _⟩,
  suffices, refine ⟨this,
    ⟨λ h, (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, _⟩⟩,
  { intro h, rw nat.rfind_opt_dom,
    simp [dom_iff_mem, code.evaln_complete] at h,
    rcases h with ⟨x, k, e⟩ | ⟨x, k, e⟩,
    { refine ⟨k, x, _⟩, simp [e] },
    { refine ⟨k, _⟩,
      cases cf.evaln k n with y,
      { exact ⟨x, by simp [e]⟩ },
      { exact ⟨y, by simp⟩ } } },
  { intros x h,
    rcases nat.rfind_opt_spec h with ⟨k, e⟩,
    revert e,
    simp; cases e' : cf.evaln k n with y; simp; intro,
    { exact or.inr (code.evaln_sound e) },
    { subst y,
        exact or.inl (code.evaln_sound e') } }
end

end nat.partrec

namespace partrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

open computable roption nat.partrec (code) nat.partrec.code

theorem merge' {f g : α →. σ}
  (hf : partrec f) (hg : partrec g) :
  ∃ k : α →. σ, partrec k ∧ ∀ a,
    (∀ x ∈ k a, x ∈ f a ∨ x ∈ g a) ∧
    ((k a).dom ↔ (f a).dom ∨ (g a).dom) :=
let ⟨k, hk, H⟩ :=
  nat.partrec.merge' (bind_decode2_iff.1 hf) (bind_decode2_iff.1 hg) in
begin
  let k' := λ a, (k (encode a)).bind (λ n, decode σ n),
  refine ⟨k', ((nat_iff.2 hk).comp computable.encode).bind
    (computable.decode.of_option.comp snd).to₂, λ a, _⟩,
  suffices, refine ⟨this,
    ⟨λ h, (this _ ⟨h, rfl⟩).imp Exists.fst Exists.fst, _⟩⟩,
  { intro h, simp [k'],
    have hk : (k (encode a)).dom :=
      (H _).2.2 (by simpa [encodek2] using h),
    existsi hk,
    cases (H _).1 _ ⟨hk, rfl⟩ with h h;
    { simp at h,
      rcases h with ⟨a', ha', y, hy, e⟩,
      simp [e.symm, encodek] } },
  { intros x h', simp [k'] at h',
    rcases h' with ⟨n, hn, hx⟩,
    have := (H _).1 _ hn, simp [mem_decode2] at this,
    cases this with h h;
    { rcases h with ⟨a', ⟨ha₁, ha₂⟩, y, hy, rfl⟩,
      rw encodek at hx ha₁, simp at hx ha₁, substs y a',
      simp [hy] } },
end

theorem merge {f g : α →. σ}
  (hf : partrec f) (hg : partrec g)
  (H : ∀ a (x ∈ f a) (y ∈ g a), x = y) :
  ∃ k : α →. σ, partrec k ∧ ∀ a x, x ∈ k a ↔ x ∈ f a ∨ x ∈ g a :=
let ⟨k, hk, K⟩ := merge' hf hg in
⟨k, hk, λ a x, ⟨(K _).1 _, λ h, begin
  have : (k a).dom := (K _).2.2 (h.imp Exists.fst Exists.fst),
  refine ⟨this, _⟩,
  cases h with h h; cases (K _).1 _ ⟨this, rfl⟩ with h' h',
  { exact mem_unique h' h },
  { exact (H _ _ h _ h').symm },
  { exact H _ _ h' _ h },
  { exact mem_unique h' h }
end⟩⟩

theorem cond {c : α → bool} {f : α →. σ} {g : α →. σ}
  (hc : computable c) (hf : partrec f) (hg : partrec g) :
  partrec (λ a, cond (c a) (f a) (g a)) :=
let ⟨cf, ef⟩ := exists_code.1 hf,
    ⟨cg, eg⟩ := exists_code.1 hg in
((eval_part.comp
    (computable.cond hc (const cf) (const cg)) computable.id).bind
  ((@computable.decode σ _).comp snd).of_option.to₂).of_eq $
λ a, by cases c a; simp [ef, eg, encodek]

theorem sum_cases
  {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ →. σ}
  (hf : computable f) (hg : partrec₂ g) (hh : partrec₂ h) :
  @partrec _ σ _ _ (λ a, sum.cases_on (f a) (g a) (h a)) :=
option_some_iff.1 $ (cond
  (sum_cases hf (const tt).to₂ (const ff).to₂)
  (sum_cases_left hf (option_some_iff.2 hg).to₂ (const option.none).to₂)
  (sum_cases_right hf (const option.none).to₂ (option_some_iff.2 hh).to₂))
.of_eq $ λ a, by cases f a; simp

end partrec

def computable_pred {α} [primcodable α] (p : α → Prop) :=
∃ [D : decidable_pred p],
by exactI computable (λ a, to_bool (p a))

/- recursively enumerable predicate -/
def re_pred {α} [primcodable α] (p : α → Prop) :=
partrec (λ a, roption.assert (p a) (λ _, roption.some ()))

theorem computable_pred.of_eq {α} [primcodable α]
  {p q : α → Prop}
  (hp : computable_pred p) (H : ∀ a, p a ↔ q a) : computable_pred q :=
(funext (λ a, propext (H a)) : p = q) ▸ hp

namespace computable_pred
variables {α : Type*} {σ : Type*}
variables [primcodable α] [primcodable σ]
open nat.partrec (code) nat.partrec.code computable

theorem rice (C : set (ℕ →. ℕ))
  (h : computable_pred (λ c, eval c ∈ C))
  {f g} (hf : nat.partrec f) (hg : nat.partrec g)
  (fC : f ∈ C) : g ∈ C :=
begin
  cases h with _ h, resetI,
  rcases fixed_point₂ (partrec.cond (h.comp fst)
    ((partrec.nat_iff.2 hg).comp snd).to₂
    ((partrec.nat_iff.2 hf).comp snd).to₂).to₂ with ⟨c, e⟩,
  simp at e,
  by_cases eval c ∈ C,
  { simp [h] at e, rwa ← e },
  { simp at h, simp [h] at e,
    rw e at h, contradiction }
end

theorem rice₂ (C : set code)
  (H : ∀ cf cg, eval cf = eval cg → (cf ∈ C ↔ cg ∈ C)) :
  computable_pred (λ c, c ∈ C) ↔ C = ∅ ∨ C = set.univ :=
by haveI := classical.dec; exact
have hC : ∀ f, f ∈ C ↔ eval f ∈ eval '' C,
from λ f, ⟨set.mem_image_of_mem _, λ ⟨g, hg, e⟩, (H _ _ e).1 hg⟩,
⟨λ h, or_iff_not_imp_left.2 $ λ C0,
  set.eq_univ_of_forall $ λ cg,
  let ⟨cf, fC⟩ := set.ne_empty_iff_exists_mem.1 C0 in
  (hC _).2 $ rice (eval '' C) (h.of_eq hC)
    (partrec.nat_iff.1 $ eval_part.comp (const cf) computable.id)
    (partrec.nat_iff.1 $ eval_part.comp (const cg) computable.id)
    ((hC _).1 fC),
λ h, by rcases h with rfl | rfl; simp [computable_pred];
  exact ⟨by apply_instance, computable.const _⟩⟩

theorem halting_problem (n) : ¬ computable_pred (λ c, (eval c n).dom)
| h := rice {f | (f n).dom} h nat.partrec.zero nat.partrec.none trivial

end computable_pred
