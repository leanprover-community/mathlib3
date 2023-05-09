/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import computability.primrec
import data.nat.psub
import data.pfun

/-!
# The partial recursive functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `part` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

open encodable denumerable part

local attribute [-simp] not_forall

namespace nat

section rfind
parameter (p : ℕ →. bool)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ff ∈ p k

parameter (H : ∃ n, tt ∈ p n ∧ ∀ k < n, (p k).dom)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in begin
  suffices : ∀m k, n ≤ k + m → acc (lbp p) k,
  { from λ a, this _ _ (nat.le_add_left _ _) },
  intros m k kn,
  induction m with m IH generalizing k;
    refine ⟨_, λ y r, _⟩; rcases r with ⟨rfl, a⟩,
  { injection mem_unique pn.1 (a _ kn) },
  { exact IH _ (by rw nat.add_right_comm; exact kn) }
end⟩

def rfind_x : {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m} :=
suffices ∀ k, (∀n < k, ff ∈ p n) → {n // tt ∈ p n ∧ ∀m < n, ff ∈ p m},
from this 0 (λ n, (nat.not_lt_zero _).elim),
@well_founded.fix _ _ lbp wf_lbp begin
  intros m IH al,
  have pm : (p m).dom,
  { rcases H with ⟨n, h₁, h₂⟩,
    rcases lt_trichotomy m n with h₃|h₃|h₃,
    { exact h₂ _ h₃ },
    { rw h₃, exact h₁.fst },
    { injection mem_unique h₁ (al _ h₃) } },
  cases e : (p m).get pm,
  { suffices,
    exact IH _ ⟨rfl, this⟩ (λ n h, this _ (le_of_lt_succ h)),
    intros n h, cases h.lt_or_eq_dec with h h,
    { exact al _ h },
    { rw h, exact ⟨_, e⟩ } },
  { exact ⟨m, ⟨_, e⟩, al⟩ }
end

end rfind

def rfind (p : ℕ →. bool) : part ℕ :=
⟨_, λ h, (rfind_x p h).1⟩

theorem rfind_spec {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) : tt ∈ p n :=
h.snd ▸ (rfind_x p h.fst).2.1

theorem rfind_min {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) :
  ∀ {m : ℕ}, m < n → ff ∈ p m :=
h.snd ▸ (rfind_x p h.fst).2.2

@[simp] theorem rfind_dom {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).dom :=
iff.rfl

theorem rfind_dom' {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).dom :=
exists_congr $ λ n, and_congr_right $ λ pn,
⟨λ H m h, (decidable.eq_or_lt_of_le h).elim (λ e, e.symm ▸ pn.fst) (H _),
 λ H m h, H (le_of_lt h)⟩

@[simp] theorem mem_rfind {p : ℕ →. bool} {n : ℕ} :
  n ∈ rfind p ↔ tt ∈ p n ∧ ∀ {m : ℕ}, m < n → ff ∈ p m :=
⟨λ h, ⟨rfind_spec h, @rfind_min _ _ h⟩,
  λ ⟨h₁, h₂⟩, let ⟨m, hm⟩ := dom_iff_mem.1 $
    (@rfind_dom p).2 ⟨_, h₁, λ m mn, (h₂ mn).fst⟩ in
  begin
    rcases lt_trichotomy m n with h|h|h,
    { injection mem_unique (h₂ h) (rfind_spec hm) },
    { rwa ← h },
    { injection mem_unique h₁ (rfind_min hm h) },
  end⟩

theorem rfind_min' {p : ℕ → bool} {m : ℕ} (pm : p m) :
  ∃ n ∈ rfind p, n ≤ m :=
have tt ∈ (p : ℕ →. bool) m, from ⟨trivial, pm⟩,
let ⟨n, hn⟩ := dom_iff_mem.1 $
  (@rfind_dom p).2 ⟨m, this, λ k h, ⟨⟩⟩ in
⟨n, hn, not_lt.1 $ λ h,
  by injection mem_unique this (rfind_min hn h)⟩

theorem rfind_zero_none
  (p : ℕ →. bool) (p0 : p 0 = none) : rfind p = none :=
eq_none_iff.2 $ λ a h,
let ⟨n, h₁, h₂⟩ := rfind_dom'.1 h.fst in
(p0 ▸ h₂ (zero_le _) : (@part.none bool).dom)

def rfind_opt {α} (f : ℕ → option α) : part α :=
(rfind (λ n, (f n).is_some)).bind (λ n, f n)

theorem rfind_opt_spec {α} {f : ℕ → option α} {a}
 (h : a ∈ rfind_opt f) : ∃ n, a ∈ f n :=
let ⟨n, h₁, h₂⟩ := mem_bind_iff.1 h in ⟨n, mem_coe.1 h₂⟩

theorem rfind_opt_dom {α} {f : ℕ → option α} :
  (rfind_opt f).dom ↔ ∃ n a, a ∈ f n :=
⟨λ h, (rfind_opt_spec ⟨h, rfl⟩).imp (λ n h, ⟨_, h⟩),
 λ h, begin
  have h' : ∃ n, (f n).is_some :=
    h.imp (λ n, option.is_some_iff_exists.2),
  have s := nat.find_spec h',
  have fd : (rfind (λ n, (f n).is_some)).dom :=
    ⟨nat.find h', by simpa using s.symm, λ _ _, trivial⟩,
  refine ⟨fd, _⟩,
  have := rfind_spec (get_mem fd),
  simp at this ⊢,
  cases option.is_some_iff_exists.1 this.symm with a e,
  rw e, trivial
end⟩

theorem rfind_opt_mono {α} {f : ℕ → option α}
  (H : ∀ {a m n}, m ≤ n → a ∈ f m → a ∈ f n)
  {a} : a ∈ rfind_opt f ↔ ∃ n, a ∈ f n :=
⟨rfind_opt_spec, λ ⟨n, h⟩, begin
  have h' := rfind_opt_dom.2 ⟨_, _, h⟩,
  cases rfind_opt_spec ⟨h', rfl⟩ with k hk,
  have := (H (le_max_left _ _) h).symm.trans
          (H (le_max_right _ _) hk),
  simp at this, simp [this, get_mem]
end⟩

inductive partrec : (ℕ →. ℕ) → Prop
| zero : partrec (pure 0)
| succ : partrec succ
| left : partrec ↑(λ n : ℕ, n.unpair.1)
| right : partrec ↑(λ n : ℕ, n.unpair.2)
| pair {f g} : partrec f → partrec g → partrec (λ n, mkpair <$> f n <*> g n)
| comp {f g} : partrec f → partrec g → partrec (λ n, g n >>= f)
| prec {f g} : partrec f → partrec g → partrec (unpaired (λ a n,
    n.elim (f a) (λ y IH, do i ← IH, g (mkpair a (mkpair y i)))))
| rfind {f} : partrec f → partrec (λ a,
    rfind (λ n, (λ m, m = 0) <$> f (mkpair a n)))

namespace partrec

theorem of_eq {f g : ℕ →. ℕ} (hf : partrec f) (H : ∀ n, f n = g n) : partrec g :=
(funext H : f = g) ▸ hf

theorem of_eq_tot {f : ℕ →. ℕ} {g : ℕ → ℕ}
  (hf : partrec f) (H : ∀ n, g n ∈ f n) : partrec g :=
hf.of_eq (λ n, eq_some_iff.2 (H n))

theorem of_primrec {f : ℕ → ℕ} (hf : primrec f) : partrec f :=
begin
  induction hf,
  case nat.primrec.zero { exact zero },
  case nat.primrec.succ { exact succ },
  case nat.primrec.left { exact left },
  case nat.primrec.right { exact right },
  case nat.primrec.pair : f g hf hg pf pg
  { refine (pf.pair pg).of_eq_tot (λ n, _),
    simp [has_seq.seq] },
  case nat.primrec.comp : f g hf hg pf pg
  { refine (pf.comp pg).of_eq_tot (λ n, _),
    simp },
  case nat.primrec.prec : f g hf hg pf pg
  { refine (pf.prec pg).of_eq_tot (λ n, _),
    simp,
    induction n.unpair.2 with m IH, {simp},
    simp, exact ⟨_, IH, rfl⟩ },
end

protected theorem some : partrec some := of_primrec primrec.id

theorem none : partrec (λ n, none) :=
(of_primrec (nat.primrec.const 1)).rfind.of_eq $
λ n, eq_none_iff.2 $ λ a ⟨h, e⟩, by simpa using h

theorem prec' {f g h}
  (hf : partrec f) (hg : partrec g) (hh : partrec h) :
  partrec (λ a, (f a).bind (λ n, n.elim (g a)
    (λ y IH, do i ← IH, h (mkpair a (mkpair y i))))) :=
((prec hg hh).comp (pair partrec.some hf)).of_eq $
λ a, ext $ λ s, by simp [(<*>)]; exact
⟨λ ⟨n, h₁, h₂⟩, ⟨_, ⟨_, h₁, rfl⟩, by simpa using h₂⟩,
 λ ⟨_, ⟨n, h₁, rfl⟩, h₂⟩, ⟨_, h₁, by simpa using h₂⟩⟩

theorem ppred : partrec (λ n, ppred n) :=
have primrec₂ (λ n m, if n = nat.succ m then 0 else 1),
from (primrec.ite
  (@@primrec_rel.comp _ _ _ _ _ _ _ primrec.eq
    primrec.fst
    (_root_.primrec.succ.comp primrec.snd))
  (_root_.primrec.const 0) (_root_.primrec.const 1)).to₂,
(of_primrec (primrec₂.unpaired'.2 this)).rfind.of_eq $
λ n, begin
  cases n; simp,
  { exact eq_none_iff.2 (λ a ⟨⟨m, h, _⟩, _⟩,
      by simpa [show 0 ≠ m.succ, by intro h; injection h] using h) },
  { refine eq_some_iff.2 _,
    simp, intros m h, simp [ne_of_gt h] }
end

end partrec

end nat

def partrec {α σ} [primcodable α] [primcodable σ]
  (f : α →. σ) := nat.partrec (λ n,
  part.bind (decode α n) (λ a, (f a).map encode))

def partrec₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (f : α → β →. σ) := partrec (λ p : α × β, f p.1 p.2)

def computable {α σ} [primcodable α] [primcodable σ] (f : α → σ) := partrec (f : α →. σ)

def computable₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (f : α → β → σ) := computable (λ p : α × β, f p.1 p.2)

theorem primrec.to_comp {α σ} [primcodable α] [primcodable σ]
  {f : α → σ} (hf : primrec f) : computable f :=
(nat.partrec.ppred.comp (nat.partrec.of_primrec hf)).of_eq $
λ n, by simp; cases decode α n; simp

theorem primrec₂.to_comp {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  {f : α → β → σ} (hf : primrec₂ f) : computable₂ f := hf.to_comp

protected theorem computable.partrec {α σ} [primcodable α] [primcodable σ]
  {f : α → σ} (hf : computable f) : partrec (f : α →. σ) := hf

protected theorem computable₂.partrec₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  {f : α → β → σ} (hf : computable₂ f) : partrec₂ (λ a, (f a : β →. σ)) := hf

namespace computable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem of_eq {f g : α → σ} (hf : computable f) (H : ∀ n, f n = g n) : computable g :=
(funext H : f = g) ▸ hf

theorem const (s : σ) : computable (λ a : α, s) :=
(primrec.const _).to_comp

theorem of_option {f : α → option β} (hf : computable f) :
  partrec (λ a, (f a : part β)) :=
(nat.partrec.ppred.comp hf).of_eq $ λ n, begin
  cases decode α n with a; simp,
  cases f a with b; simp
end

theorem to₂ {f : α × β → σ} (hf : computable f) : computable₂ (λ a b, f (a, b)) :=
hf.of_eq $ λ ⟨a, b⟩, rfl

protected theorem id : computable (@id α) := primrec.id.to_comp

theorem fst : computable (@prod.fst α β) := primrec.fst.to_comp

theorem snd : computable (@prod.snd α β) := primrec.snd.to_comp

theorem pair {f : α → β} {g : α → γ}
  (hf : computable f) (hg : computable g) : computable (λ a, (f a, g a)) :=
(hf.pair hg).of_eq $
λ n, by cases decode α n; simp [(<*>)]

theorem unpair : computable nat.unpair := primrec.unpair.to_comp

theorem succ : computable nat.succ := primrec.succ.to_comp
theorem pred : computable nat.pred := primrec.pred.to_comp
theorem nat_bodd : computable nat.bodd := primrec.nat_bodd.to_comp
theorem nat_div2 : computable nat.div2 := primrec.nat_div2.to_comp

theorem sum_inl : computable (@sum.inl α β) := primrec.sum_inl.to_comp
theorem sum_inr : computable (@sum.inr α β) := primrec.sum_inr.to_comp

theorem list_cons : computable₂ (@list.cons α) := primrec.list_cons.to_comp
theorem list_reverse : computable (@list.reverse α) := primrec.list_reverse.to_comp
theorem list_nth : computable₂ (@list.nth α) := primrec.list_nth.to_comp
theorem list_append : computable₂ ((++) : list α → list α → list α) := primrec.list_append.to_comp
theorem list_concat : computable₂ (λ l (a:α), l ++ [a]) := primrec.list_concat.to_comp
theorem list_length : computable (@list.length α) := primrec.list_length.to_comp

theorem vector_cons {n} : computable₂ (@vector.cons α n) := primrec.vector_cons.to_comp
theorem vector_to_list {n} : computable (@vector.to_list α n) := primrec.vector_to_list.to_comp
theorem vector_length {n} : computable (@vector.length α n) := primrec.vector_length.to_comp
theorem vector_head {n} : computable (@vector.head α n) := primrec.vector_head.to_comp
theorem vector_tail {n} : computable (@vector.tail α n) := primrec.vector_tail.to_comp
theorem vector_nth {n} : computable₂ (@vector.nth α n) := primrec.vector_nth.to_comp
theorem vector_nth' {n} : computable (@vector.nth α n) := primrec.vector_nth'.to_comp
theorem vector_of_fn' {n} : computable (@vector.of_fn α n) := primrec.vector_of_fn'.to_comp

theorem fin_app {n} : computable₂ (@id (fin n → σ)) := primrec.fin_app.to_comp

protected theorem encode : computable (@encode α _) :=
primrec.encode.to_comp

protected theorem decode : computable (decode α) :=
primrec.decode.to_comp

protected theorem of_nat (α) [denumerable α] : computable (of_nat α) :=
(primrec.of_nat _).to_comp

theorem encode_iff {f : α → σ} : computable (λ a, encode (f a)) ↔ computable f :=
iff.rfl

theorem option_some : computable (@option.some α) :=
primrec.option_some.to_comp

end computable

namespace partrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

open computable

theorem of_eq {f g : α →. σ} (hf : partrec f) (H : ∀ n, f n = g n) : partrec g :=
(funext H : f = g) ▸ hf

theorem of_eq_tot {f : α →. σ} {g : α → σ}
  (hf : partrec f) (H : ∀ n, g n ∈ f n) : computable g :=
hf.of_eq (λ a, eq_some_iff.2 (H a))

theorem none : partrec (λ a : α, @part.none σ) :=
nat.partrec.none.of_eq $ λ n, by cases decode α n; simp

protected theorem some : partrec (@part.some α) := computable.id

theorem _root_.decidable.partrec.const' (s : part σ) [decidable s.dom] : partrec (λ a : α, s) :=
(of_option (const (to_option s))).of_eq (λ a, of_to_option s)

theorem const' (s : part σ) : partrec (λ a : α, s) :=
by haveI := classical.dec s.dom; exact decidable.partrec.const' s

protected theorem bind {f : α →. β} {g : α → β →. σ}
  (hf : partrec f) (hg : partrec₂ g) : partrec (λ a, (f a).bind (g a)) :=
(hg.comp (nat.partrec.some.pair hf)).of_eq $
λ n, by simp [(<*>)]; cases e : decode α n with a;
  simp [e, encodek]

theorem map {f : α →. β} {g : α → β → σ}
  (hf : partrec f) (hg : computable₂ g) : partrec (λ a, (f a).map (g a)) :=
by simpa [bind_some_eq_map] using
   @@partrec.bind _ _ _ (λ a b, part.some (g a b)) hf hg

theorem to₂ {f : α × β →. σ} (hf : partrec f) : partrec₂ (λ a b, f (a, b)) :=
hf.of_eq $ λ ⟨a, b⟩, rfl

theorem nat_elim
  {f : α → ℕ} {g : α →. σ} {h : α → ℕ × σ →. σ}
  (hf : computable f) (hg : partrec g) (hh : partrec₂ h) :
  partrec (λ a, (f a).elim (g a) (λ y IH, IH.bind (λ i, h a (y, i)))) :=
(nat.partrec.prec' hf hg hh).of_eq $ λ n, begin
  cases e : decode α n with a; simp [e],
  induction f a with m IH; simp,
  rw [IH, bind_map],
  congr, funext s,
  simp [encodek]
end

theorem comp {f : β →. σ} {g : α → β}
  (hf : partrec f) (hg : computable g) : partrec (λ a, f (g a)) :=
(hf.comp hg).of_eq $
λ n, by simp; cases e : decode α n with a;
  simp [e, encodek]

theorem nat_iff {f : ℕ →. ℕ} : partrec f ↔ nat.partrec f :=
by simp [partrec, map_id']

theorem map_encode_iff {f : α →. σ} : partrec (λ a, (f a).map encode) ↔ partrec f :=
iff.rfl

end partrec

namespace partrec₂
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ]

theorem unpaired {f : ℕ → ℕ →. α} : partrec (nat.unpaired f) ↔ partrec₂ f :=
⟨λ h, by simpa using h.comp primrec₂.mkpair.to_comp,
 λ h, h.comp primrec.unpair.to_comp⟩

theorem unpaired' {f : ℕ → ℕ →. ℕ} : nat.partrec (nat.unpaired f) ↔ partrec₂ f :=
partrec.nat_iff.symm.trans unpaired

theorem comp
  {f : β → γ →. σ} {g : α → β} {h : α → γ}
  (hf : partrec₂ f) (hg : computable g) (hh : computable h) :
  partrec (λ a, f (g a) (h a)) := hf.comp (hg.pair hh)

theorem comp₂
  {f : γ → δ →. σ} {g : α → β → γ} {h : α → β → δ}
  (hf : partrec₂ f) (hg : computable₂ g) (hh : computable₂ h) :
  partrec₂ (λ a b, f (g a b) (h a b)) := hf.comp hg hh

end partrec₂

namespace computable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem comp {f : β → σ} {g : α → β}
  (hf : computable f) (hg : computable g) :
  computable (λ a, f (g a)) := hf.comp hg

theorem comp₂ {f : γ → σ} {g : α → β → γ}
  (hf : computable f) (hg : computable₂ g) :
  computable₂ (λ a b, f (g a b)) := hf.comp hg

end computable

namespace computable₂
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable δ] [primcodable σ]

theorem comp
  {f : β → γ → σ} {g : α → β} {h : α → γ}
  (hf : computable₂ f) (hg : computable g) (hh : computable h) :
  computable (λ a, f (g a) (h a)) := hf.comp (hg.pair hh)

theorem comp₂
  {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ}
  (hf : computable₂ f) (hg : computable₂ g) (hh : computable₂ h) :
  computable₂ (λ a b, f (g a b) (h a b)) := hf.comp hg hh

end computable₂

namespace partrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

open computable

theorem rfind {p : α → ℕ →. bool} (hp : partrec₂ p) :
  partrec (λ a, nat.rfind (p a)) :=
(nat.partrec.rfind $ hp.map
  ((primrec.dom_bool (λ b, cond b 0 1))
    .comp primrec.snd).to₂.to_comp).of_eq $
λ n, begin
  cases e : decode α n with a;
    simp [e, nat.rfind_zero_none, map_id'],
  congr, funext n,
  simp [part.map_map, (∘)],
  apply map_id' (λ b, _),
  cases b; refl
end

theorem rfind_opt {f : α → ℕ → option σ} (hf : computable₂ f) :
  partrec (λ a, nat.rfind_opt (f a)) :=
(rfind (primrec.option_is_some.to_comp.comp hf).partrec.to₂).bind
  (of_option hf)

theorem nat_cases_right
  {f : α → ℕ} {g : α → σ} {h : α → ℕ →. σ}
  (hf : computable f) (hg : computable g) (hh : partrec₂ h) :
  partrec (λ a, (f a).cases (some (g a)) (h a)) :=
(nat_elim hf hg (hh.comp fst (pred.comp $ hf.comp fst)).to₂).of_eq $
λ a, begin
  simp, cases f a; simp,
  refine ext (λ b, ⟨λ H, _, λ H, _⟩),
  { rcases mem_bind_iff.1 H with ⟨c, h₁, h₂⟩, exact h₂ },
  { have : ∀ m, (nat.elim (part.some (g a))
      (λ y IH, IH.bind (λ _, h a n)) m).dom,
    { intro, induction m; simp [*, H.fst] },
    exact ⟨⟨this n, H.fst⟩, H.snd⟩ }
end

theorem bind_decode₂_iff {f : α →. σ} : partrec f ↔
  nat.partrec (λ n, part.bind (decode₂ α n) (λ a, (f a).map encode)) :=
⟨λ hf, nat_iff.1 $ (of_option primrec.decode₂.to_comp).bind $
  (map hf (computable.encode.comp snd).to₂).comp snd,
λ h, map_encode_iff.1 $ by simpa [encodek₂]
  using (nat_iff.2 h).comp (@computable.encode α _)⟩

theorem vector_m_of_fn : ∀ {n} {f : fin n → α →. σ}, (∀ i, partrec (f i)) →
  partrec (λ (a : α), vector.m_of_fn (λ i, f i a))
| 0     f hf := const _
| (n+1) f hf := by simp [vector.m_of_fn]; exact
  (hf 0).bind (partrec.bind ((vector_m_of_fn (λ i, hf i.succ)).comp fst)
    (primrec.vector_cons.to_comp.comp (snd.comp fst) snd))

end partrec

@[simp] theorem vector.m_of_fn_part_some {α n} : ∀ (f : fin n → α),
  vector.m_of_fn (λ i, part.some (f i)) = part.some (vector.of_fn f) :=
vector.m_of_fn_pure

namespace computable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem option_some_iff {f : α → σ} : computable (λ a, some (f a)) ↔ computable f :=
⟨λ h, encode_iff.1 $ primrec.pred.to_comp.comp $ encode_iff.2 h,
 option_some.comp⟩

theorem bind_decode_iff {f : α → β → option σ} : computable₂ (λ a n,
  (decode β n).bind (f a)) ↔ computable₂ f :=
⟨λ hf, nat.partrec.of_eq
    (((partrec.nat_iff.2 (nat.partrec.ppred.comp $
        nat.partrec.of_primrec $ primcodable.prim β)).comp snd).bind
      (computable.comp hf fst).to₂.partrec₂) $
  λ n, by simp;
    cases decode α n.unpair.1; simp;
    cases decode β n.unpair.2; simp,
λ hf, begin
  have : partrec (λ a : α × ℕ, (encode (decode β a.2)).cases
    (some option.none) (λ n, part.map (f a.1) (decode β n))) :=
  partrec.nat_cases_right (primrec.encdec.to_comp.comp snd)
    (const none) ((of_option (computable.decode.comp snd)).map
      (hf.comp (fst.comp $ fst.comp fst) snd).to₂),
  refine this.of_eq (λ a, _),
  simp, cases decode β a.2; simp [encodek]
end⟩

theorem map_decode_iff {f : α → β → σ} : computable₂ (λ a n,
  (decode β n).map (f a)) ↔ computable₂ f :=
bind_decode_iff.trans option_some_iff

theorem nat_elim
  {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ}
  (hf : computable f) (hg : computable g) (hh : computable₂ h) :
  computable (λ a, (f a).elim (g a) (λ y IH, h a (y, IH))) :=
(partrec.nat_elim hf hg hh.partrec₂).of_eq $
λ a, by simp; induction f a; simp *

theorem nat_cases {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ}
  (hf : computable f) (hg : computable g) (hh : computable₂ h) :
  computable (λ a, (f a).cases (g a) (h a)) :=
nat_elim hf hg (hh.comp fst $ fst.comp snd).to₂

theorem cond {c : α → bool} {f : α → σ} {g : α → σ}
  (hc : computable c) (hf : computable f) (hg : computable g) :
  computable (λ a, cond (c a) (f a) (g a)) :=
(nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq $
λ a, by cases c a; refl

theorem option_cases {o : α → option β} {f : α → σ} {g : α → β → σ}
  (ho : computable o) (hf : computable f) (hg : computable₂ g) :
  @computable _ σ _ _ (λ a, option.cases_on (o a) (f a) (g a)) :=
option_some_iff.1 $
(nat_cases (encode_iff.2 ho) (option_some_iff.2 hf)
    (map_decode_iff.2 hg)).of_eq $
λ a, by cases o a; simp [encodek]; refl

theorem option_bind {f : α → option β} {g : α → β → option σ}
  (hf : computable f) (hg : computable₂ g) :
  computable (λ a, (f a).bind (g a)) :=
(option_cases hf (const option.none) hg).of_eq $
λ a, by cases f a; refl

theorem option_map {f : α → option β} {g : α → β → σ}
  (hf : computable f) (hg : computable₂ g) : computable (λ a, (f a).map (g a)) :=
option_bind hf (option_some.comp₂ hg)

theorem option_get_or_else {f : α → option β} {g : α → β}
  (hf : computable f) (hg : computable g) :
  computable (λ a, (f a).get_or_else (g a)) :=
(computable.option_cases hf hg (show computable₂ (λ a b, b), from computable.snd)).of_eq $
λ a, by cases f a; refl

theorem subtype_mk {f : α → β} {p : β → Prop} [decidable_pred p] {h : ∀ a, p (f a)}
    (hp : primrec_pred p) (hf : computable f) :
  @computable _ _ _ (primcodable.subtype hp) (λ a, (⟨f a, h a⟩ : subtype p)) :=
hf

theorem sum_cases
  {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ}
  (hf : computable f) (hg : computable₂ g) (hh : computable₂ h) :
  @computable _ σ _ _ (λ a, sum.cases_on (f a) (g a) (h a)) :=
option_some_iff.1 $
(cond (nat_bodd.comp $ encode_iff.2 hf)
  (option_map (computable.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hh)
  (option_map (computable.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hg)).of_eq $
λ a, by cases f a with b c;
  simp [nat.div2_bit, nat.bodd_bit, encodek]; refl

theorem nat_strong_rec
  (f : α → ℕ → σ) {g : α → list σ → option σ} (hg : computable₂ g)
  (H : ∀ a n, g a ((list.range n).map (f a)) = some (f a n)) : computable₂ f :=
suffices computable₂ (λ a n, (list.range n).map (f a)), from
  option_some_iff.1 $
  (list_nth.comp (this.comp fst (succ.comp snd)) snd).to₂.of_eq $
  λ a, by simp [list.nth_range (nat.lt_succ_self a.2)]; refl,
option_some_iff.1 $
(nat_elim snd (const (option.some [])) (to₂ $
  option_bind (snd.comp snd) $ to₂ $
  option_map
    (hg.comp (fst.comp $ fst.comp fst) snd)
    (to₂ $ list_concat.comp (snd.comp fst) snd))).of_eq $
λ a, begin
  simp, induction a.2 with n IH, {refl},
  simp [IH, H, list.range_succ]
end

theorem list_of_fn : ∀ {n} {f : fin n → α → σ},
  (∀ i, computable (f i)) → computable (λ a, list.of_fn (λ i, f i a))
| 0     f hf := const []
| (n+1) f hf := by simp [list.of_fn_succ]; exact
  list_cons.comp (hf 0) (list_of_fn (λ i, hf i.succ))

theorem vector_of_fn {n} {f : fin n → α → σ}
  (hf : ∀ i, computable (f i)) : computable (λ a, vector.of_fn (λ i, f i a)) :=
(partrec.vector_m_of_fn hf).of_eq $ λ a, by simp

end computable

namespace partrec
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

open computable

theorem option_some_iff {f : α →. σ} :
  partrec (λ a, (f a).map option.some) ↔ partrec f :=
⟨λ h, (nat.partrec.ppred.comp h).of_eq $
   λ n, by simp [part.bind_assoc, bind_some_eq_map],
 λ hf, hf.map (option_some.comp snd).to₂⟩

theorem option_cases_right {o : α → option β} {f : α → σ} {g : α → β →. σ}
  (ho : computable o) (hf : computable f) (hg : partrec₂ g) :
  @partrec _ σ _ _ (λ a, option.cases_on (o a) (some (f a)) (g a)) :=
have partrec (λ (a : α), nat.cases (part.some (f a))
  (λ n, part.bind (decode β n) (g a)) (encode (o a))) :=
nat_cases_right (encode_iff.2 ho) hf.partrec $
  ((@computable.decode β _).comp snd).of_option.bind
    (hg.comp (fst.comp fst) snd).to₂,
this.of_eq $ λ a, by cases o a with b; simp [encodek]

theorem sum_cases_right {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ →. σ}
  (hf : computable f) (hg : computable₂ g) (hh : partrec₂ h) :
  @partrec _ σ _ _ (λ a, sum.cases_on (f a) (λ b, some (g a b)) (h a)) :=
have partrec (λ a, (option.cases_on
  (sum.cases_on (f a) (λ b, option.none) option.some : option γ)
  (some (sum.cases_on (f a) (λ b, some (g a b))
     (λ c, option.none)))
  (λ c, (h a c).map option.some) : part (option σ))) :=
option_cases_right
  (sum_cases hf (const option.none).to₂ (option_some.comp snd).to₂)
  (sum_cases hf (option_some.comp hg) (const option.none).to₂)
  (option_some_iff.2 hh),
option_some_iff.1 $ this.of_eq $ λ a, by cases f a; simp

theorem sum_cases_left {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ → σ}
  (hf : computable f) (hg : partrec₂ g) (hh : computable₂ h) :
  @partrec _ σ _ _ (λ a, sum.cases_on (f a) (g a) (λ c, some (h a c))) :=
(sum_cases_right (sum_cases hf
  (sum_inr.comp snd).to₂ (sum_inl.comp snd).to₂) hh hg).of_eq $
λ a, by cases f a; simp

lemma fix_aux {α σ} (f : α →. σ ⊕ α) (a : α) (b : σ) :
  let F : α → ℕ →. σ ⊕ α := λ a n,
    n.elim (some (sum.inr a)) $ λ y IH, IH.bind $ λ s,
    sum.cases_on s (λ _, part.some s) f in
  (∃ (n : ℕ), ((∃ (b' : σ), sum.inl b' ∈ F a n) ∧
        ∀ {m : ℕ}, m < n → (∃ (b : α), sum.inr b ∈ F a m)) ∧
      sum.inl b ∈ F a n) ↔ b ∈ pfun.fix f a :=
begin
  intro, refine ⟨λ h, _, λ h, _⟩,
  { rcases h with ⟨n, ⟨_x, h₁⟩, h₂⟩,
    have : ∀ m a' (_: sum.inr a' ∈ F a m)
      (_: b ∈ pfun.fix f a'), b ∈ pfun.fix f a,
    { intros m a' am ba,
      induction m with m IH generalizing a'; simp [F] at am,
      { rwa ← am },
      rcases am with ⟨a₂, am₂, fa₂⟩,
      exact IH _ am₂ (pfun.mem_fix_iff.2 (or.inr ⟨_, fa₂, ba⟩)) },
    cases n; simp [F] at h₂, {cases h₂},
    rcases h₂ with h₂ | ⟨a', am', fa'⟩,
    { cases h₁ (nat.lt_succ_self _) with a' h,
      injection mem_unique h h₂ },
    { exact this _ _ am' (pfun.mem_fix_iff.2 (or.inl fa')) } },
  { suffices : ∀ a' (_: b ∈ pfun.fix f a') k (_: sum.inr a' ∈ F a k),
       ∃ n, sum.inl b ∈ F a n ∧
         ∀ (m < n) (_ : k ≤ m), ∃ a₂, sum.inr a₂ ∈ F a m,
    { rcases this _ h 0 (by simp [F]) with ⟨n, hn₁, hn₂⟩,
      exact ⟨_, ⟨⟨_, hn₁⟩, λ m mn, hn₂ m mn (nat.zero_le _)⟩, hn₁⟩ },
    intros a₁ h₁,
    apply pfun.fix_induction h₁, intros a₂ h₂ IH k hk,
    rcases pfun.mem_fix_iff.1 h₂ with h₂ | ⟨a₃, am₃, fa₃⟩,
    { refine ⟨k.succ, _, λ m mk km, ⟨a₂, _⟩⟩,
      { simp [F], exact or.inr ⟨_, hk, h₂⟩ },
      { rwa le_antisymm (nat.le_of_lt_succ mk) km } },
    { rcases IH _ am₃ k.succ _ with ⟨n, hn₁, hn₂⟩,
      { refine ⟨n, hn₁, λ m mn km, _⟩,
        cases km.lt_or_eq_dec with km km,
        { exact hn₂ _ mn km },
        { exact km ▸ ⟨_, hk⟩ } },
      { simp [F], exact ⟨_, hk, am₃⟩ } } }
end

theorem fix {f : α →. σ ⊕ α} (hf : partrec f) : partrec (pfun.fix f) :=
let F : α → ℕ →. σ ⊕ α := λ a n,
  n.elim (some (sum.inr a)) $ λ y IH, IH.bind $ λ s,
  sum.cases_on s (λ _, part.some s) f in
have hF : partrec₂ F :=
partrec.nat_elim snd (sum_inr.comp fst).partrec
  (sum_cases_right (snd.comp snd)
    (snd.comp $ snd.comp fst).to₂
    (hf.comp snd).to₂).to₂,
let p := λ a n, @part.map _ bool
  (λ s, sum.cases_on s (λ_, tt) (λ _, ff)) (F a n) in
have hp : partrec₂ p := hF.map ((sum_cases computable.id
  (const tt).to₂ (const ff).to₂).comp snd).to₂,
(hp.rfind.bind (hF.bind
  (sum_cases_right snd snd.to₂ none.to₂).to₂).to₂).of_eq $
λ a, ext $ λ b, by simp; apply fix_aux f

end partrec
