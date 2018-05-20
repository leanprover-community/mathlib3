/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

The partial recursive functions are defined similarly to the primitive
recursive functions, but now all functions are partial, implemented
using the `roption` monad, and there is an additional operation, called
μ-recursion, which performs unbounded minimization.
-/
import data.computability.primrec data.pfun

open encodable denumerable roption

namespace nat

section rfind
parameter (p : ℕ →. bool)

private def lbp (m n : ℕ) : Prop := m = n + 1 ∧ ∀ k ≤ n, ff ∈ p k

parameter (H : ∃ n, tt ∈ p n ∧ ∀ k < n, (p k).dom)

private def wf_lbp : well_founded lbp :=
⟨let ⟨n, pn⟩ := H in begin
  suffices : ∀m k, n ≤ k + m → acc (lbp p) k,
  { from λa, this _ _ (nat.le_add_left _ _) },
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
    intros n h, cases lt_or_eq_of_le h with h h,
    { exact al _ h },
    { rw h, exact ⟨_, e⟩ } },
  { exact ⟨m, ⟨_, e⟩, al⟩ }
end

end rfind

def rfind (p : ℕ →. bool) : roption ℕ :=
⟨_, λ h, (rfind_x p h).1⟩

theorem rfind_spec {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) : tt ∈ p n :=
h.snd ▸ (rfind_x p h.fst).2.1

theorem rfind_min {p : ℕ →. bool} {n : ℕ} (h : n ∈ rfind p) :
  ∀ {m : ℕ}, m < n → ff ∈ p m :=
h.snd ▸ (rfind_x p h.fst).2.2

@[simp] theorem rfind_dom {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m < n → (p m).dom :=
iff.rfl

@[simp] theorem rfind_dom' {p : ℕ →. bool} :
  (rfind p).dom ↔ ∃ n, tt ∈ p n ∧ ∀ {m : ℕ}, m ≤ n → (p m).dom :=
exists_congr $ λ n, and_congr_right $ λ pn,
⟨λ H m h, (eq_or_lt_of_le h).elim (λ e, e.symm ▸ pn.fst) (H _),
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
(p0 ▸ h₂ (zero_le _) : (@roption.none bool).dom)

inductive partrec : (ℕ →. ℕ) → Prop
| zero : partrec (pure 0)
| succ : partrec succ
| left : partrec (λ n, n.unpair.1)
| right : partrec (λ n, n.unpair.2)
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
  case nat.primrec.pair : f g hf hg pf pg {
    refine (pf.pair pg).of_eq_tot (λ n, _),
    simp [has_seq.seq] },
  case nat.primrec.comp : f g hf hg pf pg {
    refine (pf.comp pg).of_eq_tot (λ n, _),
    simp },
  case nat.primrec.prec : f g hf hg pf pg {
    refine (pf.prec pg).of_eq_tot (λ n, _),
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
  roption.bind (decode α n) (λ a, (f a).map encode))

def partrec₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (f : α → β →. σ) := partrec (λ p : α × β, f p.1 p.2)

def computable {α σ} [primcodable α] [primcodable σ] (f : α → σ) := partrec (f : α →. σ)

def computable₂ {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  (f : α → β → σ) := computable (λ p : α × β, f p.1 p.2)

theorem primrec.to_comp {α σ} [primcodable α] [primcodable σ]
  {f : α → σ} (hf : primrec f) : computable f :=
(nat.partrec.ppred.comp (nat.partrec.of_primrec hf)).of_eq $
λ n, by simp; cases decode α n; simp [option.map, option.bind]

theorem computable.part {α σ} [primcodable α] [primcodable σ]
  {f : α → σ} (hf : computable f) : partrec (f : α →. σ) := hf

theorem computable₂.part {α β σ} [primcodable α] [primcodable β] [primcodable σ]
  {f : α → β → σ} (hf : computable₂ f) : partrec₂ (λ a, (f a : β →. σ)) := hf

namespace computable
variables {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variables [primcodable α] [primcodable β] [primcodable γ] [primcodable σ]

theorem of_eq {f g : α → σ} (hf : computable f) (H : ∀ n, f n = g n) : computable g :=
(funext H : f = g) ▸ hf

theorem const (s : σ) : computable (λ a : α, s) :=
(primrec.const _).to_comp

theorem of_option {f : α → option β}
  (hf : computable f) : partrec (λ a, (f a : roption β)) :=
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

theorem none : partrec (λ a : α, @roption.none σ) :=
nat.partrec.none.of_eq $ λ n, by cases decode α n; simp

protected theorem some : partrec (@roption.some α) := computable.id

theorem const' (s : roption σ) : partrec (λ a : α, s) :=
by haveI := classical.dec s.dom; exact
(of_option (const (to_option s))).of_eq (λ a, of_to_option s)

protected theorem bind {f : α →. β} {g : α → β →. σ}
  (hf : partrec f) (hg : partrec₂ g) : partrec (λ a, (f a).bind (g a)) :=
(hg.comp (nat.partrec.some.pair hf)).of_eq $
λ n, by simp [(<*>)]; cases e : decode α n with a;
  simp [e, option.bind, option.map, encodek]

theorem map {f : α →. β} {g : α → β → σ}
  (hf : partrec f) (hg : computable₂ g) : partrec (λ a, (f a).map (g a)) :=
by simpa [bind_some_eq_map] using
   @@partrec.bind _ _ _ (λ a b, roption.some (g a b)) hf hg

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
  simp [option.map, option.bind, encodek]
end

theorem comp {f : β →. σ} {g : α → β} 
  (hf : partrec f) (hg : computable g) : partrec (λ a, f (g a)) :=
(hf.comp hg).of_eq $
λ n, by simp; cases e : decode α n with a;
  simp [e, option.bind, option.map, encodek]

theorem nat_iff {f : ℕ →. ℕ} : partrec f ↔ nat.partrec f :=
by simp [partrec, map_id']

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

theorem nat_elim
  {f : α → ℕ} {g : α → σ} {h : α → ℕ × σ → σ}
  (hf : computable f) (hg : computable g) (hh : computable₂ h) :
  computable (λ a, (f a).elim (g a) (λ y IH, h a (y, IH))) :=
(partrec.nat_elim hf hg hh.part).of_eq $
λ a, by simp; induction f a; simp *

/-
theorem nat_cases {f : α → ℕ} {g : α → σ} {h : α → ℕ → σ}
  (hf : computable f) (hg : computable g) (hh : computable₂ h) :
  computable (λ a, (f a).cases (g a) (h a)) :=
_
-/

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
    simp [e, option.bind, option.map, nat.rfind_zero_none, map_id'],
  congr, funext n,
  simp [map_map, (∘)],
  apply map_id' (λ b, _),
  cases b; refl
end

/-
theorem cond {c : α → bool} {f : α →. σ} {g : α →. σ}
  (hc : computable c) (hf : partrec f) (hg : partrec g) :
  partrec (λ a, cond (c a) (f a) (g a)) :=
(nat_cases (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq $
λ a, by cases c a; refl

theorem sum_cases
  {f : α → β ⊕ γ} {g : α → β →. σ} {h : α → γ →. σ}
  (hf : computable f) (hg : partrec₂ g) (hh : partrec₂ h) :
  @partrec _ σ _ _ (λ a, sum.cases_on (f a) (g a) (h a)) :=
(cond (nat_bodd.comp $ encode_iff.2 hf)
  (option_map (primrec.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hh)
  (option_map (primrec.decode.comp $ nat_div2.comp $ encode_iff.2 hf) hg)).of_eq $
λ a, by cases f a with b c;
  simp [nat.div2_bit, nat.bodd_bit, encodek]; refl

theorem fix {α σ} [primcodable α] [primcodable σ]
  {f : α →. σ ⊕ α} (hf : partrec f) : partrec (pfun.fix f) :=
begin
  have := nat_elim snd fst _,
end
-/

end partrec

namespace nat.partrec
open nat (mkpair)

theorem rfind' {f} (hf : nat.partrec f) : nat.partrec (nat.unpaired (λ a m,
  (nat.rfind (λ n, (λ m, m = 0) <$> f (mkpair a (n + m)))).map (+ m))) :=
partrec₂.unpaired'.2 $
begin
  refine partrec.map
    ((@partrec₂.unpaired' (λ (a b : ℕ),
      nat.rfind (λ n, (λ m, m = 0) <$> f (mkpair a (n + b))))).1 _)
    (primrec.nat_add.comp primrec.snd $
      primrec.snd.comp primrec.fst).to_comp.to₂,
  have := rfind (partrec₂.unpaired'.2 ((partrec.nat_iff.2 hf).comp
    (primrec₂.mkpair.comp
      (primrec.fst.comp $ primrec.unpair.comp primrec.fst)
      (primrec.nat_add.comp primrec.snd
        (primrec.snd.comp $ primrec.unpair.comp primrec.fst))).to_comp).to₂),
  simp at this, exact this
end

inductive code : Type
| zero : code
| succ : code
| left : code
| right : code
| pair : code → code → code
| comp : code → code → code
| prec : code → code → code
| rfind' : code → code

namespace code

def encode_code : code → ℕ
| zero         := 0
| succ         := 1
| left         := 2
| right        := 3
| (pair cf cg) := bit0 (bit0 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (comp cf cg) := bit0 (bit1 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (prec cf cg) := bit1 (bit0 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (rfind' cf)  := bit1 (bit1 $ encode_code cf) + 4

def of_nat_code : ℕ → code
| 0     := zero
| 1     := succ
| 2     := left
| 3     := right
| (n+4) := let m := n.div2.div2 in
  have hm : m < n + 4, by simp [m, nat.div2_val];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_le_left hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_le_right hm,
  match n.bodd, n.div2.bodd with
  | ff, ff := pair (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | ff, tt := comp (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | tt, ff := prec (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | tt, tt := rfind' (of_nat_code m)
  end

private theorem encode_of_nat_code : ∀ n, encode_code (of_nat_code n) = n
| 0     := rfl
| 1     := rfl
| 2     := rfl
| 3     := rfl
| (n+4) := let m := n.div2.div2 in
  have hm : m < n + 4, by simp [m, nat.div2_val];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_le_left hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_le_right hm,
  have IH : _ := encode_of_nat_code m,
  have IH1 : _ := encode_of_nat_code m.unpair.1,
  have IH2 : _ := encode_of_nat_code m.unpair.2,
  begin
    transitivity, swap,
    rw [← nat.bit_decomp n, ← nat.bit_decomp n.div2],
    simp [encode_code, of_nat_code, -add_comm],
    cases n.bodd; cases n.div2.bodd;
      simp [encode_code, of_nat_code, -add_comm, IH, IH1, IH2, m, nat.bit]
  end

instance : denumerable code :=
mk' ⟨encode_code, of_nat_code,
  λ c, by induction c; try {refl}; simp [
    encode_code, of_nat_code, -add_comm, *],
  encode_of_nat_code⟩

def eval : code → ℕ →. ℕ
| zero         := pure 0
| succ         := nat.succ
| left         := λ n, n.unpair.1
| right        := λ n, n.unpair.2
| (pair cf cg) := λ n, mkpair <$> eval cf n <*> eval cg n
| (comp cf cg) := λ n, eval cg n >>= eval cf
| (prec cf cg) := nat.unpaired (λ a n,
    n.elim (eval cf a) (λ y IH, do i ← IH, eval cg (mkpair a (mkpair y i))))
| (rfind' cf)  := nat.unpaired (λ a m,
    (nat.rfind (λ n, (λ m, m = 0) <$>
      eval cf (mkpair a (n + m)))).map (+ m))

def evaln : ∀ k : ℕ, code → ℕ → option ({m // m ≤ k} × ℕ)
| 0     _            := λ m, option.none
| (k+1) zero         := λ n, pure (⟨_, le_refl _⟩, 0)
| (k+1) succ         := λ n, pure (⟨_, le_refl _⟩, (nat.succ n))
| (k+1) left         := λ n, pure (⟨_, le_refl _⟩, n.unpair.1)
| (k+1) right        := λ n, pure (⟨_, le_refl _⟩, n.unpair.2)
| (k+1) (pair cf cg) := λ n, do
  (⟨k₁, h₁⟩, x) ← evaln (k+1) cf n,
  (⟨k₂, h₂⟩, y) ← evaln (k+1) cg n,
  pure (⟨min k₁ k₂, le_trans (min_le_left _ _) h₁⟩, mkpair x y)
| (k+1) (comp cf cg) := λ n, do
  (⟨k₁, h₁⟩, x) ← evaln (k+1) cg n,
  (⟨k₂, h₂⟩, y) ← evaln (k+1) cf x,
  pure (⟨min k₁ k₂, le_trans (min_le_left _ _) h₁⟩, y)
| (k+1) (prec cf cg) := nat.unpaired $ λ a n,
  n.cases (evaln (k+1) cf a) $ λ y, do
    (⟨k₁, h₁⟩, i) ← evaln k (prec cf cg) (mkpair a y),
    let h₁' := nat.lt_succ_of_le h₁,
    (⟨k₂, h₂⟩, y) ← evaln k₁ cg (mkpair a (mkpair y i)),
    pure (⟨k₂, nat.le_succ_of_le $ le_trans h₂ h₁⟩, y)
| (k+1) (rfind' cf)  := nat.unpaired $ λ a m, do
  (⟨k₁, h₁⟩, x) ← evaln (k+1) cf 0,
  if x = 0 then pure (⟨k₁, h₁⟩, 0) else
  do (⟨k₂, h₂⟩, y) ← evaln k (rfind' cf) (mkpair a (x+1)),
  pure (⟨k₂, nat.le_succ_of_le h₂⟩, y)

instance : has_mem (ℕ →. ℕ) code := ⟨λ f c, eval c = f⟩

theorem exists_code {f : ℕ →. ℕ} : nat.partrec f ↔ ∃ c : code, eval c = f :=
⟨λ h, begin
  induction h,
  case nat.partrec.zero { exact ⟨zero, rfl⟩ },
  case nat.partrec.succ { exact ⟨succ, rfl⟩ },
  case nat.partrec.left { exact ⟨left, rfl⟩ },
  case nat.partrec.right { exact ⟨right, rfl⟩ },
  case nat.partrec.pair : f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨pair cf cg, rfl⟩ },
  case nat.partrec.comp : f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨comp cf cg, rfl⟩ },
  case nat.partrec.prec : f g pf pg hf hg {
    rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨prec cf cg, rfl⟩ },
  case nat.partrec.rfind : f pf hf {
    rcases hf with ⟨cf, rfl⟩,
    refine ⟨comp (rfind' cf) (pair (pair left right) zero), _⟩,
    simp [eval, (<*>), pure, pfun.pure, map_id'] },
end, λ h, begin
  rcases h with ⟨c, rfl⟩, induction c,
  case nat.partrec.code.zero { exact nat.partrec.zero },
  case nat.partrec.code.succ { exact nat.partrec.succ },
  case nat.partrec.code.left { exact nat.partrec.left },
  case nat.partrec.code.right { exact nat.partrec.right },
  case nat.partrec.code.pair : cf cg pf pg { exact pf.pair pg },
  case nat.partrec.code.comp : cf cg pf pg { exact pf.comp pg },
  case nat.partrec.code.prec : cf cg pf pg { exact pf.prec pg },
  case nat.partrec.code.rfind' : cf pf { exact pf.rfind' },
end⟩

section
open primrec

theorem pair_prim : primrec₂ pair :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem comp_prim : primrec₂ comp :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit1.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem prec_prim : primrec₂ prec :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem rfind_prim : primrec rfind' :=
of_nat_iff.2 $ encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit1.comp $
    encode_iff.2 $ primrec.of_nat code)
  (const 4)

theorem rec_prim {α σ} [primcodable α] [primcodable σ]
  {c : α → code} (hc : primrec c)
  {z : α → σ} (hz : primrec z)
  {s : α → σ} (hs : primrec s)
  {l : α → σ} (hl : primrec l)
  {r : α → σ} (hr : primrec r)
  {pr : α → code × code × σ × σ → σ} (hpr : primrec₂ pr)
  {co : α → code × code × σ × σ → σ} (hco : primrec₂ co)
  {pc : α → code × code × σ × σ → σ} (hpc : primrec₂ pc)
  {rf : α → code × σ → σ} (hrf : primrec₂ rf) :
let PR (a) := λ cf cg hf hg, pr a (cf, cg, hf, hg),
    CO (a) := λ cf cg hf hg, co a (cf, cg, hf, hg),
    PC (a) := λ cf cg hf hg, pc a (cf, cg, hf, hg),
    RF (a) := λ cf hf, rf a (cf, hf),
    F (a c) : σ := code.rec_on c
      (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a) in
    primrec (λ a, F a (c a)) :=
begin
  intros,
  let G₁ : (α × list σ) × ℕ × ℕ → option σ := λ p,
    let a := p.1.1, IH := p.1.2, n := p.2.1, m := p.2.2 in
    (IH.nth m).bind $ λ s,
    (IH.nth m.unpair.1).bind $ λ s₁,
    (IH.nth m.unpair.2).map $ λ s₂,
    cond n.bodd
      (cond n.div2.bodd
        (rf a (of_nat code m, s))
        (pc a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd
        (co a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))
        (pr a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))),
  have : primrec G₁,
  { refine option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _,
    refine option_bind ((list_nth.comp (snd.comp fst)
      (fst.comp $ primrec.unpair.comp (snd.comp snd))).comp fst) _,
    refine option_map ((list_nth.comp (snd.comp fst)
      (snd.comp $ primrec.unpair.comp (snd.comp snd))).comp $ fst.comp fst) _,
    have a := fst.comp (fst.comp $ fst.comp $ fst.comp fst),
    have n := fst.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m := snd.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m₁ := fst.comp (primrec.unpair.comp m),
    have m₂ := snd.comp (primrec.unpair.comp m),
    have s := snd.comp (fst.comp fst),
    have s₁ := snd.comp fst,
    have s₂ := snd,
    exact (nat_bodd.comp n).cond
      ((nat_bodd.comp $ nat_div2.comp n).cond
        (hrf.comp a (((primrec.of_nat code).comp m).pair s))
        (hpc.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂)))
      (primrec.cond (nat_bodd.comp $ nat_div2.comp n)
        (hco.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))
        (hpr.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))) },
  let G : α → list σ → option σ := λ a IH,
    IH.length.cases (some (z a)) $ λ n,
    n.cases (some (s a)) $ λ n,
    n.cases (some (l a)) $ λ n,
    n.cases (some (r a)) $ λ n,
    G₁ ((a, IH), n, n.div2.div2),
  have : primrec₂ G := (nat_cases
    (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) $
    nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hl.comp (fst.comp $ fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hr.comp (fst.comp $ fst.comp $ fst.comp fst)))
    (this.comp $
      ((fst.pair snd).comp $ fst.comp $ fst.comp $ fst.comp $ fst).pair $
      snd.pair $ nat_div2.comp $ nat_div2.comp snd)),
  refine ((primrec.nat_strong_rec
    (λ a n, F a (of_nat code n)) this.to₂ $ λ a n, _).comp
    primrec.id $ primrec.encode_iff.2 hc).of_eq (λ a, by simp),
  simp,
  iterate 4 {cases n with n, {refl}},
  simp [G], rw [list.length_map, list.length_range],
  let m := n.div2.div2,
  show G₁ ((a, (list.range (n+4)).map (λ n, F a (of_nat code n))), n, m)
    = option.some (F a (of_nat code (n+4))),
  have hm : m < n + 4, by simp [nat.div2_val, m];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_le_left hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_le_right hm,
  simp [G₁], simp [list.nth_map, list.nth_range,
    hm, m1, m2, option.map, option.bind],
  change of_nat code (n+4) with of_nat_code (n+4),
  simp [of_nat_code],
  cases n.bodd; cases n.div2.bodd; refl
end

/-
theorem rec_part {α σ} [primcodable α] [primcodable σ]
  {c : α → code} (hc : computable c)
  {z : α →. σ} (hz : partrec z)
  {s : α →. σ} (hs : partrec s)
  {l : α →. σ} (hl : partrec l)
  {r : α →. σ} (hr : partrec r)
  {pr : α → code × code × σ × σ →. σ} (hpr : partrec₂ pr)
  {co : α → code × code × σ × σ →. σ} (hco : partrec₂ co)
  {pc : α → code × code × σ × σ →. σ} (hpc : partrec₂ pc)
  {rf : α → code × σ →. σ} (hrf : partrec₂ rf) :
let PR (a) := λ cf cg (pf pg : roption σ),
       pf.bind $ λ hf, pg.bind $ λ hg, pr a (cf, cg, hf, hg),
    CO (a) := λ cf cg (pf pg : roption σ),
       pf.bind $ λ hf, pg.bind $ λ hg, co a (cf, cg, hf, hg),
    PC (a) := λ cf cg (pf pg : roption σ),
       pf.bind $ λ hf, pg.bind $ λ hg, pc a (cf, cg, hf, hg),
    RF (a) := λ cf (pf : roption σ), pf.bind $ λ hf, rf a (cf, hf),
    F (a c) : roption σ := code.rec_on c
      (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a) in
    partrec (λ a, F a (c a)) :=
begin
  intros,

end
-/

end

end code
end nat.partrec