import logic.basic
import data.bool
import data.nat.basic
import data.list.min_max
import algebra.order_functions
import tactic.vampire.list
import tactic.vampire.misc

universes u v

namespace vampire

open nat list

variables {α β : Type}
variables {A : Type u}
variables {B : Type v}

def rl  (α : Type) : Type := list α → Prop
def fn  (α : Type) : Type := list α → α
def rls (α : Type) : Type := nat → rl α
def fns (α : Type) : Type := nat → fn α
def vas (α : Type) : Type := nat → α

/-
def nrl (α : Type) : nat → Type
| 0       := Prop
| (k + 1) := α → nrl k

def nfn (α : Type) : nat → Type
| 0       := α
| (k + 1) := α → nfn k

def nrl.unfix : ∀ {k : nat}, nrl α k → rl α
| 0       f []        := f
| 0       f (_ :: _)  := false
| (k + 1) f []        := false
| (k + 1) f (a :: as) := nrl.unfix (f a) as

def nfn.unfix [inhabited α] : ∀ {k : nat}, nfn α k → fn α
| 0       f []        := f
| 0       f (_ :: _)  := default α
| (k + 1) f []        := default α
| (k + 1) f (a :: as) := nfn.unfix (f a) as

def Rdf (α : Type) : rls α := λ _ _, false
def Fdf (α : Type) [inhabited α] : fns α := λ _ _, default α
def Vdf (α : Type) [inhabited α] : vas α := λ _, default α

local notation f `₀↦` a := assign a f

-/

@[derive decidable_eq]
inductive xtrm : bool → Type 
| vr   : nat → xtrm ff
| fn   : nat → xtrm tt → xtrm ff
| nil  : xtrm tt 
| cons : xtrm ff → xtrm tt → xtrm tt 

@[reducible] def trm  := xtrm ff
@[reducible] def trms := xtrm tt

local notation `#` := xtrm.vr
local notation `&` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts

namespace xtrm 

def size : ∀ {b : bool}, xtrm b → nat
| ff (# k)      := 0
| ff (& k ts)   := ts.size + 1
| tt []*        := 0
| tt (t ::* ts) := t.size + ts.size + 1

lemma size_tail_lt_size_cons {t : trm} {ts : trms} : 
  (xtrm.size ts) < xtrm.size (xtrm.cons t ts) :=  
by { apply lt_of_lt_of_le (lt_succ_self _),
     unfold xtrm.size,
     rw add_assoc, 
     apply nat.le_add_left }

end xtrm

namespace trms

def mem (t : trm) : trms → Prop
| []*        := false
| (s ::* ts) := t = s ∨ mem ts
using_well_founded {
  dec_tac := `[ apply xtrm.size_tail_lt_size_cons ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}

instance has_mem : has_mem trm trms := ⟨mem⟩ 

lemma mem_cons_iff (t s : trm) (ts : trms) : 
  t ∈ (s ::* ts) ↔ t = s ∨ t ∈ ts := iff.refl _

end trms

lemma xtrm.lt_size_fn {k : nat} :
  ∀ {ts : trms} {s : trm}, 
  s ∈ ts → xtrm.size s < xtrm.size (& k ts)  
| []*        := by rintros _ ⟨_⟩
| (t ::* ts) := 
  by { intros s h0,
       rw trms.mem_cons_iff at h0, cases h0,
       { subst h0, unfold xtrm.size, 
         repeat {rw [add_assoc]},
         apply lt_trans (lt_succ_self _),
         rw @add_lt_add_iff_left _ _ _ 1 _,
         apply succ_lt_succ (zero_lt_succ _) },
       apply lt_trans (@xtrm.lt_size_fn ts _ h0), 
       apply succ_lt_succ,
       apply xtrm.size_tail_lt_size_cons }

/-

def trms.length : trms → nat 
| []*        := 0
| (_ ::* ts) := trms.length ts + 1

def vmap  : Type := nat × trm
def vmaps : Type := list vmap

def vmaps.get (k : nat) : vmaps → option trm
| []             := none
| ((m, t) :: μs) := if k = m then some t else vmaps.get μs

-/
namespace trm

def map (f : trm → A) : trms → list A 
| []*        := []
| (t ::* ts) := f t :: map ts

def lmap : ∀ {ts : trms}, (∀ t : trm, t ∈ ts → A) → list A 
| []*  _       := []
| (t ::* ts) f := (f t (or.inl rfl) :: @lmap ts (λ x h, f x $ or.inr h))

def tmap : ∀ {ts : trms}, (∀ t : trm, t ∈ ts → trm) → trms  
| []*  _       := []*
| (t ::* ts) f := (f t (or.inl rfl) ::* @tmap ts (λ x h, f x $ or.inr h))

def rec {C : trm → Sort u} 
  (f : ∀ k : nat, C (# k)) 
  (g : ∀ k : nat, ∀ ts : trms, 
    (∀ t ∈ ts, C t) → C (& k ts)) : 
  ∀ t : trm, C t 
| (# k)    := f _
| (& k ts) := g _ _ (λ x h, rec _)
using_well_founded {
  dec_tac := `[ apply xtrm.lt_size_fn, assumption ],
  rel_tac := λ _ _, `[exact ⟨_, measure_wf xtrm.size⟩]
}
/-


def repr : trm → string := 
rec 
  (λ k, "X" ++ k.to_subs) 
  (λ k ts f, "f" ++ k.to_subs ++ repr_tuple (lmap f))

instance has_repr : has_repr trm := ⟨repr⟩

meta instance has_to_format : has_to_format trm := ⟨λ x, repr x⟩ 

meta def to_expr : trm → expr :=
rec 
  (λ k, expr.app `(xtrm.vr) k.to_expr) 
  (λ k ts f, expr.app `(xtrm.fn) 
    (foldr (λ x y, expr.mk_app `(xtrm.cons) [x, y]) `(xtrm.nil) (lmap f)))

def vnew : trm → nat :=
rec succ (λ _ _ f, (lmap f).maximum)

def fnew : trm → nat :=
rec (λ _, 0) (λ k _ f, max (k + 1) (lmap f).maximum)

-/
def vinc (m n : nat) : trm → trm :=
rec 
  (λ k, # (if k < m then k else k + n)) 
  (λ k ts f, & k (tmap f))
/-
def finc : trm → trm :=
rec 
  (λ k, # k)
  (λ k ts f, & (k + 1) (tmap f))
  
def vdec (m : nat) : trm → trm :=
rec 
  (λ k, # (if m < k then k - 1 else k))
  (λ k ts f, & k (tmap f))

def vsub (m : nat) (r : trm) : trm → trm :=
rec 
  (λ k, if k = m then r else # k)
  (λ k ts f, & k (tmap f))

def vsubs (μs : vmaps) : trm → trm :=
rec 
  (λ k, match μs.get k with
        | none     := # k
        | (some t) := t
        end)
  (λ k ts f, & k (tmap f))

def val (F : fns α) (V : vas α) : trm → α :=
rec V (λ k _ f, F k (lmap f))

lemma lmap_eq_map (f : trm → A) :
  ∀ ts : trms, lmap (λ x, λ _ : x ∈ ts, f x) = map f ts 
| []*        := rfl
| (t ::* ts) := 
  by { unfold lmap, unfold map,
       apply congr_arg,
       apply lmap_eq_map }
  
lemma val_fn (F : fns α) (V : vas α) (k : nat) (ts : trms) : 
  val F V (& k ts) = F k (map (val F V) ts) := 
by { unfold val, unfold rec,
     apply congr_arg,
     apply lmap_eq_map }


def farity (m : nat) : trm → option nat :=
rec 
  (λ _, none)
  (λ k ts f, if k = m 
             then some (trms.length ts) 
             else (lmap f).orelse)

def vocc (m : nat) : trm → Prop :=
rec (λ k, k = m) (λ _ _ f, (lmap f).disj)

lemma exists_mem_cons_iff 
  (p : trm → Prop) (t : trm) (ts : trms) :
  (∃ x ∈ (t ::* ts), p x) ↔ p t ∨ ∃ x ∈ ts, p x :=
by { constructor,
     { rintro ⟨s, h0, h1⟩, 
       rw xtrm.mem_cons_iff at h0,
       cases h0,
       { left, rw ← h0, exact h1 },
       right, refine ⟨s, h0, h1⟩ },
     rintro (h0 | ⟨s, h0, h1⟩),
     { refine ⟨t, or.inl rfl, h0⟩ },
     refine ⟨s, or.inr h0, h1⟩ }

lemma disj_iff_exists_mem (p : trm → Prop) :
  ∀ ts : trms, (map p ts).disj ↔ ∃ x ∈ ts, p x
| []*        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (t ::* ts) := 
  by { unfold map,
       rw [disj_cons, exists_mem_cons_iff,
         disj_iff_exists_mem ts] }

lemma vocc_fn (k m : nat) (ts : trms) : 
  vocc m (& k ts) ↔ ∃ t ∈ ts, trm.vocc m t := 
by { have h0 : vocc m (& k ts) = (map (vocc m) ts).disj,
     { unfold vocc, unfold rec,
       apply congr_arg, apply lmap_eq_map },
     rw h0, apply disj_iff_exists_mem }
  
def replace (t s : trm) : trm → trm :=
rec
  (λ k, if (# k) = t then s else (# k))
  (λ k ts f, if (& k ts) = t 
             then s 
             else & k (tmap f))
            
lemma forall_mem_of_forall_mem_cons 
  {p : trm → Prop} {t : trm} {ts : trms} :
  (∀ x : trm, x ∈ (t ::* ts) → p x) → 
  (∀ x : trm, x ∈ ts → p x) := 
λ h0 t h1, h0 _ (or.inr h1)

lemma map_eq_map (f g : trm → A) :
  ∀ {ts : trms}, 
  (∀ t : trm, t ∈ ts → f t = g t) → 
  map f ts = map g ts
| []* := λ _, rfl
| (t ::* ts) :=
  by { intro h0, unfold map,
       rw [ h0 _ (or.inl rfl), @map_eq_map ts ],
       apply forall_mem_of_forall_mem_cons h0 }


meta def trmlst.to_expr : list trm → expr 
| []        := `(@list.nil trm)
| (t :: ts) := 
  expr.mk_app `(@list.cons trm) [t.to_expr, trmlst.to_expr ts]

def vas.vsubs (F : fns α) (μ : vmaps) (V : vas α) (k : nat) : α :=
match μ.get k with
| none     := V k
| (some t) := t.val F V 
end

-/

end trm

inductive atm : Type 
| rl : nat → list trm → atm
| eq : trm → trm →  atm

namespace atm

/-
def repr : atm → string
| (atm.rl k ts) := "r" ++ k.to_subs ++ ts.repr
| (atm.eq t s) := t.repr ++ " = " ++ s.repr

meta def to_expr : atm → expr
| (atm.rl k ts) := 
  expr.mk_app `(atm.rl) [k.to_expr, trmlst.to_expr ts]
| (atm.eq t s) := 
  expr.mk_app `(atm.eq) [t.to_expr, s.to_expr]

def vnew : atm → nat
| (atm.rl _ ts) := (ts.map trm.vnew).maximum
| (atm.eq t s)  := max t.vnew s.vnew

def fnew : atm → nat
| (atm.rl _ ts) := (ts.map trm.fnew).maximum
| (atm.eq t s)  := max t.fnew s.fnew

def rnew : atm → nat
| (atm.rl k _) := k + 1
| (atm.eq _ _) := 0

-/
def vinc (m n : nat) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vinc m n)
| (atm.eq t s)  := atm.eq (t.vinc m n) (s.vinc m n)

def default : atm := atm.eq (& 0 []*) (& 0 []*)

/-

def vdec (m : nat) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vdec m)
| (atm.eq t s)  := atm.eq (t.vdec m) (s.vdec m)


def finc : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map trm.finc) 
| (atm.eq t s)  := atm.eq t.finc s.finc

def vsub (m : nat) (r : trm) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vsub m r)
| (atm.eq t s)  := atm.eq (trm.vsub m r t) (trm.vsub m r s)

def vsubs (μs : vmaps) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.vsubs μs)
| (atm.eq t s)  := atm.eq (t.vsubs μs) (s.vsubs μs)

def holds (R : rls α) (F : fns α) (V : vas α) : atm → Prop
| (atm.rl k ts) := R k (ts.map $ trm.val F V)
| (atm.eq t s)  := t.val F V = s.val F V

def rarity (m : nat) : atm → option nat
| (atm.rl k ts) := if k = m then some ts.length else none
| (atm.eq _ _)  := none 

def farity (m : nat) : atm → option nat
| (atm.rl k ts) := (ts.map $ trm.farity m).orelse
| (atm.eq t s)  := t.farity m <|> s.farity m 

def vocc (m : nat) : atm → Prop
| (atm.rl _ ts) := ∃ t ∈ ts, trm.vocc m t
| (atm.eq t s)  := t.vocc m ∨ s.vocc m

def replace (r u : trm) : atm → atm
| (atm.rl k ts) := atm.rl k (ts.map $ trm.replace r u)
| (atm.eq t s)  := atm.eq (trm.replace r u t) (trm.replace r u s) 

-/
end atm


inductive frm : Type
| atm : bool →  atm → frm
| bin : bool → frm → frm → frm
| qua : bool → frm → frm

local notation `+*`     := frm.atm tt
local notation `-*`     := frm.atm ff
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p

namespace frm

/-
def repr : frm → string
| (+* a)   :=          a.repr
| (-* a)   := "¬"   ++ a.repr
| (p ∨* q) := "("   ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "("   ++ p.repr ++ " ∧ " ++ q.repr ++ ")"
| (∀* p)   := "(∀ " ++ p.repr ++ ")"
| (∃* p)   := "(∃ " ++ p.repr ++ ")"

instance has_repr : has_repr frm := ⟨repr⟩

meta instance has_to_format : has_to_format frm := ⟨λ x, repr x⟩

meta def to_expr : frm → expr
| (frm.atm b a)   := expr.mk_app `(frm.atm) [b.to_expr, a.to_expr]
| (frm.bin b f g) := expr.mk_app `(frm.bin) [b.to_expr, f.to_expr, g.to_expr]
| (frm.qua b f)   := expr.mk_app `(frm.qua) [b.to_expr, f.to_expr]

def rnew : frm → nat
| (frm.atm _ a)   := a.rnew
| (frm.bin _ f g) := max f.rnew g.rnew
| (frm.qua _ f)   := f.rnew

def fnew : frm → nat
| (frm.atm _ a)   := a.fnew
| (frm.bin _ f g) := max (f.fnew) (g.fnew)
| (frm.qua _ f)   := f.fnew

def vnew : frm → nat
| (frm.atm _ a)   := a.vnew
| (frm.bin _ f g) := max f.vnew g.vnew
| (frm.qua _ f)   := f.vnew - 1

-/
def vinc : nat → nat → frm → frm
| m n (frm.atm b a)   := frm.atm b (a.vinc m n)
| m n (frm.bin b f g) := frm.bin b (f.vinc m n) (g.vinc m n)
| m n (frm.qua b f)   := frm.qua b (f.vinc (m + 1) n)

def default : frm := +* atm.default 

/-

def vdec : nat → frm → frm
| m (frm.atm b a)   := frm.atm b (a.vdec m)
| m (frm.bin b f g) := frm.bin b (f.vdec m) (g.vdec m)
| m (frm.qua b f)   := frm.qua b (f.vdec $ m + 1)


def finc : frm → frm
| (frm.atm b a)   := frm.atm b a.finc
| (frm.bin b f g) := frm.bin b f.finc g.finc
| (frm.qua b f)   := frm.qua b f.finc

def vsub : nat → trm → frm → frm
| k t (frm.atm b a)   := frm.atm b (a.vsub k t)
| k t (frm.bin b f g) := frm.bin b (f.vsub k t) (g.vsub k t)
| k t (frm.qua b f)   := frm.qua b (f.vsub (k + 1) (t.vinc 0 1))

def neg : frm → frm
| (frm.atm b a)   := frm.atm (bnot b) a
| (frm.bin b f g) := frm.bin (bnot b) f.neg g.neg
| (frm.qua b f)   := frm.qua (bnot b) f.neg

def holds (R : rls α) (F : fns α) : vas α → frm → Prop
| V (+* a)   :=   a.holds R F V
| V (-* a)   := ¬ a.holds R F V
| V (p ∨* q) := p.holds V ∨ q.holds V
| V (p ∧* q) := p.holds V ∧ q.holds V
| V (∀* p)   := ∀ x : α, p.holds (V ₀↦ x)
| V (∃* p)   := ∃ x : α, p.holds (V ₀↦ x)

def fvx (R : rls α) (F : fns α) : nat → vas α → frm → Prop
| 0       V f := f.holds R F V
| (k + 1) V f := ∀ x : α, fvx k (V ₀↦ x) f

-- def efx [inhabited α] (R : rls α) : nat → fns α → frm → Prop
-- | 0       F f := f.holds R F (Vdf α)
-- | (m + 1) F f := ∃ x : fn α, f.efx m (F ₀↦ x)
-- 
-- def erxefx [inhabited α] : nat → rls α → nat → fns α → frm → Prop
-- | 0       R m F f := f.efx R m F
-- | (k + 1) R m F f := ∃ x : rl α, f.erxefx k (R ₀↦ x) m F

def rarity_core (rdx : nat) : frm → option nat
| (frm.atm b a)   := a.rarity rdx
| (frm.bin _ f g) := f.rarity_core <|> g.rarity_core
| (frm.qua _ f)   := f.rarity_core

def rarity (rdx : nat) (f : frm) : nat :=
option.get_or_else (f.rarity_core rdx) 0

def farity_core (fdx : nat) : frm → option nat
| (frm.atm _ a)   := a.farity fdx
| (frm.bin _ f g) := f.farity_core <|> g.farity_core
| (frm.qua _ f)   := f.farity_core

def farity (fdx : nat) (f : frm) : nat :=
option.get_or_else (f.farity_core fdx) 0

def ffx [inhabited α] (R : rls α) : nat → fns α → frm → Prop
| 0       F f := f.holds R F (Vdf α)
| (m + 1) F f := ∀ x : nfn α (f.farity m), f.ffx m (F ₀↦ x.unfix)

def frxffx [inhabited α] : nat → rls α → nat → fns α → frm → Prop
| 0       R m F f := f.ffx R m F
| (k + 1) R m F f := ∀ x : nrl α (f.rarity k), f.frxffx k (R ₀↦ x.unfix) m F

def vocc : frm → nat → Prop
| (frm.atm _ a)   k := a.vocc k
| (frm.bin _ f g) k := f.vocc k ∨ g.vocc k
| (frm.qua _ f)   k := f.vocc (k + 1)

-/

def cons_qua_count : frm → nat
| (frm.qua _ f) := f.cons_qua_count + 1
| _             := 0

def F : frm → Prop
| (frm.atm _ a)   := true
| (frm.bin _ p q) := F p ∧ F q
| (frm.qua _ p)   := false

def QF : frm → Prop
| (frm.qua _ f) := QF f
| f              := F f

/-

instance F.decidable : decidable_pred F
| (frm.atm _ _)   := decidable.true
| (frm.bin _ f g) :=
  @and.decidable _ _ (F.decidable f) (F.decidable g)
| (frm.qua _ _)   := decidable.false

def AF : frm → Prop
| (∀* f) := AF f
| (∃* _) := false
| f      := F f

instance AF.decidable : decidable_pred AF
| (frm.atm _ _)   := F.decidable _
| (frm.bin _ _ _) := F.decidable _
| (∀* f)          := AF.decidable f
| (∃* f)          := decidable.false

def strip_fa : frm → frm
| (∀* f) := strip_fa f
| f      := f

-/

end frm

/-

/- Lemmas -/

variables {R R1 R2 : rls α} {F F1 F2 : fns α} {V V1 V2 : vas α}
variables {b : bool} (f f1 f2 g g1 g2 : frm)

local notation R `; ` F `; ` V ` ⊨ ` f := frm.holds R F V f

lemma holds_neg : ∀ {V : vas α} {f : frm},
  (R ; F ; V ⊨ f.neg) ↔ ¬ (R ; F ; V ⊨ f)
| _ (+* a)   := iff.refl _
| _ (-* a)   := 
  by simp only [ frm.neg, frm.holds,
       bnot, classical.not_not ]
| _ (p ∨* q) :=
  begin
    unfold frm.holds,
    rw not_or_distrib,
    apply pred_mono_2;
    apply holds_neg
  end
| _ (p ∧* q) :=
  begin
    unfold frm.holds,
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
  end
| _ (∀* p)   :=
  begin
    unfold frm.holds,
    rw @not_forall _ _ (classical.dec _) (classical.dec_pred _),
    apply exists_congr,
    intro v, apply holds_neg
  end
| _ (∃* p)   :=
  begin
    unfold frm.holds,
    rw @not_exists,
    apply forall_congr,
    intro v, apply holds_neg
  end

def ext (k : nat) (f g : nat → β) : Prop := ∀ m, f (m + k) = g m

lemma ext_zero_refl (f : nat → β) : ext 0 f f := λ _, rfl

lemma eq_of_ext_zero {f f' : nat → β} :
  ext 0 f f' → f = f' :=
by { intros h0, apply funext, intro k, apply h0 }

lemma ext_succ {k : nat} {f g : nat → β} {b : β} :
  ext k f (g ₀↦ b) → ext (k + 1) f g :=
begin
  intros h0 m,
  apply eq.trans _ (h0 (m + 1)),
  apply congr_arg,
  rw add_assoc,
  apply congr_arg _ (add_comm _ _)
end

lemma ext_assign {k : nat} {f g : nat → β} :
  ext (k + 1) f g → ext k f (g ₀↦ f k) :=
by { rintros h0 ⟨m⟩,
     { rw zero_add, refl },
     simp only [nat.succ_add, assign, (h0 m).symm],
     refl }

def forall_ext (k : nat) (f : nat → β) (p : (nat → β) → Prop) : Prop :=
∀ f' : nat → β, ext k f' f → p f'

def exists_ext (k : nat) (f : nat → β) (p : (nat → β) → Prop) : Prop :=
∃ f' : nat → β, ext k f' f ∧ p f'

local notation F `∀⟹` k := forall_ext k F
local notation F `∃⟹` k := exists_ext k F

lemma trm.val_eq_val (F : fns α) {V W : vas α} :
  ∀ t : trm, (∀ m : nat, t.vocc m → V m = W m) →
  (t.val F V = t.val F W) :=
trm.rec 
  (begin 
     intros k h0, 
     apply h0 k rfl,
   end) 
  (begin
     intros k ts ih h0,
     rw [trm.val_fn, trm.val_fn],
     apply congr_arg,
     apply trm.map_eq_map,
     intros t h1, apply ih _ h1,
     intros m h2, apply h0,
     rw trm.vocc_fn,
     refine ⟨t, h1, h2⟩
   end)

lemma atm.holds_iff_holds {l : atm} {V W : vas α} 
  (h0 : ∀ m : nat, l.vocc m → V m = W m) :
  (l.holds R F V ↔ l.holds R F W) :=
begin
  cases l with k ts t s,
  { have h1 : ts.map (λ x, x.val F V []) = ts.map (λ x, x.val F W []),
    { apply list.map_eq_map_of_forall_mem_eq,
      intros t h1,
      rw trm.val_eq_val,
      intros m h2,
      apply h0 _ ⟨t, h1, h2⟩ },
    unfold atm.holds; rw h1 },
  unfold atm.holds,
  rw [ trm.val_eq_val F t,
       trm.val_eq_val F s ];
  intros k h1; apply h0,
  { right, exact h1 },
  left, exact h1 
end

lemma holds_iff_holds  :
  ∀ f : frm, ∀ V W : vas α,
  (∀ m : nat, f.vocc m → V m = W m) →
  ((R ; F ; V ⊨ f) ↔ (R ; F ; W ⊨ f))
| (frm.atm b a) V W h0 := 
  by { cases b; unfold frm.holds;
       rw atm.holds_iff_holds h0 }
| (frm.bin b f g) V W h0 :=
  begin
    cases b;
    apply pred_mono_2;
    apply holds_iff_holds;
    intros m h1; apply h0;
    try {left, assumption};
    right; assumption
  end
| (frm.qua b f) V W h0 :=
  begin
    cases b;
    try {apply forall_congr};
    try {apply exists_congr};
    intro a; apply holds_iff_holds;
    intros m h1; cases m with m;
    try {refl}; apply h0; exact h1
  end

#exit
lemma trm.val_replace {t s : trm} (h0 : t.val F V [] = s.val F V []) : 
  ∀ r : trm, 
    (trm.replace t s tt r).val F V [] = r.val F V [] ∧ 
    (trm.replace t s ff r).val F V = r.val F V 
| (# k) :=  
  by { constructor;
       unfold trm.replace,  
       { by_cases h1 : (# k) = t,
         { rw [ if_pos (and.intro _ h1), h1, h0 ], 
           simp only [bool.coe_sort_tt] },
         rw if_neg, intro h2, exact (h1 h2.right) },
       rw if_neg, rintro ⟨⟨_⟩, _⟩ }
| ($ k) := 
  by { constructor; 
       unfold trm.replace,
       { by_cases h1 : $ k = t,
         { rw [ if_pos (and.intro _ h1), h1, h0 ],
           simp only [bool.coe_sort_tt] },
         rw if_neg, intro h2, exact (h1 h2.right) },
       rw if_neg, rintro ⟨⟨_⟩, _⟩ }
| (r & u) :=  
  by { constructor; 
       unfold trm.replace,
       { by_cases h1 : (r & u) = t,
         { rw [ if_pos (and.intro _ h1), h1, h0 ],
           simp only [bool.coe_sort_tt] },
         rw if_neg,
         { unfold trm.val,
           rw [ (trm.val_replace r).right,
                (trm.val_replace u).left ] },
         intro h2, exact (h1 h2.right) },
       rw if_neg, 
       { unfold trm.val,
         rw [ (trm.val_replace r).right,
              (trm.val_replace u).left ] },
       rintro ⟨⟨_⟩, _⟩ }

lemma atm.holds_replace {r u : trm} 
  (h0 : r.val F V [] = u.val F V []) : 
  ∀ l : atm, l.holds R F V → (l.replace r u).holds R F V 
| (atm.rl k ts) h1 := 
  by { have h3 : ((λ x, trm.val F V x []) ∘ trm.replace r u tt) = 
                  (λ x, trm.val F V x []),
       { apply funext, intro x,
         apply (trm.val_replace h0 x).left },
       unfold atm.replace, 
       unfold atm.holds,
       rw [ list.map_map, h3 ],
       apply h1 }
| (atm.eq t s) h1 := 
  by { unfold atm.replace, 
       unfold atm.holds, 
       rw [ (trm.val_replace h0 t).left,
            (trm.val_replace h0 s).left ],
       apply h1 } 

lemma trm.lt_of_vnew_le {k m : nat} :
  ∀ {t : trm}, t.vnew ≤ k → t.vocc m → m < k
| (# n) h0 h1 :=
  by { cases h1, apply nat.lt_of_succ_le h0 }
| ($ _)    h0 h1 := by cases h1
| (t & s) h0 h1 :=
  begin
    cases h1;
    apply trm.lt_of_vnew_le _ h1,
    { apply le_of_max_le_left h0 },
    apply le_of_max_le_right h0
  end

lemma atm.lt_of_vnew_le :
  ∀ {l : atm}, ∀ {k m : nat},
  l.vnew ≤ k → l.vocc m → m < k
| (atm.rl _ ts) k m h0 h1 :=
  by { rcases h1 with ⟨t, h2, h3⟩, 
       apply trm.lt_of_vnew_le _ h3,
       apply le_trans _ h0,
       apply list.le_maximum_of_mem,
       apply list.mem_map_of_mem trm.vnew h2 }
| (atm.eq t s) k m h0 h1 :=
  by { have ht := le_of_max_le_left h0,
       have hs := le_of_max_le_right h0,
       cases h1;
       apply trm.lt_of_vnew_le _ h1;
       assumption }

lemma frm.lt_of_vnew_le :
  ∀ {f : frm}, ∀ {k m : nat},
  f.vnew ≤ k → f.vocc m → m < k
| (frm.atm _ _) k m h0 h1 :=
  atm.lt_of_vnew_le h0 h1
| (frm.bin _ f g) k m h0 h1 :=
  begin
    cases h1;
    apply frm.lt_of_vnew_le _ h1,
    { apply le_of_max_le_left h0 },
    apply le_of_max_le_right h0
  end
| (frm.qua _ f) k m h0 h1 :=
  begin
    rw ← nat.succ_lt_succ_iff,
    apply @frm.lt_of_vnew_le f (k + 1) (m + 1) _ h1,
    unfold frm.vnew at h0,
    rw [← add_le_add_iff_right 1, nat.sub_add_eq_max] at h0,
    apply le_trans (le_max_left _ _) h0,
  end

lemma ffx_of_forall_fxt [inhabited α] {R : rls α} :
  ∀ {m : nat} {F : fns α} {f : frm},
  (F ∀⟹ m) (λ F', (R; F'; Vdf α ⊨ f)) → f.ffx R m F
| 0       F f h0 := h0 _ (ext_zero_refl _)
| (m + 1) F f h0 :=
  begin
    intro x,
    apply ffx_of_forall_fxt,
    intros F' h1, apply h0,
    apply ext_succ h1,
  end

lemma frxffx_of_forall_rxt [inhabited α] :
  ∀ {k : nat} {R : rls α} {m : nat} {F : fns α} {f : frm},
  (R ∀⟹ k) (λ R', (F ∀⟹ m) (λ F', R'; F'; Vdf α ⊨ f)) →
  f.frxffx k R m F
| 0 R m F f h0 :=
  by { apply ffx_of_forall_fxt,
       apply h0 _ (ext_zero_refl _) }
| (k + 1) R m F f h0 :=
  begin
    intro x,
    apply frxffx_of_forall_rxt,
    intros R' h1, apply h0,
    apply ext_succ h1
  end

lemma trm.val_vsubs_eq_of_wfc (μs : vmaps) :
  ∀ t : trm, 
    (t.wfc ff → (t.vsubs μs).val F V = t.val F (V.vsubs F μs)) ∧ 
    (t.wfc tt → (t.vsubs μs).val F V [] = t.val F (V.vsubs F μs) []) 
| (# k) := 
  by { constructor; intro h0,
       { cases h0 },
       cases h1 : μs.get k with s;
       simp only [trm.val, trm.vsubs, h1, vas.vsubs] }
| ($ k) := 
  by { constructor; intro h0; refl }
| (t & s) := 
  by constructor; intro h0;
     simp only [trm.val, trm.vsubs];
     rw [ (trm.val_vsubs_eq_of_wfc t).left h0.left,  
            (trm.val_vsubs_eq_of_wfc s).right h0.right ]
      
lemma trm.val_vsubs_eq_of_wf (μs : vmaps) :
  ∀ t : trm, t.wf → 
    (t.vsubs μs).val F V [] = t.val F (V.vsubs F μs) []
| (# k) _ := 
  by { cases h1 : μs.get k with s;
       simp only [trm.val, trm.vsubs, h1, vas.vsubs] }
| ($ k) _ := 
  by { constructor; intro h0; refl }
| (t & s) h0 :=
  by { unfold trm.vsubs,
       unfold trm.val,
       rw [ (trm.val_vsubs_eq_of_wfc _ t).left h0.left,  
            (trm.val_vsubs_eq_of_wfc _ s).right h0.right ] }

def prepend (k : nat) (f g : nat → β) : nat → β
| m := if m < k then f m else g (m - k)

lemma ext_prepend (k : nat) (f g : nat → β) :
  ext k (prepend k f g) g
| m :=
  begin
    unfold prepend,
    rw if_neg,
    { rw nat.add_sub_cancel },
    rw not_lt,
    apply nat.le_add_left,
  end

lemma forall_ext_holds_of_fvx :
  ∀ k : nat, ∀ V : vas α,
  f.fvx R F k V →
  ∀ W : vas α, ext k W V →
  (R ; F ; W ⊨ f)
| 0 V h0 W h1 :=
  begin
    have h2 : W = V,
    { apply funext h1 },
    rw h2, exact h0
  end
| (k + 1) V h0 W h1 :=
  begin
    unfold frm.fvx at h0,
    apply forall_ext_holds_of_fvx k (V ₀↦ W k) (h0 _) W,
    intro m, cases m with m,
    { rw zero_add, refl },
    rw nat.succ_add, apply h1
  end

lemma holds_of_forall_vxt_holds {k : nat} {f : frm} :
  f.vnew ≤ k → (V ∀⟹ k) (λ V', f.holds R F V') →
  ∀ W : vas α, (R ; F ; W ⊨ f) :=
  begin
    intros h0 h1 W,
    rw holds_iff_holds f W (prepend k W V) _,
    { apply h1,
      apply ext_prepend },
    intros m h2,
    unfold prepend,
    rw if_pos,
    apply frm.lt_of_vnew_le h0 h2,
  end

lemma ext_comp_of_ext_succ {k : nat} {f g : nat → β} :
  ext (k + 1) f g → ext k (f ∘ nat.succ) g :=
by { intros h0 m, rw ← (h0 m), refl }

lemma forall_vxt_succ_holds {k : nat} {f : frm} :
  (V ∀⟹ k + 1) (λ V', f.holds R F V') ↔
  (V ∀⟹ k) (λ V', (∀* f).holds R F V') :=
by { constructor; intros h0 V' h1,
     { intro a,
       apply h0 (V' ₀↦ a) h1 },
     have h2 : V' = ((V' ∘ nat.succ) ₀↦ V' 0),
     { apply funext,
       rintro ⟨m⟩; refl },
     rw h2,
     apply h0 (V' ∘ nat.succ)
       (ext_comp_of_ext_succ h1) (V' 0) }

lemma vnew_neg :
  ∀ f : frm, f.neg.vnew = f.vnew
| (frm.atm _ _)   := rfl
| (frm.bin _ f g) :=
  by simp only [frm.neg, frm.vnew,
       vnew_neg f, vnew_neg g]
| (frm.qua _ f)   :=
  by simp only [frm.neg, frm.vnew, vnew_neg f]

lemma forall_ext_zero :
  ∀ {f : frm}, (R; F; V ⊨ f) →
  (V ∀⟹ 0) (λ V', (R; F; V' ⊨ f)) :=
begin
  intros f h0 V' h1,
  have h2 : V' = V,
  { apply funext (λ k, _),
    rw ← h1 k, refl },
  rw h2, exact h0
end

lemma holds_strip_fa :
  ∀ {f : frm} {k : nat}, 
  f.AF → f.vnew ≤ k →
  (V ∀⟹ k) (λ V', (R; F; V' ⊨ f)) →
  ∀ W : vas α, (R ; F ; W ⊨ f.strip_fa)
| (frm.atm _ _) k h0 h1 h2 W :=
  begin
    unfold frm.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (frm.bin b f g) k h0 h1 h2 W :=
  begin
    unfold frm.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (∃* f) k h0 h1 h2 W := by cases h0
| (∀* f) k h0 h1 h2 W :=
  begin
    unfold frm.AF at h0,
    unfold frm.vnew at h1,
    unfold frm.strip_fa,
    rw ← forall_vxt_succ_holds at h2,
    apply holds_strip_fa h0 _ h2,
    cases f.vnew,
    { apply nat.zero_le },
    apply nat.succ_le_succ h1,
  end

lemma F_strip_fa :
  ∀ f : frm, f.AF → f.strip_fa.F
| (frm.atm _ _) h   := trivial
| (frm.bin _ f g) h := h
| (∀* f) h          := F_strip_fa f h
| (∃* f) h          := by cases h

lemma holds_bin_of_holds_bin {R' : rls α} {F' : fns α}
  {V' : vas α} {b : bool} {f g f' g' : frm} :
  (f.holds R F V → f'.holds R' F' V') →
  (g.holds R F V → g'.holds R' F' V') →
  (frm.bin b f g).holds R F V →
  (frm.bin b f' g').holds R' F' V' :=
begin
  intros h0 h1 h2, cases b,
  { refine ⟨h0 h2.left, h1 h2.right⟩ },
  cases h2,
  { left, apply h0 h2 },
  right, apply h1 h2
end


-/
end vampire