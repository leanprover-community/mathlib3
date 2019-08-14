import tactic.vampire.misc
import logic.basic
import data.bool
import data.nat.basic
import algebra.order_functions

namespace vampire

variables {α β : Type}

def rl  (α : Type) : Type := list α → Prop
def fn  (α : Type) : Type := list α → α
def rls (α : Type) : Type := nat → rl α
def fns (α : Type) : Type := nat → fn α
def vas (α : Type) : Type := nat → α

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

inductive term : Type
| fn : nat  → term
| tp : term → term → term
| vp : term → nat  → term

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

def mapping  : Type := nat × term
def mappings : Type := list mapping

def mappings.get (k : nat) : mappings → option term
| []             := none
| ((m, t) :: μs) := if k = m then some t else mappings.get μs

namespace term

def repr_core : term → string
| (# k)    := "F" ++ k.to_subs
| (t &t s) := t.repr_core ++ " (" ++ s.repr_core ++ ")"
| (t &v k) := t.repr_core ++ " X" ++ k.to_subs

def repr (t : term) : string :=
"(" ++ t.repr_core ++ ")"

instance has_repr : has_repr term := ⟨repr⟩

meta def to_expr : term → expr
| (term.fn k)    := expr.mk_app `(term.fn) [k.to_expr]
| (term.tp t s) := expr.mk_app `(term.tp) [t.to_expr, s.to_expr]
| (term.vp t k) := expr.mk_app `(term.vp) [t.to_expr, k.to_expr]

def vnew : term → nat
| (# k)    := 0
| (t &t s) := max t.vnew s.vnew
| (t &v k) := max t.vnew (k + 1)

def fnew : term → nat
| (# k)    := k + 1
| (t &t s) := max t.fnew s.fnew
| (t &v k) := t.fnew

def vinc (m : nat) : term → term
| (# k)    := # k
| (t &t s) := t.vinc &t s.vinc
| (t &v k) := t.vinc &v (if k < m then k else k + 1)

def finc : term → term
| (# k)    := # (k + 1)
| (t &t s) := t.finc &t s.finc
| (t &v k) := t.finc &v k

def vdec (m : nat) : term → term
| (# k)    := # k
| (t &t s) := t.vdec &t s.vdec
| (t &v k) := t.vdec &v (if m < k then k - 1 else k)

def subst (k : nat) (t : term) : term → term
| (# m)    := # m
| (s &t r) := s.subst &t r.subst
| (s &v m) := if k = m then s.subst &t t else s.subst &v m

def substs (μ : mappings) : term → term
| (# k)    := # k
| (t &t s) := t.substs &t s.substs
| (t &v k) :=
  match μ.get k with
  | none     := t.substs &v k
  | (some s) := t.substs &t s
  end

def val (F : fns α) (V : vas α) : term → (list α → α)
| (# k)    := F k
| (t &t s) := t.val ∘ list.cons (s.val [])
| (t &v k) := t.val ∘ list.cons (V k)

def farity (fdx : nat) : nat → term → option nat
| acc (# k)    := if k = fdx then some acc else none
| acc (t &t s) := t.farity (acc + 1) <|> s.farity 0
| acc (t &v _) := t.farity $ acc + 1

def vocc (k : nat) : term → Prop
| (# _)    := false
| (t &t s) := (t.vocc) ∨ (s.vocc)
| (t &v m) := t.vocc ∨ m = k

def vinc_zeroes : nat → term → term
| 0       t := t
| (k + 1) t := (vinc_zeroes k t).vinc 0

end term

def vas.substs (F : fns α) (μ : mappings) (V : vas α) (k : nat) : α :=
match μ.get k with
| none     := V k
| (some t) := t.val F V []
end

inductive atom : Type
| rl : nat  → atom
| tp : atom → term → atom
| vp : atom → nat  → atom

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

namespace atom

def vnew : atom → nat
| ($ k)    := 0
| (a ^t t) := max a.vnew t.vnew
| (a ^v k) := max a.vnew (k + 1)

def rnew : atom → nat
| ($ k)    := k + 1
| (a ^t _) := a.rnew
| (a ^v _) := a.rnew

def fnew : atom → nat
| ($ k)    := 0
| (a ^t t) := max a.fnew t.fnew
| (a ^v _) := a.fnew

def repr_core : atom → string
| ($ k)    := "R" ++ k.to_subs
| (a ^t t) := a.repr_core ++ " " ++ t.repr
| (a ^v k) := a.repr_core ++ " X" ++ k.to_subs

def repr (a : atom) : string :=
"(" ++ a.repr_core ++ ")"

instance has_repr : has_repr atom := ⟨repr⟩

meta def to_expr : atom → expr
| ($ k)    := expr.mk_app `(atom.rl) [k.to_expr]
| (a ^t t) := expr.mk_app `(atom.tp) [a.to_expr, t.to_expr]
| (a ^v k) := expr.mk_app `(atom.vp) [a.to_expr, k.to_expr]

def finc : atom → atom
| ($ k)    := $ k
| (a ^t t) := a.finc ^t t.finc
| (a ^v k) := a.finc ^v k

def vinc (m : nat) : atom → atom
| ($ k)    := $ k
| (a ^t t) := a.vinc ^t (t.vinc m)
| (a ^v k) := a.vinc ^v (if k < m then k else k + 1)

def vdec (m : nat) : atom → atom
| ($ k)    := $ k
| (a ^t t) := a.vdec ^t (t.vdec m)
| (a ^v k) := a.vdec ^v (if m < k then k - 1 else k)

def subst (k : nat) (t : term) : atom → atom
| ($ m)    := $ m
| (a ^t s) := a.subst ^t (term.subst k t s)
| (a ^v m) := if k = m then a.subst ^t t else a.subst ^v m

def substs (μs : mappings) : atom → atom
| ($ k)    := $ k
| (a ^t t) := a.substs ^t (t.substs μs)
| (a ^v k) :=
  match μs.get k with
  | none     := a.substs ^v k
  | (some s) := a.substs ^t s
  end

def val (R : rls α) (F : fns α) (V : vas α) : atom → (list α → Prop)
| ($ k)    := R k
| (a ^t t) := a.val ∘ list.cons (t.val F V [])
| (a ^v k) := a.val ∘ list.cons (V k)

def rarity (rdx : nat) : atom → option nat
| ($ k)    := if k = rdx then some 0 else none
| (a ^t _) := nat.succ <$> a.rarity
| (a ^v _) := nat.succ <$> a.rarity

def farity (fdx : nat) : atom → option nat
| ($ k)    := none
| (a ^t t) := a.farity <|> t.farity fdx 0
| (a ^v _) := a.farity

def vocc (k : nat) : atom → Prop
| ($ _)    := false
| (a ^t t) := a.vocc ∨ t.vocc k
| (a ^v m) := a.vocc ∨ m = k

end atom

inductive lit : Type
| atom : bool → atom → lit
| eq   : bool → term → term → lit

local notation `-*`     := lit.atom ff
local notation `+*`     := lit.atom tt
local notation t `=*` s := lit.eq tt t s
local notation t `≠*` s := lit.eq ff t s

namespace lit

def repr : lit → string
| (-* a)   := "¬" ++ a.repr
| (+* a)   := a.repr
| (t =* s) := t.repr ++ " = " ++ s.repr
| (t ≠* s) := t.repr ++ " ≠ " ++ s.repr

meta def to_expr : lit → expr
| (lit.atom b a) := expr.mk_app `(lit.atom) [b.to_expr, a.to_expr]
| (lit.eq b t s) := expr.mk_app `(lit.eq) [b.to_expr, t.to_expr, s.to_expr]

def rnew : lit → nat
| (lit.atom _ a) := a.rnew
| (lit.eq _ _ _) := 0

def fnew : lit → nat
| (lit.atom _ a) := a.fnew
| (lit.eq _ t s) := max t.fnew s.fnew

def vnew : lit → nat
| (lit.atom _ a) := a.vnew
| (lit.eq _ t s) := max t.vnew s.vnew

def finc : lit → lit
| (lit.atom b a) := lit.atom b a.finc
| (lit.eq b t s) := lit.eq b t.finc s.finc

def vinc (k : nat) : lit → lit
| (lit.atom b a) := lit.atom b (a.vinc k)
| (lit.eq b t s) := lit.eq b (t.vinc k) (s.vinc k)

def vdec (k : nat) : lit → lit
| (lit.atom b a) := lit.atom b (a.vdec k)
| (lit.eq b t s) := lit.eq b (t.vdec k) (s.vdec k)

def subst (k : nat) (r : term) : lit → lit
| (lit.atom b a) := lit.atom b (a.subst k r)
| (lit.eq b t s) := lit.eq b (term.subst k r t) (term.subst k r s)

def not : lit → lit
| (lit.atom b a) := lit.atom (bnot b) a
| (lit.eq b t s) := lit.eq (bnot b) t s


def holds (R : rls α) (F : fns α) (V : vas α) : lit → Prop
| (+* a)   :=   (a.val R F V [])
| (-* a)   := ¬ (a.val R F V [])
| (t =* s) :=   (t.val F V []) = (s.val F V [])
| (t ≠* s) := ¬ (t.val F V []) = (s.val F V [])

def rarity (k : nat) : lit → option nat
| (lit.atom b a) := a.rarity k
| (lit.eq b t s) := none

def farity (k : nat) : lit → option nat
| (lit.atom b a) := a.farity k
| (lit.eq b t s) := t.farity k 0 <|> s.farity k 0

def vocc (k : nat) : lit → Prop
| (lit.atom b a) := a.vocc k
| (lit.eq b t s) := t.vocc k ∨ s.vocc k

def default : lit := +* ($ 0)

def substs (μ : mappings) : lit → lit
| (lit.atom b a) := lit.atom b (a.substs μ)
| (lit.eq b t s) := lit.eq b (t.substs μ) (s.substs μ)

instance has_repr : has_repr lit := ⟨repr⟩

meta instance has_to_format : has_to_format lit := ⟨λ x, repr x⟩

end lit

inductive form : Type
| lit : lit → form
| bin : bool → form → form → form
| qua : bool → form → form

local notation `⟪` l `⟫` := form.lit l
local notation p `∨*` q  := form.bin tt p q
local notation p `∧*` q  := form.bin ff p q
local notation `∃*` p    := form.qua tt p
local notation `∀*` p    := form.qua ff p

namespace form

def repr : form → string
| ⟪l⟫      := l.repr
| (p ∨* q) := "(" ++ p.repr ++ " ∨ " ++ q.repr ++ ")"
| (p ∧* q) := "(" ++ p.repr ++ " ∧ " ++ q.repr ++ ")"
| (∀* p)   := "(∀ " ++ p.repr ++ ")"
| (∃* p)   := "(∃ " ++ p.repr ++ ")"

instance has_repr : has_repr form := ⟨repr⟩

meta instance has_to_format : has_to_format form := ⟨λ x, repr x⟩

meta def to_expr : form → expr
| (form.lit l)     := expr.mk_app `(form.lit) [l.to_expr]
| (form.bin b f g) := expr.mk_app `(form.bin) [b.to_expr, f.to_expr, g.to_expr]
| (form.qua b f)   := expr.mk_app `(form.qua) [b.to_expr, f.to_expr]

def rnew : form → nat
| (form.lit l)     := l.rnew
| (form.bin _ f g) := max f.rnew g.rnew
| (form.qua _ f)   := f.rnew

def fnew : form → nat
| (form.lit l)     := l.fnew
| (form.bin _ f g) := max (f.fnew) (g.fnew)
| (form.qua _ f)   := f.fnew

def vnew : form → nat
| (form.lit l)     := l.vnew
| (form.bin _ f g) := max f.vnew g.vnew
| (form.qua _ f)   := f.vnew - 1

def vinc : nat → form → form
| m (form.lit l)     := form.lit (l.vinc m)
| m (form.bin b f g) := form.bin b (f.vinc m) (g.vinc m)
| m (form.qua b f)   := form.qua b (f.vinc $ m + 1)

def vdec : nat → form → form
| m (form.lit l)     := form.lit (l.vdec m)
| m (form.bin b f g) := form.bin b (f.vdec m) (g.vdec m)
| m (form.qua b f)   := form.qua b (f.vdec $ m + 1)

def default : form := ⟪ lit.default ⟫

def finc : form → form
| (form.lit l)     := form.lit l.finc
| (form.bin b f g) := form.bin b f.finc g.finc
| (form.qua b f)   := form.qua b f.finc

def subst : nat → term → form → form
| k t (form.lit l)     := form.lit (l.subst k t)
| k t (form.bin b f g) := form.bin b (f.subst k t) (g.subst k t)
| k t (form.qua b f)   := form.qua b (f.subst (k + 1) (t.vinc 0))

def neg : form → form
| (form.lit l)     := form.lit l.not
| (form.bin b f g) := form.bin (bnot b) f.neg g.neg
| (form.qua b f)   := form.qua (bnot b) f.neg

def tautology : form := ⟪+* ($ 0)⟫ ∨* ⟪-* ($ 0)⟫

def holds (R : rls α) (F : fns α) : vas α → form → Prop
| V ⟪ l ⟫    := l.holds R F V
| V (p ∨* q) := p.holds V ∨ q.holds V
| V (p ∧* q) := p.holds V ∧ q.holds V
| V (∀* p)   := ∀ x : α, p.holds (V ₀↦ x)
| V (∃* p)   := ∃ x : α, p.holds (V ₀↦ x)

def fvx (R : rls α) (F : fns α) : nat → vas α → form → Prop
| 0       V f := f.holds R F V
| (k + 1) V f := ∀ x : α, fvx k (V ₀↦ x) f

def efx [inhabited α] (R : rls α) : nat → fns α → form → Prop
| 0       F f := f.holds R F (Vdf α)
| (m + 1) F f := ∃ x : fn α, f.efx m (F ₀↦ x)

def erxefx [inhabited α] : nat → rls α → nat → fns α → form → Prop
| 0       R m F f := f.efx R m F
| (k + 1) R m F f := ∃ x : rl α, f.erxefx k (R ₀↦ x) m F

def rarity_core (rdx : nat) : form → option nat
| (form.lit l)     := l.rarity rdx
| (form.bin _ f g) := f.rarity_core <|> g.rarity_core
| (form.qua _ f)   := f.rarity_core

def rarity (rdx : nat) (f : form) : nat :=
option.get_or_else (f.rarity_core rdx) 0

def farity_core (fdx : nat) : form → option nat
| (form.lit l)     := l.farity fdx
| (form.bin _ f g) := f.farity_core <|> g.farity_core
| (form.qua _ f)   := f.farity_core

def farity (fdx : nat) (f : form) : nat :=
option.get_or_else (f.farity_core fdx) 0

def ffx [inhabited α] (R : rls α) : nat → fns α → form → Prop
| 0       F f := f.holds R F (Vdf α)
| (m + 1) F f := ∀ x : nfn α (f.farity m), f.ffx m (F ₀↦ x.unfix)

def frxffx [inhabited α] : nat → rls α → nat → fns α → form → Prop
| 0       R m F f := f.ffx R m F
| (k + 1) R m F f := ∀ x : nrl α (f.rarity k), f.frxffx k (R ₀↦ x.unfix) m F

def vocc : form → nat → Prop
| (form.lit l)     k := l.vocc k
| (form.bin _ f g) k := f.vocc k ∨ g.vocc k
| (form.qua _ f)   k := f.vocc (k + 1)

def cons_qua_count : form → nat
| (form.qua _ f) := f.cons_qua_count + 1
| _              := 0

def F : form → Prop
| (form.lit _)     := true
| (form.bin _ p q) := F p ∧ F q
| (form.qua _ p)   := false

def QF : form → Prop
| (form.qua _ f) := QF f
| f              := F f

instance F.decidable : decidable_pred F
| (form.lit _)     := decidable.true
| (form.bin _ f g) :=
  @and.decidable _ _ (F.decidable f) (F.decidable g)
| (form.qua _ _)   := decidable.false

def AF : form → Prop
| (∀* f) := AF f
| (∃* _) := false
| f      := F f

instance AF.decidable : decidable_pred AF
| (form.lit _)     := F.decidable _
| (form.bin _ _ _) := F.decidable _
| (∀* f)           := AF.decidable f
| (∃* f)           := decidable.false

def strip_fa : form → form
| (∀* f) := strip_fa f
| f      := f

end form

/- Lemmas -/

variables {R R1 R2 : rls α} {F F1 F2 : fns α} {V V1 V2 : vas α}
variables {b : bool} (f f1 f2 g g1 g2 : form)

local notation R `; ` F `; ` V ` ⊨ ` f := form.holds R F V f

lemma lit.holds_not :
  ∀ {l : lit}, (l.not.holds R F V) ↔ ¬ (l.holds R F V)
| (lit.atom b a):=
  by cases b;
     simp only [classical.not_not, lit.not,
       lit.holds, bool.bnot_true, bool.bnot_false]
| (lit.eq b t s):=
  by cases b;
     simp only [classical.not_not, lit.not,
       lit.holds, bool.bnot_true, bool.bnot_false]

lemma holds_neg : ∀ {V : vas α} {f : form},
  (R ; F ; V ⊨ f.neg) ↔ ¬ (R ; F ; V ⊨ f)
| V (form.lit l) := lit.holds_not
| M (p ∨* q) :=
  begin
    unfold form.holds,
    rw not_or_distrib,
    apply pred_mono_2;
    apply holds_neg
  end
| M (p ∧* q) :=
  begin
    unfold form.holds,
    rw @not_and_distrib _ _ (classical.dec _),
    apply pred_mono_2; apply holds_neg
  end
| M (∀* p)   :=
  begin
    unfold form.holds,
    rw @not_forall _ _ (classical.dec _) (classical.dec_pred _),
    apply exists_congr,
    intro v, apply holds_neg
  end
| M (∃* p)   :=
  begin
    unfold form.holds,
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

local notation `∀^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, forall_ext k F p) := r

def exists_ext (k : nat) (f : nat → β) (p : (nat → β) → Prop) : Prop :=
∃ f' : nat → β, ext k f' f ∧ p f'

local notation `∃^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, exists_ext k F p) := r

lemma term.val_eq_val (V W : vas α) :
  ∀ t : term, (∀ m : nat, t.vocc m → V m = W m) →
  (t.val F V = t.val F W)
| (# _)    _  := rfl
| (t &t s) h0 :=
  begin
    unfold term.val,
    rw [term.val_eq_val t _, term.val_eq_val s _];
    intros m h1; apply h0,
    { right, exact h1 },
    left, exact h1
  end
| (t &v m) h0 :=
  begin
    unfold term.val,
    rw [term.val_eq_val t _, h0 m (or.inr rfl)],
    intros n h1, apply h0,
    left, exact h1
  end

lemma atom.val_eq_val (R) (F) (V W : vas α) :
  ∀ a : atom, (∀ m : nat, a.vocc m → V m = W m) →
  (a.val R F V = a.val R F W)
| ($ _)    _  := rfl
| (a ^t t) h0 :=
  begin
    unfold atom.val,
    rw [atom.val_eq_val a _, term.val_eq_val V W t _];
    intros m h1; apply h0,
    { right, exact h1 },
    left, exact h1
  end
| (a ^v m) h0 :=
  begin
    unfold atom.val,
    rw [atom.val_eq_val a _, h0 m (or.inr rfl)],
    intros n h1, apply h0,
    left, exact h1
  end

lemma lit.holds_iff_holds {l : lit} {V W : vas α} :
  (∀ m : nat, l.vocc m → V m = W m) →
  (l.holds R F V ↔ l.holds R F W) :=
begin
  intro h0,
  cases l with b a b t s;
  cases b;
  unfold lit.holds;
  try { rw atom.val_eq_val, exact h0 };
  { rw [ term.val_eq_val V W t,
         term.val_eq_val V W s ];
    intros k h1; apply h0,
    { right, exact h1 },
    left, exact h1 },
end

lemma holds_iff_holds  :
  ∀ f : form, ∀ V W : vas α,
  (∀ m : nat, f.vocc m → V m = W m) →
  ((R ; F ; V ⊨ f) ↔ (R ; F ; W ⊨ f))
| (form.lit a) V W h0 := lit.holds_iff_holds h0
| (form.bin b f g) V W h0 :=
  begin
    cases b;
    apply pred_mono_2;
    apply holds_iff_holds;
    intros m h1; apply h0;
    try {left, assumption};
    right; assumption
  end
| (form.qua b f) V W h0 :=
  begin
    cases b;
    try {apply forall_congr};
    try {apply exists_congr};
    intro a; apply holds_iff_holds;
    intros m h1; cases m with m;
    try {refl}; apply h0; exact h1
  end

lemma term.lt_of_vnew_le (k m : nat) :
  ∀ t : term, t.vnew ≤ k →
  t.vocc m → m < k
| (# _)    h0 h1 := by cases h1
| (t &t s) h0 h1 :=
  begin
    cases h1;
    apply term.lt_of_vnew_le _ _ h1,
    { apply le_of_max_le_left h0 },
    apply le_of_max_le_right h0
  end
| (t &v n) h0 h1 :=
  begin
    cases h1,
    { apply term.lt_of_vnew_le _ _ h1,
      apply le_of_max_le_left h0 },
    rw ← h1,
    apply nat.lt_of_succ_le (le_of_max_le_right h0),
  end

lemma atom.lt_of_vnew_le (k m : nat) :
  ∀ a : atom, a.vnew ≤ k →
  a.vocc m → m < k
| ($ _)    h0 h1 := by cases h1
| (a ^t t) h0 h1 :=
  begin
    cases h1,
    { apply atom.lt_of_vnew_le _ _ h1,
      apply le_of_max_le_left h0 },
    apply term.lt_of_vnew_le _ _ _ _ h1,
    apply le_of_max_le_right h0
  end
| (a ^v n) h0 h1 :=
  begin
    cases h1,
    { apply atom.lt_of_vnew_le _ _ h1,
      apply le_of_max_le_left h0 },
    rw ← h1,
    apply nat.lt_of_succ_le (le_of_max_le_right h0),
  end

lemma lit.lt_of_vnew_le :
  ∀ {l : lit}, ∀ {k m : nat},
  l.vnew ≤ k → l.vocc m → m < k
| (lit.atom b a) k m h0 h1 :=
  atom.lt_of_vnew_le _ _ _ h0 h1
| (lit.eq b t s) k m h0 h1 :=
  by { have ht := le_of_max_le_left h0,
       have hs := le_of_max_le_right h0,
       cases h1;
       apply term.lt_of_vnew_le _ _ _ _ h1;
       assumption }

lemma form.lt_of_vnew_le :
  ∀ {f : form}, ∀ {k m : nat},
  f.vnew ≤ k → f.vocc m → m < k
| (form.lit l) k m h0 h1 :=
  lit.lt_of_vnew_le h0 h1
| (form.bin _ f g) k m h0 h1 :=
  begin
    cases h1;
    apply form.lt_of_vnew_le _ h1,
    { apply le_of_max_le_left h0 },
    apply le_of_max_le_right h0
  end
| (form.qua _ f) k m h0 h1 :=
  begin
    rw ← nat.succ_lt_succ_iff,
    apply @form.lt_of_vnew_le f (k + 1) (m + 1) _ h1,
    unfold form.vnew at h0,
    rw [← add_le_add_iff_right 1, nat.sub_add_eq_max] at h0,
    apply le_trans (le_max_left _ _) h0,
  end

lemma ffx_of_forall_fxt [inhabited α] {R : rls α} :
  ∀ {m : nat} {F : fns α} {f : form},
  (∀^ F' ∷ m ⇒ F, (R; F'; Vdf α ⊨ f)) →
  f.ffx R m F
| 0       F f h0 := h0 _ (ext_zero_refl _)
| (m + 1) F f h0 :=
  begin
    intro x,
    apply ffx_of_forall_fxt,
    intros F' h1, apply h0,
    apply ext_succ h1,
  end

lemma frxffx_of_forall_rxt [inhabited α] :
  ∀ {k : nat} {R : rls α} {m : nat} {F : fns α} {f : form},
  (∀^ R' ∷ k ⇒ R, ∀^ F' ∷ m ⇒ F, (R'; F'; Vdf α ⊨ f)) →
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

lemma term.val_substs (μs : mappings) :
  ∀ t : term, (t.substs μs).val F V = t.val F (V.substs F μs)
| (# k)   := rfl
| (t &t s) :=
  by simp only [term.val, term.substs, term.val_substs]
| (t &v k) :=
  by cases h1 : μs.get k with s;
    { simp only [term.val, term.substs, h1,
        term.val_substs t, vas.substs] }

lemma atom.val_substs (μs : mappings) :
  ∀ a : atom, (a.substs μs).val R F V = a.val R F (V.substs F μs)
| ($ k)   := rfl
| (a ^t s) :=
  by simp only [atom.val, atom.substs,
       atom.val_substs, term.val_substs]
| (a ^v k) :=
  by cases h1 : μs.get k with s;
    { simp only [atom.val, atom.substs, h1,
        atom.val_substs a, vas.substs] }


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
    unfold form.fvx at h0,
    apply forall_ext_holds_of_fvx k (V ₀↦ W k) (h0 _) W,
    intro m, cases m with m,
    { rw zero_add, refl },
    rw nat.succ_add, apply h1
  end


lemma holds_of_forall_vxt_holds {k : nat} {f : form} :
  f.vnew ≤ k → (∀^ V' ∷ k ⇒ V, f.holds R F V') →
  ∀ W : vas α, (R ; F ; W ⊨ f) :=
  begin
    intros h0 h1 W,
    rw holds_iff_holds f W (prepend k W V) _,
    { apply h1,
      apply ext_prepend },
    intros m h2,
    unfold prepend,
    rw if_pos,
    apply form.lt_of_vnew_le h0 h2,
  end

lemma ext_comp_of_ext_succ {k : nat} {f g : nat → β} :
  ext (k + 1) f g → ext k (f ∘ nat.succ) g :=
by { intros h0 m, rw ← (h0 m), refl }

lemma forall_vxt_succ_holds {k : nat} {f : form} :
  (∀^ V' ∷ (k + 1) ⇒ V, f.holds R F V') ↔
  (∀^ V' ∷ k ⇒ V, (∀* f).holds R F V') :=
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
  ∀ f : form, f.neg.vnew = f.vnew
| (form.lit l) := by {cases l; refl}
| (form.bin _ f g) :=
  by simp only [form.neg, form.vnew,
       vnew_neg f, vnew_neg g]
| (form.qua _ f)   :=
  by simp only [form.neg, form.vnew, vnew_neg f]

lemma forall_ext_zero :
  ∀ {f : form}, (R; F; V ⊨ f) →
  (∀^ V' ∷ 0 ⇒ V, (R; F; V' ⊨ f)) :=
begin
  intros f h0 V' h1,
  have h2 : V' = V,
  { apply funext (λ k, _),
    rw ← h1 k, refl },
  rw h2, exact h0
end

lemma holds_strip_fa :
  ∀ {f : form} {k : nat} ,
  f.AF → f.vnew ≤ k →
  (∀^ V' ∷ k ⇒ V, (R; F; V' ⊨ f)) →
  ∀ W : vas α, (R ; F ; W ⊨ f.strip_fa)
| (form.lit l) k h0 h1 h2 W :=
  begin
    unfold form.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (form.bin b f g) k h0 h1 h2 W :=
  begin
    unfold form.strip_fa,
    apply holds_of_forall_vxt_holds h1 h2
  end
| (∃* f) k h0 h1 h2 W := by cases h0
| (∀* f) k h0 h1 h2 W :=
  begin
    unfold form.AF at h0,
    unfold form.vnew at h1,
    unfold form.strip_fa,
    rw ← forall_vxt_succ_holds at h2,
    apply holds_strip_fa h0 _ h2,
    cases f.vnew,
    { apply nat.zero_le },
    apply nat.succ_le_succ h1,
  end

lemma F_strip_fa :
  ∀ f : form, f.AF → f.strip_fa.F
| (form.lit _) h     := trivial
| (form.bin _ f g) h := h
| (∀* f) h           := F_strip_fa f h
| (∃* f) h           := by cases h

lemma holds_bin_of_holds_bin {R' : rls α} {F' : fns α}
  {V' : vas α} {b : bool} {f g f' g' : form} :
  (f.holds R F V → f'.holds R' F' V') →
  (g.holds R F V → g'.holds R' F' V') →
  (form.bin b f g).holds R F V →
  (form.bin b f' g').holds R' F' V' :=
begin
  intros h0 h1 h2, cases b,
  { refine ⟨h0 h2.left, h1 h2.right⟩ },
  cases h2,
  { left, apply h0 h2 },
  right, apply h1 h2
end

end vampire
