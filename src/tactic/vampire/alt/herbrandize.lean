import tactic.vampire.alt.form

namespace alt

local notation `#`      := term.fn
local notation t `&t` s := term.tp t s
local notation t `&v` k := term.vp t k

local notation `$`      := atom.rl
local notation a `^t` t := atom.tp a t
local notation a `^v` t := atom.vp a t

local notation `-*` := form.lit ff
local notation `+*` := form.lit tt
local notation p `∨*` q        := form.bin tt p q
local notation p `∧*` q        := form.bin ff p q
local notation `∃*`            := form.qua tt
local notation `∀*`            := form.qua ff

def forall_locs : form → nat → list nat
| (form.lit _ _)   _ := []
| (form.bin _ _ _) _ := []
| (∃* f) k           := forall_locs f (k + 1)
| (∀* f) k           := k :: forall_locs f k

def herbrand_term : nat → term
| 0       := # 0
| (k + 1) := (herbrand_term k) &v (k + 1)

def herbrandize_one (ht : term) : nat → form → form
| 0       (∀* f) := (f.incr_fdx.subst 0 ht).decr_idx 0
| (k + 1) (∃* f) := ∃* (herbrandize_one k f)
| _       _      := form.default

def herbrandize_many : list nat → form → form
| []        f := f
| (l :: ls) f :=
  herbrandize_many ls (herbrandize_one (herbrand_term l) l f)

def herbrandize (f : form) : form :=
herbrandize_many (forall_locs f 0) f

def ex_locs : form → nat → list nat
| (form.lit _ _)   _ := []
| (form.bin _ _ _) _ := []
| (∀* f) k           := ex_locs f (k + 1)
| (∃* f) k           := k :: ex_locs f k

def skolem_term : nat → term
| 0       := # 0
| (k + 1) := (skolem_term k) &v (k + 1)

def skolemize_one (st : term) : nat → form → form
| (k + 1) (∀* f) := ∀* (skolemize_one k f)
| 0       (∃* f) := (f.incr_fdx.subst 0 st).decr_idx 0
| _       _      := form.default

def skolemize_many : list nat → form → form
| []        f := f
| (l :: ls) f :=
  skolemize_many ls (skolemize_one (skolem_term l) l f)

def skolemize (f : form) : form :=
skolemize_many (forall_locs f 0) f

variables {α : Type} [inhabited α]

local notation `∀^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, forall_ext k F p) := r
local notation `∃^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, exists_ext k F p) := r
local notation R `;` F `;` V `⊨` f := form.holds R F V f

theorem holds_skolemize {R} {F} {f} :
  let ls := forall_locs f 0 in
  (R; F; Vdf α ⊨ f) →
  (∃^ F' ∷ ls.length ⇒ F, R; F'; Vdf α ⊨ skolemize f) := sorry

theorem holds_herbrandize (R) (F) (f) :
  let ls := forall_locs f 0 in
  (∀^ F' ∷ ls.length ⇒ F, R; F'; Vdf α ⊨ herbrandize f) →
  (R; F; Vdf α ⊨ f) := sorry

#exit
theorem herbrandizes_frxffx_imp :
  ∀ (k : nat) (R : rls α) (m : nat) (F : fns α) (f : form),
  let ls := forall_locs f 0 in
  (herbrandize f).frxffx k R (fn + ls.length) F →
  (∀^ R' ∷ k ⇒ R, ∀^ F' ∷ m ⇒ F, R'; F'; Vdf α ⊨ f) := sorry

  #exit
(list.product

def foo : form := ∃* (∀* (∀* (+* ((($ 0 ^v 0) ^v 1) ^v 2))))

def ls := (forall_locs foo 0)
#eval (herbrandizes ls foo)

#exit

def ht := (herbrand_term 1)

def bar : atom := ((($ 0 ^v 0) ^t (# 1 &v 1)) ^v 1)
def bar' : atom := (($ 0 ^v 0) ^t (# 1 &v 1))

def quz : term := (# 1 &v 1)

#eval quz
#eval term.subst 0 ht quz

#exit
#eval (# 1)
#eval (# 1).subst 0 ht
#exit

-- #eval herbrandize (herbrand_term 1) 0 (∀* (+* ((($ 0 ^v 0) ^t (# 0 &v 1)) ^v 1)))
#eval (+* ((($ 0 ^v 0) ^t (# 0 &v 1)) ^v 1)).incr_fdx
#eval (+* ((($ 0 ^v 0) ^t (# 0 &v 1)) ^v 1)).incr_fdx.subst 0 ht

 #exit
#eval (+* ((($ 0 ^v 0) ^t (# 0 &v 1)) ^v 1)).incr_fdx.subst 0 ht

#eval herbrandize (herbrand_term 1) 1 (herbrandize (herbrand_term 1) 1 foo)

#exit
#eval (herbrandize (herbrand_term 1) 1 foo).incr_fdx

#exit


end vampire
