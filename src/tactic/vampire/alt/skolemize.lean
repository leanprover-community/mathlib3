import tactic.vampire.alt.form
import data.vector

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

--def ex_locs : pnf → nat → list nat
--| (pnf.qf _)     _ := []
--| (pnf.qua ff f) k := ex_locs f (k + 1)
--| (pnf.qua tt f) k := k :: ex_locs f k

-- def fa_count : pnf → nat
-- | (pnf.qf _)     := 0
-- | (pnf.qua ff f) := fa_count f + 1
-- | (pnf.qua tt f) := fa_count f

def ex_count : form → nat
| (form.lit _)     := 0
| (form.bin _ _ _) := 0
| (∀* f)           := ex_count f
| (∃* f)           := ex_count f + 1

def skolem_term : nat → term
| 0       := # 0
| (k + 1) := (skolem_term k) &v (k + 1)

def skolemize_one : form → nat → form
| (∀* f) k := ∀* (skolemize_one f (k + 1))
| (∃* f) k := (f.incr_fdx.subst 0 (skolem_term k)).decr_vdx 0
| _      _ := form.tautology

def skolemize_core : nat → form → form
| 0       f := f
| (k + 1) f := skolemize_core k (skolemize_one f 0)

def skolemize (f : form) : form :=
skolemize_core (ex_count f) f

variables {α : Type} [inhabited α]
variables {R : rls α} {F : fns α} {V : vas α}

local notation `∀^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, forall_ext k F p) := r
local notation `∃^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, exists_ext k F p) := r
local notation R `;` F `;` V `⊨` f := form.holds R F V f

lemma AF_of_QF :
  ∀ f : form, ex_count f = 0 → f.QF → f.AF
| (form.lit l)     h0 h1 := trivial
| (form.bin b f g) h0 h1 := h1
| (∀* f)           h0 h1 := AF_of_QF f h0 h1

lemma ex_count_decr_vdx :
  ∀ f : form, ∀ m : nat, ex_count (f.decr_vdx m) = ex_count f
| (form.lit l)     m := rfl
| (form.bin b f g) m := rfl
| (form.qua b f)   m :=
  by cases b;
     simp [ form.decr_vdx, ex_count,
       ex_count_decr_vdx _ (m + 1) ]

lemma ex_count_incr_fdx :
  ∀ f : form, ex_count f.incr_fdx = ex_count f
| (form.lit l)     := rfl
| (form.bin b f g) := rfl
| (form.qua b f)   :=
  by cases b;
     simp [ form.incr_fdx, ex_count,
       ex_count_incr_fdx f ]

lemma ex_count_subst :
  ∀ f : form, ∀ k : nat, ∀ t : term,
  ex_count (f.subst k t) = ex_count f
| (form.lit l)     k t := rfl
| (form.bin b f g) k t := rfl
| (form.qua b f)   k t :=
  by cases b;
     simp [ form.subst, ex_count,
       ex_count_subst ]
lemma ex_count_skolemize_one_eq {k : nat} :
  ∀ {f : form}, ∀ m : nat,
  ex_count f = k + 1 →
  ex_count (skolemize_one f m) = k
| (∀* f) m h0 :=
  by { unfold skolemize_one,
       apply ex_count_skolemize_one_eq (m + 1) ,
       apply h0 }
| (∃* f) m h0 :=
  begin
    unfold skolemize_one,
    unfold ex_count at h0,
    rw [ ex_count_decr_vdx,
         ex_count_subst,
         ex_count_incr_fdx,
         nat.succ_inj h0 ],
  end

local notation f `₀↦` a := assign a f

-- lemma holds_skolemize_one_aux :
--   ∀ f : form, ∀ k : nat,
--   (∀^ V' ∷ k ⇒ V, f.holds R F V') →
--   ∃ g : fn α, (skolemize_one f k).holds R (F ₀↦ g) V
-- | (form.lit _) k h0 :=
--   by { refine ⟨λ _, default α, _⟩,
--        apply classical.em }
-- | (form.bin _ _ _) k h0 :=
--   by { refine ⟨λ _, default α, _⟩,
--        apply classical.em }
-- | (∀* f) k h0 :=
--   begin
--
--
--   end
-- | (∃* f) k h0 :=  sorry

variable {β : Type}

def lassign : list β → (nat → β) → nat → β
| []        f k       := f k
| (b :: bs) f 0       := b
| (b :: bs) f (k + 1) := lassign bs f k

def vassign {k : nat} (v : vector β k) (f : nat → β) : nat → β :=
lassign v.val f

lemma ext_lassign (f : nat → β) :
  ∀ (k : nat) (l : list β),
  l.length = k → ext k (lassign l f) f
| 0       []        _  _ := rfl
| (k + 1) []        h0 _ := by cases h0
| 0       (b :: bs) h0 _ := by cases h0
| (k + 1) (b :: bs) h0 m :=
  by apply ext_lassign k bs (nat.succ_inj h0)

lemma ext_vassign {k : nat} (v : vector β k) (f : nat → β) :
  ext k (vassign v f) f :=
by { apply ext_lassign, apply v.property }

def to_fn [inhabited α] {k : nat} (f : vector α k → α) : fn α
| l := if h : l.length = k then f ⟨l, h⟩ else default α

lemma exists_eq_vassign_of_ext {k : nat} {f g : nat → α} :
  ext k f g → ∃ v : vector α k, f = vassign v g := sorry

-- def vas.skolem (k m : nat) (v : vector α k) (a : α) (V W : vas α) : Prop :=
--   (∀ m < k, V m = W m) ∧
--   (W k = a) ∧
--   (∀ m ≥ k, V m = W (k + 1))
--
--
lemma foobar {a : α} {g : fn α} {t : term}
  (h0 : (t.decr_vdx 0).val (F ₀↦ g) V [] = a) :
  ∀ {f : form}, (R ; F ; (V ₀↦ a) ⊨ f) →
  (R ; (F ₀↦ g) ; V ⊨ (f.incr_fdx.subst 0 t).decr_vdx 0) := sorry

lemma holds_skolemize_one_aux [inhabited α] {k : nat} {f : form} :
  (∀^ V' ∷ k ⇒ V, ∃ a : α, f.holds R F (V' ₀↦ a)) →
  ∃ g : fn α, ∀^ V' ∷ k ⇒ V,
    ((f.incr_fdx.subst 0 (skolem_term k)).decr_vdx 0).holds R (F ₀↦ g) V' :=
by { intro h0,
  have h1 : ∀ v : vector α k, ∃ a : α, f.holds R F ((vassign v V) ₀↦ a),
  { intro v, apply h0 (vassign v V) (ext_vassign _ _) },
  rw classical.skolem at h1,
  cases h1 with s h1,
  refine ⟨to_fn s, _⟩,
  intros V' h2,
  cases exists_eq_vassign_of_ext h2 with v h3,
  have h4 := h1 v,
  rw ← h3 at *,
  --apply foobar f V' (V' ₀↦ s v) _ h4,

}




#exit

lemma holds_skolemize_one :
  ∀ {f : form}, f.holds R F V →
  ∃ g : fn α, (skolemize_one f 0).holds R (F ₀↦ g) V :=  sorry

-- by { intros f h0, apply holds_skolemize_one_aux,
--   intros V' h1, rw eq_of_ext_zero h1, exact h0 }

lemma holds_skolemize :
  ∀ k : nat, ∀ F : fns α, ∀ f : form,
  ex_count f = k → f.holds R F V →
  (∃^ F' ∷ k ⇒ F, (skolemize_core k f).holds R F' V)
| 0       F f h0 h1 := ⟨F, ext_zero_refl _, h1⟩
| (k + 1) F f h0 h1 :=
  begin
    unfold skolemize_core,
    cases holds_skolemize_one h1 with g h2,
    rcases holds_skolemize k (F ₀↦ g) (skolemize_one f 0)
      (ex_count_skolemize_one_eq  _ h0) h2 with ⟨F', h3, h4⟩,
    refine ⟨F', _, h4⟩,
    apply ext_succ h3,
  end


  #exit
lemma holds_skolemize {f : form} :
  f.holds R F V →
  (∃^ F' ∷ (ex_count f) ⇒ F, (skolemize f).holds R F' V) :=
begin
  intro h0, unfold skolemize,
end

#exit


lemma F_decr_vdx :
  ∀ f : form, ∀ m : nat, f.F → (f.decr_vdx m).F
| (form.lit l)     m h0 := trivial
| (form.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_decr_vdx; assumption }

lemma QF_decr_vdx :
  ∀ f : form, ∀ m : nat, f.QF → (f.decr_vdx m).QF
| (form.lit l)     m h0 := trivial
| (form.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_decr_vdx; assumption }
| (form.qua b f)   m h0 := QF_decr_vdx f _ h0

lemma F_incr_fdx :
  ∀ f : form, f.F → f.incr_fdx.F
| (form.lit l)     h0 := trivial
| (form.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_incr_fdx; assumption }

lemma QF_incr_fdx :
  ∀ f : form, f.QF → (f.incr_fdx).QF
| (form.lit l)     h0 := trivial
| (form.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_incr_fdx; assumption }
| (form.qua b f)   h0 := QF_incr_fdx f h0

lemma F_subst :
  ∀ f : form, ∀ k : nat, ∀ t : term,
  f.F → (f.subst k t).F
| (form.lit l)     k t h0 := trivial
| (form.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_subst; assumption }

lemma QF_subst :
  ∀ f : form, ∀ k : nat, ∀ t : term,
  f.QF → (f.subst k t).QF
| (form.lit l)     k t h0 := trivial
| (form.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_subst; assumption }
| (form.qua b f)   k t h0 := QF_subst f _ _ h0

lemma QF_skolemize_one :
  ∀ f : form, ∀ m : nat,
  f.QF → (skolemize_one f m).QF
| (form.lit l)     m h0 := trivial
| (form.bin _ _ _) m h0 := trivial
| (∀* f)           m h0 := QF_skolemize_one f _ h0
| (∃* f)           m h0 :=
  begin
    apply QF_decr_vdx,
    apply QF_subst,
    apply QF_incr_fdx,
    exact h0
  end

lemma AF_skolemize_core :
  ∀ k : nat, ∀ {f : form},
  ex_count f = k → f.QF → (skolemize_core k f).AF
| 0       f h0 h1 := AF_of_QF _ h0 h1
| (k + 1) f h0 h1 :=
  begin
    unfold skolemize_core,
    apply AF_skolemize_core,
    { apply ex_count_skolemize_one_eq _ h0 },
    apply QF_skolemize_one _ _ h1
  end

lemma AF_skolemize {f : form} :
  f.QF → (skolemize f).AF :=
by { intro h0, unfold skolemize,
     apply AF_skolemize_core _ rfl h0 }

#exit

lemma fresh_vdx_skolemize :
  ∀ f : form, (skolemize f).fresh_vdx = f.fresh_vdx := sorry

lemma univ_skolemize {f : form} :
  (skolemize f).univ := sorry

#exit


#exit

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
