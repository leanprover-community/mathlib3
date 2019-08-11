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

@[reducible] def term.skolem_subst
  (k : nat) (s : term) (t : term) :=
(term.subst k s t.incr_fdx).vdec k

@[reducible] def atom.skolem_subst
  (k : nat) (s : term) (a : atom) :=
(a.incr_fdx.subst k s).vdec k

@[reducible] def lit.skolem_subst
  (k : nat) (s : term) (l : lit) :=
(l.incr_fdx.subst k s).vdec k

@[reducible] def form.skolem_subst
  (k : nat) (s : term) (f : form) :=
(f.incr_fdx.subst k s).vdec k

def skolemize_one : form → nat → form
| (∀* f) k := ∀* (skolemize_one f (k + 1))
| (∃* f) k := f.skolem_subst 0 (skolem_term k)  --(f.incr_fdx.subst 0 (skolem_term k)).vdec 0
| _      _ := form.tautology

def skolemize_core : nat → form → form
| 0       f := f
| (k + 1) f := skolemize_core k (skolemize_one f 0)

def skolemize (f : form) : form :=
skolemize_core (ex_count f) f

variables {α : Type}
variables {R : rls α} {F : fns α} {V : vas α}

local notation `∀^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, forall_ext k F p) := r
local notation `∃^` binders ` ∷ ` k ` ⇒ `  F `, ` r:(scoped p, exists_ext k F p) := r
local notation R `;` F `;` V `⊨` f := form.holds R F V f

lemma AF_of_QF :
  ∀ f : form, ex_count f = 0 → f.QF → f.AF
| (form.lit l)     h0 h1 := trivial
| (form.bin b f g) h0 h1 := h1
| (∀* f)           h0 h1 := AF_of_QF f h0 h1

lemma ex_count_vdec :
  ∀ f : form, ∀ m : nat, ex_count (f.vdec m) = ex_count f
| (form.lit l)     m := rfl
| (form.bin b f g) m := rfl
| (form.qua b f)   m :=
  by cases b;
     simp [ form.vdec, ex_count,
       ex_count_vdec _ (m + 1) ]

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
    unfold form.skolem_subst,
    unfold ex_count at h0,
    rw [ ex_count_vdec,
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

lemma exists_eq_lassign_of_ext :
  ∀ k : nat, ∀ f g : nat → α,
  ext k f g → ∃ l : list α, l.length = k ∧ f = lassign l g
| 0       f g h0 := ⟨[], rfl, eq_of_ext_zero h0⟩
| (k + 1) f g h0 :=
  by { cases exists_eq_lassign_of_ext k (f ∘ nat.succ) g _ with l h1,
       { refine ⟨f 0 :: l, _, _⟩,
         { simp only [list.length, h1.left] },
         apply funext, rintro ⟨m⟩,
         { refl },
         simp only [lassign, h1.right.symm] },
       apply h0 }

lemma exists_eq_vassign_of_ext {k : nat} {f g : nat → α} :
  ext k f g → ∃ v : vector α k, f = vassign v g :=
by { intro h0, cases exists_eq_lassign_of_ext _ _ _ h0 with l h1,
     refine ⟨⟨l, h1.left⟩, h1.right⟩ }

def splice (k : nat) (a : α) (W V : vas α) : Prop :=
(∀ m < k, W m = V m) ∧ W k = a ∧ (∀ m ≥ k, W (m + 1) = V m)

lemma form.skolem_subst_qua
  (b : bool) (f : form) (k : nat) (s : term) :
  (form.qua b f).skolem_subst k s =
  form.qua b (f.skolem_subst (k + 1) (s.vinc 0)) := rfl

lemma form.skolem_subst_lit
  (l : lit) (k : nat) (s : term) :
  (form.lit l).skolem_subst k s = form.lit (l.skolem_subst k s) := rfl

lemma form.skolem_subst_bin
  (b : bool) (f g : form) (k : nat) (s : term) :
  (form.bin b f g).skolem_subst k s =
  form.bin b (f.skolem_subst k s) (g.skolem_subst k s) := rfl

lemma lit.skolem_subst_neg
  (a : atom) (k : nat) (s : term) :
  (lit.neg a).skolem_subst k s = lit.neg (a.skolem_subst k s) := rfl

lemma lit.skolem_subst_pos
  (a : atom) (k : nat) (s : term) :
  (lit.pos a).skolem_subst k s = lit.pos (a.skolem_subst k s) := rfl

open nat

lemma splice_succ {k : nat} {a b : α} {W V : vas α} :
  splice k a W V → splice (k + 1) a (W ₀↦ b) (V ₀↦ b) :=
by { rintro ⟨h0, h1, h2⟩,
     constructor,
     { rintros ⟨m⟩ h3,
       { refl },
       apply h0,
       apply lt_of_succ_lt_succ h3 },
     refine ⟨h1, _⟩,
     rintros ⟨m⟩ h3,
     { cases h3 },
     apply h2,
     apply le_of_succ_le_succ h3 }

lemma holds_qua_of_holds_qua
  {R S : rls α} {F G : fns α} {V W : vas α} {b : bool} {f g : form} :
  (∀ x : α, f.holds R F (V ₀↦ x) → g.holds S G (W ₀↦ x)) →
  (form.qua b f).holds R F V →
  (form.qua b g).holds S G W :=
by { intros h0 h1, cases b,
     { intro x, apply h0 x (h1 x) },
     cases h1 with x h2,
     refine ⟨x, h0 x h2⟩ }

lemma val_vdec_succ_vinc_zero {a} {k} :
   ∀ t : term,
   ((t.vinc 0).vdec (k + 1)).val F (V ₀↦ a) =
   (t.vdec k).val F V
| (# m)    := rfl
| (t &t s) :=
  by simp only [ term.val,
      val_vdec_succ_vinc_zero t,
      val_vdec_succ_vinc_zero s,
       term.vdec, term.vinc ]
| (t &v m) :=
  by { unfold term.vinc,
       unfold term.vdec,
       unfold term.val,
       rw [ val_vdec_succ_vinc_zero t,
         if_neg (not_lt_zero _), nat.add_sub_cancel ],
       by_cases h0 : k < m,
       { cases m,
         { apply false.elim (not_lt_zero _ h0) },
         rw [ if_pos h0, if_pos (succ_lt_succ h0) ],
         refl },
       rw [ if_neg h0, if_neg (λ h1, _) ],
       { refl },
       apply h0 (lt_of_succ_lt_succ h1) }

lemma term.val_skolem_subst {x : α} {g : fn α} {s : term} :
  ∀ {t : term} {k : nat} {W V : vas α},
  splice k x W V →
  ((s.vdec k).val (F ₀↦ g) V [] = x) →
  (term.skolem_subst k s t).val (F ₀↦ g) V = t.val F W := sorry

lemma atom.val_skolem_subst
  {x : α} {y : fn α} {s : term} {k : nat} {W V : vas α} :
  ∀ {a : atom}, splice k x W V →
  ((s.vdec k).val (F ₀↦ y) V [] = x) →
  (a.skolem_subst k s).val R (F ₀↦ y) V = a.val R F W
| ($ k)    h0 h1 := rfl
| (a ^v k) h0 h1 :=
  by {


  }

#exit
| (a ^t t):=
  by simp only [ atom.skolem_subst, atom.incr_fdx,
       atom.subst, atom.val, atom.val_skolem_subst a,
       atom.vdec, term.val_skolem_subst h0 t ]

lemma holds_skolem_subst {x : α} {y : fn α} :
  ∀ {f : form} {k : nat} {s : term} {W V : vas α},
  splice k x W V →
  ((s.vdec k).val (F ₀↦ y) V [] = x) →
  (R ; F ; W ⊨ f) →
  (R ; (F ₀↦ y) ; V ⊨ f.skolem_subst k s)
| (form.lit l) k s W V h0 h1 h2 :=
  by { rw form.skolem_subst_lit,
       cases l with a;
       try { rw lit.skolem_subst_neg };
       try { rw lit.skolem_subst_pos };
       unfold form.holds;
       unfold lit.holds;
       rw atom.val_skolem_subst h0 h1;
       apply h2 }
| (form.bin b f g) k s W V h0 h1 h2 :=
  by { rw form.skolem_subst_bin,
       apply holds_bin_of_holds_bin _ _ h2;
       apply holds_skolem_subst h0 h1 }
| (form.qua b f) k s W V h0 h1 h2 :=
  by { rw form.skolem_subst_qua,
       apply holds_qua_of_holds_qua _ h2,
       intros a h3,
       apply holds_skolem_subst _ _ h3,
       { apply splice_succ h0 },
       rw val_vdec_succ_vinc_zero,
       apply h1 }

  #exit
| (# k):= rfl
| (t &t r):=
  by simp only [ term.skolem_subst, term.incr_fdx,
       term.subst, term.vdec, term.val,
       term.val_skolem_subst t, term.val_skolem_subst r ]
| (t &v k):=
  by { unfold term.skolem_subst,
       unfold term.incr_fdx,
       unfold term.subst,
       by_cases h1 : 0 = k,
       { rw if_pos h1,
         simp only [ term.skolem_subst, term.incr_fdx,
           term.subst, term.vdec, term.val,
           term.val_skolem_subst t, h0, h1.symm, assign ] },
       rw if_neg h1,
       cases k with k,
       { exact false.elim (h1 rfl) },
       unfold term.vdec,
       unfold term.val,
       rw [ if_pos (nat.zero_lt_succ _),
            term.val_skolem_subst t ],
       refl }

lemma atom.val_skolem_subst {x : α} {g : fn α} {s : term}
  (h0 : (s.vdec 0).val (F ₀↦ g) V [] = x) :
  ∀ a : atom, (a.skolem_subst s).val R (F ₀↦ g) V = a.val R F (V ₀↦ x)
| ($ k):= rfl
| (a ^t t):=
  by simp only [ atom.skolem_subst, atom.incr_fdx,
       atom.subst, atom.val, atom.val_skolem_subst a,
       atom.vdec, term.val_skolem_subst h0 t ]
| (a ^v k):=
  by { unfold atom.skolem_subst,
       unfold atom.incr_fdx,
       unfold atom.subst,
       by_cases h1 : 0 = k,
       { rw if_pos h1,
         simp only [ atom.skolem_subst, atom.incr_fdx,
           atom.subst, atom.vdec, atom.val,
           atom.val_skolem_subst a, h0, h1.symm, assign ] },
       rw if_neg h1,
       cases k with k,
       { exact false.elim (h1 rfl) },
       unfold atom.vdec,
       unfold atom.val,
       rw [ if_pos (nat.zero_lt_succ _),
            atom.val_skolem_subst a ],
       refl }

#check form.skolem_subst
lemma holds_skolem_subst {x : α} {y : fn α} {s : term}
  (h0 : (s.vdec 0).val (F ₀↦ y) V [] = x) :
  ∀ {f : form},
  (R ; F ; (V ₀↦ x) ⊨ f) →
  (R ; (F ₀↦ y) ; V ⊨ f.skolem_subst s)
| (form.lit l) h1 :=
  by { cases l with a a;
       { simp only [ form.skolem_subst,
           form.incr_fdx, form.subst,
           form.vdec, form.holds, lit.holds,
           lit.vdec, lit.subst, lit.incr_fdx,
           atom.incr_fdx ],
         simp only [form.holds, lit.holds] at h1,
         rw atom.val_skolem_subst h0, apply h1 } }
| (form.bin b f g) h1 :=
  by apply holds_bin_of_holds_bin _ _ h1;
     apply holds_skolem_subst
| (form.qua b f) h1 :=
  by {

  }


#exit
lemma to_fn_eq [inhabited α] {k : nat} (s : vector α k → α) (v : vector α k) :
  to_fn s v.val = s v :=
begin
  unfold to_fn, unfold dite,
  cases (nat.decidable_eq v.val.length k) with h0 h0,
  { exact false.elim (h0 v.property) },
  simp only [list.length, subtype.eta]
end

open nat

lemma lassign_eq_of_lt :
  ∀ {k m : nat} {l : list α} (h0 : m < k) (h1 : l.length = k),
  lassign l V m = l.nth_le m (by {rw h1, exact h0})
| 0       _ _               h0 h1 := by cases h0
| (k + 1) _ []              h0 h1 := by cases h1
| (k + 1) 0 (a :: as)       h0 h1 := rfl
| (k + 1) (m + 1) (a :: as) h0 h1 :=
  lassign_eq_of_lt (lt_of_succ_lt_succ h0) (succ_inj h1)


lemma vassign_eq_of_lt {k m : nat} (v : vector α k) (h0 : m < k) :
  vassign v V m = v.val.nth_le m (by {rw v.property, exact h0}) :=
lassign_eq_of_lt _ _

lemma list.drop_eq_cons_of_lt :
  ∀ {l : list α} {k m : nat} (h0 : m < k) (h1 : l.length = k),
  l.drop m = l.nth_le m (by {rw h1, exact h0}) :: l.drop (m + 1)
| _         0       _       h0 h1 := by cases h0
| []        (k + 1) _       _  h1 := by cases h1
| (a :: as) (k + 1) 0       h0 h1 := rfl
| (a :: as) (k + 1) (m + 1) h0 h1 :=
  begin
    simp only [list.drop, list.nth_le],
    apply list.drop_eq_cons_of_lt,
    { apply lt_of_succ_lt_succ h0 },
    apply succ_inj h1,
  end

lemma val_vdec_zero_skolem_term [inhabited α]
  {k : nat} (F : fns α) (V : vas α) (s : vector α k → α) {v : vector α k} :
  ∀ m : nat, ∀ as : list α, m ≤ k → v.val.drop m = as →
  ((skolem_term m).vdec 0).val (F ₀↦ to_fn s) (vassign v V) as = s v
| 0       as hle h0 :=
  by simp only [ list.drop, skolem_term, term.val,
       term.vdec, assign, h0.symm, to_fn_eq ]
| (m + 1) as h0 h1 :=
  begin
    have : ((skolem_term m).vdec 0).val
      (F ₀↦ to_fn s) (vassign v V) (vassign v V m :: as) = s v,
    { apply val_vdec_zero_skolem_term m _ (le_trans (le_succ _) h0),
    rw [list.drop_eq_cons_of_lt, vassign_eq_of_lt, h1],
    rwa succ_le_iff at h0 },
    exact this
  end

lemma list.drop_eq_nil :
  ∀ {l : list α}, ∀ {k : nat},
  l.length = k → l.drop k = [] := sorry

lemma holds_skolemize_one_aux [inhabited α] {k : nat} {f : form} :
  (∀^ V' ∷ k ⇒ V, ∃ a : α, f.holds R F (V' ₀↦ a)) →
  ∃ g : fn α, ∀^ V' ∷ k ⇒ V,
    ((f.incr_fdx.subst 0 (skolem_term k)).vdec 0).holds R (F ₀↦ g) V' :=
by { intro h0,
     have h1 : ∀ v : vector α k, ∃ a : α, f.holds R F ((vassign v V) ₀↦ a),
     { intro v, apply h0 (vassign v V) (ext_vassign _ _) },
     rw classical.skolem at h1,
     cases h1 with s h1,
     refine ⟨to_fn s, _⟩,
     intros V' h2,
     cases exists_eq_vassign_of_ext h2 with v h3,
     rw h3,
     have h5 := val_vdec_zero_skolem_term F V s k []
       (le_refl _) (list.drop_eq_nil v.property),
     apply holds_vdec_zero h5 (h1 v) }

def AE : form → Prop
| (∀* f) := AE f
| (∃* f) := true
| _      := false

def AxE (f : form) : nat → form
| 0       := ∃* f
| (k + 1) := ∀* (AxE k)

def Ax (f : form) : nat → form
| 0       := f
| (k + 1) := ∀* (Ax k)

lemma exists_kernel_of_AE :
  ∀ f : form, AE f → ∃ g : form, ∃ k : nat, f = AxE g k := sorry

lemma holds_AxE_imp :
  ∀ k : nat, ∀ V : vas α, ∀ f : form, ((AxE f k).holds R F V) →
  (∀^ V' ∷ k ⇒ V, ∃ a : α, f.holds R F (V' ₀↦ a))
| 0 V f h0 :=
  by { intros V' h1, rw eq_of_ext_zero h1, apply h0 }
| (k + 1) V f h0 :=
  by { intros V' h1,
       apply holds_AxE_imp k _ f (h0 (V' k)) V',
       intro m, cases m,
       { simp only [zero_add, assign] },
       simp only [assign, (h1 m).symm, succ_add],
       refl }

lemma holds_skolemize_one_of_not_AE :
  ∀ f : form, ¬ AE f →
  ∀ R : rls α, ∀ F : fns α, ∀ V : vas α, ∀ k : nat,
  (skolemize_one f k).holds R F V
| (∀* f) h0 R F V k :=
  by { unfold skolemize_one, intro a,
       apply holds_skolemize_one_of_not_AE f h0 }
| (∃* f) h0 R F V k := false.elim (h0 trivial)
| (form.lit _)     h0 R F V k := classical.em _
| (form.bin _ _ _) h0 R F V k := classical.em _


lemma skolemize_one_AxE (f : form) :
  ∀ k m : nat, skolemize_one (AxE f k) m =
  Ax ((f.incr_fdx.subst 0 (skolem_term (k + m))).vdec 0) k
| 0 m := by { rw zero_add, refl }
| (k + 1) m :=
  by { simp only [ AxE, skolemize_one, Ax,
         skolemize_one_AxE k (m + 1), succ_add ],
    refine ⟨rfl, rfl⟩ }

-- lemma holds_skolemize_one_AxE' (x : fn α) :
--   ∀ k m : nat, ∀ f : form,
--   (∀^ V' ∷ (k + m) ⇒ V, R; F; V' ⊨ skolemize_one (AxE f k) m) ↔
--   (∀^ V' ∷ (k + m) ⇒ V, R; F; V' ⊨
--     (form.subst 0 (skolem_term $ m + k) (form.incr_fdx f)).vdec 0)
-- | 0 m g :=
--   begin
--     apply forall_congr, intro V',
--     rw [add_zero],
--     apply forall_congr, intro h0,
--     simp only [AxE, skolemize_one],
--   end
-- | (k + 1) m g :=
--   begin
--
--
--   end
--
-- #exit
-- lemma holds_skolemize_one_AxE (x : fn α) (k : nat) (g : form) :
--   (R; (F ₀↦ x); V ⊨ skolemize_one (AxE g k) 0) ↔
--   (∀^ V' ∷ k ⇒ V, R; (F ₀↦ x); V' ⊨
--     (form.subst k (skolem_term k) (form.incr_fdx g)).vdec k) := sorry

lemma holds_Ax :
  ∀ k : nat, ∀ f : form,
  (Ax f k).holds R F V ↔
  ∀^ V' ∷ k ⇒ V, f.holds R F V' := sorry

lemma holds_skolemize_one [inhabited α] {f : form} :
  f.holds R F V →
  ∃ g : fn α, (skolemize_one f 0).holds R (F ₀↦ g) V :=
begin
  intro h0, cases (classical.em $ AE f) with h1 h1,
  { rcases exists_kernel_of_AE _ h1 with ⟨g, k, h2⟩,
    subst h2,
    cases holds_skolemize_one_aux (holds_AxE_imp _ _ _ h0) with x h2,
    refine ⟨x, _⟩,
    rw [skolemize_one_AxE, add_zero, holds_Ax],
    exact h2 },
  refine ⟨λ _, default α, _⟩,
  apply holds_skolemize_one_of_not_AE,
  apply h1,
end

-- by { intros f h0, apply holds_skolemize_one_aux,
--   intros V' h1, rw eq_of_ext_zero h1, exact h0 }

#exit
lemma exists_fxt_holds_skolemize_core [inhabited α] :
  ∀ k : nat, ∀ F : fns α, ∀ f : form,
  ex_count f = k → f.holds R F V →
  (∃^ F' ∷ k ⇒ F, (skolemize_core k f).holds R F' V)
| 0       F f h0 h1 := ⟨F, ext_zero_refl _, h1⟩
| (k + 1) F f h0 h1 :=
  begin
    unfold skolemize_core,
    cases holds_skolemize_one h1 with g h2,
    rcases exists_fxt_holds_skolemize_core k (F ₀↦ g) (skolemize_one f 0)
      (ex_count_skolemize_one_eq  _ h0) h2 with ⟨F', h3, h4⟩,
    refine ⟨F', _, h4⟩,
    apply ext_succ h3
  end

#exit
lemma holds_skolemize {f : form} :
  f.holds R F V →
  (∃^ F' ∷ (ex_count f) ⇒ F, (skolemize f).holds R F' V) :=
begin
  intro h0, unfold skolemize,
end

#exit


lemma F_vdec :
  ∀ f : form, ∀ m : nat, f.F → (f.vdec m).F
| (form.lit l)     m h0 := trivial
| (form.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }

lemma QF_vdec :
  ∀ f : form, ∀ m : nat, f.QF → (f.vdec m).QF
| (form.lit l)     m h0 := trivial
| (form.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }
| (form.qua b f)   m h0 := QF_vdec f _ h0

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
    apply QF_vdec,
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
