import tactic.vampire.frm
import data.vector

namespace vampire

variables {α : Type}
variables {R : rls α} {F : fns α} {V V' : vas α}

local notation `#`     := trm.vr
local notation `$`     := trm.fn
local notation t `&` s := trm.ap t s
local notation `r*`     := atm.rl 
local notation t `=*` s := atm.eq t s 
local notation `+*`     := frm.atm tt
local notation `-*`     := frm.atm ff
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p
local notation R `;` F `;` V `⊨` f := frm.holds R F V f
local notation F `∀⟹` k := forall_ext k F
local notation F `∃⟹` k := exists_ext k F
local notation R `;` F `;` V `⊨` f := frm.holds R F V f

def ex_count : frm → nat
| (frm.atm _ _)   := 0
| (frm.bin _ _ _) := 0
| (∀* f)          := ex_count f
| (∃* f)          := ex_count f + 1

def skolem_trm : nat → trm
| 0       := $ 0
| (k + 1) := (skolem_trm k) & (# (k + 1))

@[reducible] def trm.skolem_vsub
  (k : nat) (s : trm) (t : trm) :=
(trm.vsub k s t.finc).vdec k

@[reducible] def atm.skolem_vsub
  (k : nat) (s : trm) (a : atm) :=
(a.finc.vsub k s).vdec k

@[reducible] def frm.skolem_vsub
  (k : nat) (s : trm) (f : frm) :=
(f.finc.vsub k s).vdec k

def skolemize_one : frm → nat → frm
| (∀* f) k := ∀* (skolemize_one f (k + 1))
| (∃* f) k := f.skolem_vsub 0 (skolem_trm k)
| _      _ := frm.default

def skolemize_core : nat → frm → frm
| 0       f := f
| (k + 1) f := skolemize_core k (skolemize_one f 0)

def skolemize (f : frm) : frm :=
skolemize_core (ex_count f) f

lemma AF_of_QF :
  ∀ f : frm, ex_count f = 0 → f.QF → f.AF
| (frm.atm b _)   h0 h1 := trivial
| (frm.bin b f g) h0 h1 := h1
| (∀* f)          h0 h1 := AF_of_QF f h0 h1

lemma ex_count_vdec :
  ∀ f : frm, ∀ m : nat, ex_count (f.vdec m) = ex_count f
| (frm.atm _ _)   m := rfl
| (frm.bin b f g) m := rfl
| (frm.qua b f)   m :=
  by cases b;
     simp [ frm.vdec, ex_count,
       ex_count_vdec _ (m + 1) ]

lemma ex_count_finc :
  ∀ f : frm, ex_count f.finc = ex_count f
| (frm.atm _ _)   := rfl
| (frm.bin _ _ _) := rfl
| (frm.qua b f)   :=
  by cases b;
     simp [ frm.finc, ex_count,
       ex_count_finc f ]

lemma ex_count_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  ex_count (f.vsub k t) = ex_count f
| (frm.atm _ _)   _ _ := rfl
| (frm.bin _ _ _) _ _ := rfl
| (frm.qua b _)   _ _ :=
  by cases b;
     simp [ frm.vsub, ex_count,
       ex_count_vsub ]

lemma ex_count_skolemize_one_eq {k : nat} :
  ∀ {f : frm}, ∀ m : nat,
  ex_count f = k + 1 →
  ex_count (skolemize_one f m) = k
| (∀* f) m h0 :=
  by { unfold skolemize_one,
       apply ex_count_skolemize_one_eq (m + 1) ,
       apply h0 }
| (∃* f) m h0 :=
  begin
    unfold skolemize_one,
    unfold frm.skolem_vsub,
    unfold ex_count at h0,
    rw [ ex_count_vdec,
         ex_count_vsub,
         ex_count_finc,
         nat.succ_inj h0 ],
  end

local notation f `₀↦` a := assign a f


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

lemma frm.skolem_vsub_qua
  (b : bool) (f : frm) (k : nat) (s : trm) :
  (frm.qua b f).skolem_vsub k s =
  frm.qua b (f.skolem_vsub (k + 1) (s.vinc 0 1)) := rfl

lemma frm.skolem_vsub_atm
  (b : bool) (a : atm) (k : nat) (s : trm) :
  (frm.atm b a).skolem_vsub k s = frm.atm b (a.skolem_vsub k s) := rfl

lemma frm.skolem_vsub_bin
  (b : bool) (f g : frm) (k : nat) (s : trm) :
  (frm.bin b f g).skolem_vsub k s =
  frm.bin b (f.skolem_vsub k s) (g.skolem_vsub k s) := rfl

lemma trm.skolem_vsub_ap
  {t r : trm} {k : nat} {s : trm}  :
  trm.skolem_vsub k s (t & r) =
  (trm.skolem_vsub k s t & trm.skolem_vsub k s r) := rfl

lemma atm.skolem_vsub_rl
  {k m : nat} {ts : list trm} {r : trm} :
  (r* k ts).skolem_vsub m r = 
  r* k (ts.map $ trm.skolem_vsub m r) := 
by { simp only [atm.skolem_vsub, list.map_map, 
       atm.finc, atm.vsub, atm.vdec, trm.skolem_vsub],
     constructor; refl }

lemma atm.skolem_vsub_eq
  {t s : trm} {m : nat} {r : trm} :
  (t =* s).skolem_vsub m r = 
  (trm.skolem_vsub m r t =* trm.skolem_vsub m r s) := rfl

lemma trm.skolem_vsub_eq_of_eq
  {k m : nat} {s : trm} (h0 : m = k) :
  trm.skolem_vsub k s (# m) = s.vdec k :=
by { simp only [ trm.val, trm.vdec, trm.vsub,
       trm.skolem_vsub, trm.finc, if_pos h0 ] }

lemma trm.skolem_vsub_eq_of_gt
  {k m : nat} {s : trm} (h0 : m > k) :
  trm.skolem_vsub k s (# m) = # (m - 1) :=
by simp only [ trm.skolem_vsub, trm.vsub, trm.finc, 
     if_neg (ne_of_gt h0), trm.vdec, if_pos h0 ]

lemma trm.skolem_vsub_eq_of_lt
  {k m : nat} {s : trm} (h0 : m < k) :
  trm.skolem_vsub k s (# m) = # m :=
by simp only [ trm.skolem_vsub, trm.vsub, trm.finc, trm.vdec,
      if_neg (ne_of_lt h0), if_neg (not_lt_of_gt h0) ] 

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
  {R S : rls α} {F G : fns α} {V W : vas α} {b : bool} {f g : frm} :
  (∀ x : α, f.holds R F (V ₀↦ x) → g.holds S G (W ₀↦ x)) →
  (frm.qua b f).holds R F V →
  (frm.qua b g).holds S G W :=
by { intros h0 h1, cases b,
     { intro x, apply h0 x (h1 x) },
     cases h1 with x h2,
     refine ⟨x, h0 x h2⟩ }

lemma val_vdec_succ_vinc_zero {k : nat} {x : α}:
   ∀ t : trm,
   ((t.vinc 0 1).vdec (k + 1)).val F (V ₀↦ x) =
   (t.vdec k).val F V 
| ($ m)    := rfl
| (t & s) :=
  by simp only [ trm.val, val_vdec_succ_vinc_zero t,
       val_vdec_succ_vinc_zero s, trm.vdec, trm.vinc ]
| (# m) :=
  by { apply funext, intro,
       unfold trm.vinc,
       unfold trm.vdec,
       unfold trm.val,
       rw [ if_neg (not_lt_zero _), nat.add_sub_cancel ],
       by_cases h0 : k < m,
       { cases m,
         { apply false.elim (not_lt_zero _ h0) },
         rw [ if_pos h0, if_pos (succ_lt_succ h0) ],
         refl },
       rw [ if_neg h0, if_neg (λ h1, _) ],
       { refl },
       apply h0 (lt_of_succ_lt_succ h1) }

lemma trm.val_skolem_vsub_of_wfc
  {x : α} {y : fn α} {r : trm} {k : nat} {W V : vas α}
  (h0 : splice k x W V) (h1 : (r.vdec k).val (F ₀↦ y) V [] = x) :
  ∀ t : trm, 
    (t.wfc ff → (trm.skolem_vsub k r t).val (F ₀↦ y) V = t.val F W) ∧ 
    (t.wfc tt → (trm.skolem_vsub k r t).val (F ₀↦ y) V [] = t.val F W [])  
| (# m) := 
  by { constructor; rintro ⟨_⟩,
       rcases nat.lt_trichotomy m k with h2 | h2 | h2,
       { rw trm.skolem_vsub_eq_of_lt h2,
         simp only [ trm.val, h0.left _ h2 ] },
       { rw [ trm.skolem_vsub_eq_of_eq h2, h1,
              h2, (h0.right.left).symm ], refl },
       rw trm.skolem_vsub_eq_of_gt h2,
       cases m, { cases h2 },
       rw lt_succ_iff at h2,
       apply (h0.right.right m h2).symm }
| ($ m) := by { constructor; intro; refl }
| (t & s) :=
  by constructor; intro h2; 
     { rw trm.skolem_vsub_ap,
       simp only [ trm.val,
         (trm.val_skolem_vsub_of_wfc t).left h2.left,
         (trm.val_skolem_vsub_of_wfc s).right h2.right ] } 

lemma wfc_tt_of_wf :
  ∀ t : trm, t.wf → t.wfc tt :=
by { rintros (k | k | ⟨t, s⟩) h0; 
     try { apply h0 }, 
     unfold trm.wfc, refl }

lemma wf_of_wfc {t : trm} {b : bool} : t.wfc b → t.wf :=
by { intro h0, cases t with k k t s; 
     try { apply h0 }, trivial, }

lemma trm.val_skolem_vsub_of_wf
  {x : α} {y : fn α} {r : trm} {k : nat} {W V : vas α}
  (h0 : splice k x W V) (h1 : (r.vdec k).val (F ₀↦ y) V [] = x) 
  {t : trm} (h2 : t.wf) : 
  (trm.skolem_vsub k r t).val (F ₀↦ y) V [] = t.val F W [] :=
(trm.val_skolem_vsub_of_wfc h0 h1 _).right (wfc_tt_of_wf _ h2) 

def atm.wf : atm → Prop 
| (atm.rl k ts) := ∀ t ∈ ts, trm.wf t
| (atm.eq t s)  := t.wf ∧ s.wf 

lemma atm.holds_skolem_vsub
  {x : α} {y : fn α} {s : trm} {k : nat} (R : rls α) {W V : vas α}
  (h0 : splice k x W V) (h1 : (s.vdec k).val (F ₀↦ y) V [] = x) :
  ∀ {a : atm}, a.wf → 
    ((a.skolem_vsub k s).holds R (F ₀↦ y) V ↔ a.holds R F W)
| (atm.rl k ts) h2 :=
  by { rw atm.skolem_vsub_rl,
       unfold atm.holds,
       rw [list.map_map],
       apply iff_of_eq (congr_arg _ _),
       apply list.map_eq_map_of_forall_mem_eq,
       intros t h4,
       apply trm.val_skolem_vsub_of_wf h0 h1 (h2 _ h4) }
| (atm.eq t s) h2 :=
  by { rw atm.skolem_vsub_eq,
       unfold atm.holds,
       rw [ trm.val_skolem_vsub_of_wf h0 h1 h2.left,
            trm.val_skolem_vsub_of_wf h0 h1 h2.right ] }

def frm.wf : frm → Prop
| (frm.atm _ a)   := a.wf
| (frm.bin _ f g) := f.wf ∧ g.wf
| (frm.qua _ f)   := f.wf 

lemma holds_skolem_vsub {x : α} {y : fn α} :
  ∀ {f : frm} {k : nat} {s : trm} {W V : vas α},
  f.wf → splice k x W V →
  ((s.vdec k).val (F ₀↦ y) V [] = x) →
  (R ; F ; W ⊨ f) →
  (R ; (F ₀↦ y) ; V ⊨ f.skolem_vsub k s)
| (frm.atm b a) k s W V h0 h1 h2 h4 :=
  by { rw frm.skolem_vsub_atm,
       cases b; unfold frm.holds;
       rw atm.holds_skolem_vsub R h1 h2 h0;
       exact h4 }
| (frm.bin b f g) k s W V h0 h1 h2 h3 :=
  by { cases h0,
       rw frm.skolem_vsub_bin,
       apply holds_bin_of_holds_bin _ _ h3;
       apply holds_skolem_vsub _ h1 h2;
       assumption }
| (frm.qua b f) k s W V h0 h1 h2 h3 :=
  by { rw frm.skolem_vsub_qua,
       apply holds_qua_of_holds_qua _ h3,
       intros a h3,
       apply holds_skolem_vsub _ _ _ h3,
       { exact h0 },
       { apply splice_succ h1 },
       rw val_vdec_succ_vinc_zero,
       apply h2 }

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

lemma val_vdec_zero_skolem_trm [inhabited α]
  {k : nat} (F : fns α) (V : vas α) (s : vector α k → α) {v : vector α k} :
  ∀ m : nat, ∀ as : list α, m ≤ k → v.val.drop m = as →
  ((skolem_trm m).vdec 0).val (F ₀↦ to_fn s) (vassign v V) as = s v
| 0       as hle h0 :=
  by simp only [ list.drop, skolem_trm, trm.val,
       trm.vdec, assign, h0.symm, to_fn_eq ]
| (m + 1) as h0 h1 :=
  begin
    have : ((skolem_trm m).vdec 0).val
      (F ₀↦ to_fn s) (vassign v V) (vassign v V m :: as) = s v,
    { apply val_vdec_zero_skolem_trm m _ (le_trans (le_succ _) h0),
    rw [list.drop_eq_cons_of_lt, vassign_eq_of_lt, h1],
    rwa succ_le_iff at h0 },
    exact this
  end

lemma splice_zero (x : α) (V : vas α) : splice 0 x (V ₀↦ x) V :=
⟨λ _ h0, by cases h0, rfl, λ m _, rfl⟩

lemma drop_eq_nil :
  ∀ {l : list α}, ∀ {k : nat},
  l.length = k → l.drop k = []
| []        0       h0 := rfl
| []        (k + 1) h0 := by cases h0
| (a :: as) 0       h0 := by cases h0
| (a :: as) (k + 1) h0 :=
  by { unfold list.drop, apply drop_eq_nil,
       apply nat.succ_inj h0 }

lemma holds_skolemize_one_aux [inhabited α] 
  {k : nat} {f : frm} (hwf : f.wf) :
  (V ∀⟹ k) (λ V', ∃ a : α, f.holds R F (V' ₀↦ a)) →
  ∃ g : fn α, (V ∀⟹ k)
    (λ V', ((f.finc.vsub 0 (skolem_trm k)).vdec 0).holds R (F ₀↦ g) V') :=
by { intro h0,
     have h1 : ∀ v : vector α k, ∃ a : α, f.holds R F ((vassign v V) ₀↦ a),
     { intro v, apply h0 (vassign v V) (ext_vassign _ _) },
     rw classical.skolem at h1,
     cases h1 with s h1,
     refine ⟨to_fn s, _⟩,
     intros V' h2,
     cases exists_eq_vassign_of_ext h2 with v h3,
     rw h3,
     have h5 := val_vdec_zero_skolem_trm F V s k []
       (le_refl _) (drop_eq_nil v.property),
     apply holds_skolem_vsub hwf (splice_zero (s v) _) h5 (h1 _) }

def AE : frm → Prop
| (∀* f) := AE f
| (∃* f) := true
| _      := false

def AxE (f : frm) : nat → frm
| 0       := ∃* f
| (k + 1) := ∀* (AxE k)

def Ax (f : frm) : nat → frm
| 0       := f
| (k + 1) := ∀* (Ax k)

lemma exists_kernel_of_AE :
  ∀ f : frm, AE f → ∃ g : frm, ∃ k : nat, f = AxE g k
| (frm.atm _ _)   h0 := by cases h0
| (frm.bin b f g) h0 := by cases h0
| (∃* f)          h0 := ⟨f, 0, rfl⟩
| (∀* f)          h0 :=
  by { rcases exists_kernel_of_AE f h0 with ⟨g, k, h1⟩,
       refine ⟨g, k + 1, _⟩,
       unfold AxE, rw h1 }

lemma holds_AxE_imp :
  ∀ k : nat, ∀ V : vas α, ∀ f : frm, 
  ((AxE f k).holds R F V) →
  (V ∀⟹ k) (λ V', ∃ a : α, f.holds R F (V' ₀↦ a))
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
  ∀ f : frm, ¬ AE f →
  ∀ R : rls α, ∀ F : fns α, ∀ V : vas α, ∀ k : nat,
  (skolemize_one f k).holds R F V
| (∀* f) h0 R F V k :=
  by { unfold skolemize_one, intro a,
       apply holds_skolemize_one_of_not_AE f h0 }
| (∃* f) h0 R F V k := false.elim (h0 trivial)
| (frm.atm _ _)   h0 R F V k := rfl
| (frm.bin _ _ _) h0 R F V k := rfl

lemma skolemize_one_AxE (f : frm) :
  ∀ k m : nat, skolemize_one (AxE f k) m =
  Ax ((f.finc.vsub 0 (skolem_trm (k + m))).vdec 0) k
| 0 m := by { rw zero_add, refl }
| (k + 1) m :=
  by { simp only [ AxE, skolemize_one, Ax,
         skolemize_one_AxE k (m + 1), succ_add ],
    refine ⟨rfl, rfl⟩ }

lemma holds_Ax :
  ∀ k : nat, ∀ f : frm, ∀ V : vas α,
  (Ax f k).holds R F V ↔ (V ∀⟹ k) (λ V', f.holds R F V')
| 0 f V :=
  by { constructor; intro h0,
       { intros V' h1,
         rw eq_of_ext_zero h1,
         apply h0 },
       apply h0,
       apply ext_zero_refl }
| (k + 1) f V :=
  by{ simp only [Ax, frm.holds],
      constructor; intro h0,
      { intros V' h1,
        have h2 := h0 (V' k),
        rw holds_Ax at h2,
        apply h2 _ (ext_assign h1) },
      intro a,
      rw holds_Ax,
      intros V' h1,
      apply h0 _ (ext_succ h1) }

lemma wf_of_wf_AxE : 
  ∀ {k : nat} {f : frm}, (AxE f k).wf → f.wf 
| 0       _ := id
| (k + 1) f := @wf_of_wf_AxE k _ 

lemma holds_skolemize_one [inhabited α] {f : frm} :
  f.wf → f.holds R F V →
  ∃ g : fn α, (skolemize_one f 0).holds R (F ₀↦ g) V :=
begin
  intros hwf h0, 
  cases (classical.em $ AE f) with h1 h1,
  { rcases exists_kernel_of_AE _ h1 with ⟨g, k, h2⟩,
    subst h2, 
    cases holds_skolemize_one_aux (wf_of_wf_AxE hwf) 
      (holds_AxE_imp _ _ _ h0) with x h2,
    refine ⟨x, _⟩,
    rw [skolemize_one_AxE, add_zero, holds_Ax],
    exact h2 },
  refine ⟨λ _, default α, _⟩,
  apply holds_skolemize_one_of_not_AE,
  apply h1,
end

lemma frm.wf_default : frm.default.wf := 
by constructor; exact trivial

lemma trm.wfc_finc : 
  ∀ {t : trm}, ∀ b : bool, t.wfc b → t.finc.wfc b
| (# _)   _ h0 := h0
| ($ _)   _ h0 := h0 
| (t & s) _ h0 :=
  by { cases h0, constructor; 
       apply trm.wfc_finc; assumption } 

lemma trm.wf_finc : ∀ {t : trm}, t.wf → t.finc.wf 
| (# _)   _  := trivial 
| ($ _)   _  := trivial 
| (t & s) h0 :=
  by { cases h0, constructor; 
       apply trm.wfc_finc; assumption } 

lemma atm.wf_finc : ∀ {a : atm}, a.wf → a.finc.wf 
| (atm.rl _ ts) h0 := 
  by { unfold atm.finc,
       unfold atm.wf,
       apply list.forall_mem_map_of_forall_mem,
       apply trm.wf_finc, apply h0 }
| (atm.eq t s) h0 := 
  by { cases h0, constructor;
       apply trm.wf_finc; assumption }

lemma frm.wf_finc : ∀ {f : frm}, f.wf → f.finc.wf 
| (frm.atm _ _)   h0 := atm.wf_finc h0
| (frm.bin _ _ _) h0 := 
  by { cases h0, constructor; 
       apply frm.wf_finc; assumption }
| (frm.qua _ f)   h0 := @frm.wf_finc f h0

lemma trm.wfc_vdec {k : nat} : 
  ∀ {t : trm}, ∀ b : bool, t.wfc b → (t.vdec k).wfc b
| (# _)   _ h0 := h0
| ($ _)   _ h0 := h0 
| (t & s) _ h0 :=
  by { cases h0, constructor; 
       apply trm.wfc_vdec; assumption } 

lemma trm.wf_vdec {k : nat} : 
  ∀ {t : trm}, t.wf → (t.vdec k).wf 
| (# _)   _  := trivial 
| ($ _)   _  := trivial 
| (t & s) h0 :=
  by { cases h0, constructor; 
       apply trm.wfc_vdec; assumption } 

lemma atm.wf_vdec {k : nat} : 
  ∀ {a : atm}, a.wf → (a.vdec k).wf 
| (atm.rl _ ts) h0 := 
  by { unfold atm.vdec,
       unfold atm.wf,
       apply list.forall_mem_map_of_forall_mem,
       apply trm.wf_vdec, apply h0 }
| (atm.eq t s) h0 := 
  by { cases h0, constructor;
       apply trm.wf_vdec; assumption }

lemma frm.wf_vdec : 
  ∀ (k : nat) {f : frm}, f.wf → (f.vdec k).wf 
| _ (frm.atm _ _)   h0 := atm.wf_vdec h0
| _ (frm.bin _ _ _) h0 := 
  by { cases h0, constructor; 
       apply frm.wf_vdec; assumption }
| k (frm.qua _ f)   h0 := @frm.wf_vdec _ f h0

lemma trm.wfc_vsub {m : nat} {r : trm} (h0 : r.wf) : 
  ∀ {t : trm}, ∀ b : bool, t.wfc b → (trm.vsub m r t).wfc b
| (# k) tt h1 := ite_cases (wfc_tt_of_wf _ h0) h1
| ($ _) b h0 := h0 
| (t & s) _ h0 :=
  by { cases h0, constructor; 
       apply trm.wfc_vsub; assumption } 

lemma trm.wf_vsub {m : nat} {r : trm} {h0 : r.wf} : 
  ∀ {t : trm}, t.wf → (trm.vsub m r t).wf 
| (# k)   h1 := ite_cases h0 h1 
| ($ _)   _  := trivial 
| (t & s) h1 :=
  by { cases h1, constructor; 
       apply trm.wfc_vsub; assumption } 

lemma atm.wf_vsub {m : nat} {r : trm} {h0 : r.wf} : 
  ∀ {a : atm}, a.wf → (a.vsub m r).wf 
| (r* _ ts) h1 := 
  by { unfold atm.vsub,
       unfold atm.wf,
       apply list.forall_mem_map_of_forall_mem,
       apply trm.wf_vsub,
       apply h0, apply h1 }
| (atm.eq t s) h1 := 
  by { cases h1, constructor;
       apply trm.wf_vsub; assumption }

lemma trm.wfc_vinc {m n : nat} : 
  ∀ t : trm, ∀ b : bool, t.wfc b → (t.vinc m n).wfc b 
| (# k)   tt h0 := rfl
| ($ k)   _  h0 := h0
| (t & s) _  h0 := 
  by { cases h0, constructor; 
       apply trm.wfc_vinc; assumption }

lemma trm.wf_vinc {m n : nat} : 
  ∀ t : trm, t.wf → (t.vinc m n).wf 
| (# k)   h0 := trivial
| ($ k)   h0 := trivial
| (t & s) h0 := 
  by { cases h0, constructor; 
       apply trm.wfc_vinc; assumption }

lemma frm.wf_vsub : 
  ∀ {f : frm} (k : nat) {t : trm}, 
  f.wf → t.wf → (f.vsub k t).wf 
| (frm.atm _ _)   k t h0 h1 := @atm.wf_vsub _ _ h1 _ h0 
| (frm.bin b f g) k t h0 h1 := 
  by { cases h0, constructor;
       apply frm.wf_vsub; assumption }
| (frm.qua _ f)   k t h0 h1 := 
  @frm.wf_vsub f _ _ h0 (trm.wf_vinc _ h1)

lemma wf_skolem_vsub {f : frm} {t : trm} (k : nat) :
  f.wf → t.wf → (f.skolem_vsub k t).wf :=
by { intros h0 h1, 
     unfold frm.skolem_vsub,
     apply frm.wf_vdec,
     apply frm.wf_vsub _ _ h1,
     apply frm.wf_finc h0 }

lemma wfc_ff_skolem_trm : ∀ {k : nat}, (skolem_trm k).wfc ff 
| 0       := trivial
| (k + 1) := ⟨wfc_ff_skolem_trm, rfl⟩ 

lemma wf_skolem_trm {k : nat} : (skolem_trm k).wf := 
wf_of_wfc wfc_ff_skolem_trm

lemma wf_skolemize_one : 
  ∀ f : frm, f.wf → ∀ k : nat, (skolemize_one f k).wf 
| (frm.atm _ _)   _ _ := frm.wf_default
| (frm.bin _ _ _) _ _ := frm.wf_default
| (∀* f) h0 k := by apply wf_skolemize_one f h0
| (∃* f) h0 k := 
  by { unfold skolemize_one,
       apply wf_skolem_vsub,
       exact h0,
       apply wf_skolem_trm }

lemma exists_fxt_holds_skolemize_core [inhabited α] :
  ∀ k : nat, ∀ F : fns α, ∀ f : frm,
  f.wf → ex_count f = k → f.holds R F V →
  (F ∃⟹ k) (λ F', (skolemize_core k f).holds R F' V)
| 0       F f _   h0 h1 := ⟨F, ext_zero_refl _, h1⟩
| (k + 1) F f hwf h0 h1 :=
  begin
    unfold skolemize_core,
    cases holds_skolemize_one hwf h1 with g h2,
    rcases exists_fxt_holds_skolemize_core
      k (F ₀↦ g) (skolemize_one f 0) _
      (ex_count_skolemize_one_eq  _ h0) h2 with ⟨F', h3, h4⟩,
    { refine ⟨F', _, h4⟩,
      apply ext_succ h3 },
    apply wf_skolemize_one _ hwf
  end

lemma holds_skolemize [inhabited α] {f : frm} :
  f.wf → f.holds R F V →
  (F ∃⟹ ex_count f) (λ F', (skolemize f).holds R F' V) :=
λ h0 h1, exists_fxt_holds_skolemize_core _ _ _ h0 rfl h1

lemma F_vdec :
  ∀ f : frm, ∀ m : nat, f.F → (f.vdec m).F
| (frm.atm _ _)   m h0 := trivial
| (frm.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }

lemma QF_vdec :
  ∀ f : frm, ∀ m : nat, f.QF → (f.vdec m).QF
| (frm.atm _ _)   m h0 := trivial
| (frm.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }
| (frm.qua b f)   m h0 := QF_vdec f _ h0

lemma F_finc :
  ∀ f : frm, f.F → f.finc.F
| (frm.atm _ _)   h0 := trivial
| (frm.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_finc; assumption }

lemma QF_finc :
  ∀ f : frm, f.QF → (f.finc).QF
| (frm.atm _ _)   h0 := trivial
| (frm.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_finc; assumption }
| (frm.qua b f)   h0 := QF_finc f h0

lemma F_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  f.F → (f.vsub k t).F
| (frm.atm _ _)   k t h0 := trivial
| (frm.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vsub; assumption }

lemma QF_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  f.QF → (f.vsub k t).QF
| (frm.atm _ _)   k t h0 := trivial
| (frm.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vsub; assumption }
| (frm.qua b f)   k t h0 := QF_vsub f _ _ h0

lemma QF_skolemize_one :
  ∀ f : frm, ∀ m : nat,
  f.QF → (skolemize_one f m).QF
| (frm.atm _ _)   m h0 := trivial
| (frm.bin _ _ _) m h0 := trivial
| (∀* f)           m h0 := QF_skolemize_one f _ h0
| (∃* f)           m h0 :=
  begin
    apply QF_vdec,
    apply QF_vsub,
    apply QF_finc,
    exact h0
  end

lemma AF_skolemize_core :
  ∀ k : nat, ∀ {f : frm},
  ex_count f = k → f.QF → (skolemize_core k f).AF
| 0       f h0 h1 := AF_of_QF _ h0 h1
| (k + 1) f h0 h1 :=
  begin
    unfold skolemize_core,
    apply AF_skolemize_core,
    { apply ex_count_skolemize_one_eq _ h0 },
    apply QF_skolemize_one _ _ h1
  end

lemma AF_skolemize {f : frm} :
  f.QF → (skolemize f).AF :=
by { intro h0, unfold skolemize,
     apply AF_skolemize_core _ rfl h0 }

end vampire
