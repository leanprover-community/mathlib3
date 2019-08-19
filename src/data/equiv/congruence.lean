import group_theory.submonoid order.order_iso algebra.pi_instances tactic.default data.equiv.algebra

variables {M : Type*} {N : Type*} {P : Type*}
          [monoid M] [monoid N] [monoid P]

set_option old_structure_cmd true

namespace monoid_hom

lemma map_pow (f : M →*P) (a : M) : ∀(n : ℕ), f (a ^ n) = (f a) ^ n
| 0            := map_one f
| (nat.succ n) := by rw [pow_succ, map_mul, map_pow n]; refl

end monoid_hom

namespace mul_equiv

@[simp] lemma to_monoid_hom_apply {h : M ≃* N} {x : M} : h.to_monoid_hom x = h x := rfl

@[simp] lemma to_monoid_hom_symm_apply {h : M ≃* N} {x : N} :
  h.symm.to_monoid_hom x = h.symm x := rfl

@[simp] lemma to_monoid_hom_left_inv {h : M ≃* N} :
  h.symm.to_monoid_hom.comp h.to_monoid_hom = monoid_hom.id M :=
by ext; simp; refl

@[simp] lemma to_monoid_hom_right_inv {h : M ≃* N} :
h.to_monoid_hom.comp h.symm.to_monoid_hom = monoid_hom.id N :=
by ext; simp; refl

def submonoid_congr {A B : submonoid M} (h : A = B) : A ≃* B :=
{ map_mul' := λ x y, rfl,
  ..equiv.set_congr $ submonoid.ext'_iff.2 h }

def submonoid.to_monoid_hom {A B : submonoid M} (h : A ≃* B) : A →* B :=
@mul_equiv.to_monoid_hom A B _ _ h

end mul_equiv

namespace monoid_hom

@[reducible] def range_mk (f : M →* N) : M →* f.range :=
subtype_mk f.range f $ λ x, ⟨x, submonoid.mem_top x, rfl⟩

lemma range_top_of_surjective (f : M →* N) (hf : function.surjective f) :
  f.range = (⊤ : submonoid N) :=
submonoid.ext'_iff.1 $ (set.ext_iff _ _).2 $ λ x,
⟨λ h, submonoid.mem_top x, λ h, exists.elim (hf x) $ λ w hw, ⟨w, submonoid.mem_top w, hw⟩⟩

@[simp] lemma surjective_of_range_mk (f : M →* P) : function.surjective f.range_mk :=
λ ⟨w, z, hzm, hz⟩, ⟨z, by rcases hz; rcases _x; refl⟩

end monoid_hom

/- Congruence relations -/

variables (M)

structure con :=
(r : M → M → Prop)
(r_iseqv : equivalence r)
(r_mul : ∀ {w x y z}, r w x → r y z → r (w*y) (x*z))

namespace con

variables {M}

instance : has_coe_to_fun (con M) := ⟨_, λ c, λ m n, c.r m n⟩

@[simp] lemma rel_coe {c : con M} : c.r = (c : M → M → Prop) := rfl
@[simp] lemma refl (c : con M) : reflexive c := λ x, c.2.1 x
@[simp] lemma symm (c : con M) : symmetric c := λ _ _ h, c.2.2.1 h
@[simp] lemma trans (c : con M) : transitive c := λ  _ _ _ hx hy, c.2.2.2 hx hy
@[simp] lemma mul (c : con M) : ∀ {w x y z}, c w x → c y z → c (w*y) (x*z) :=
λ _ _ _ _ h1 h2, c.3 h1 h2
@[simp] lemma iseqv (c : con M) : equivalence c := c.2

lemma r_inj {c d : con M} (H : c.r = d.r) : c = d :=
by cases c; cases d; simp * at *

@[extensionality] lemma ext {c d : con M} (H : ∀ x y : M, c x y ↔ d x y) :
  c = d := r_inj $ by ext x y; exact H x y

lemma ext_iff {c d : con M} : (∀ x y : M, c x y ↔ d x y) ↔ c = d :=
⟨λ h, ext h, λ h x y, h ▸ iff.rfl⟩

variables (M)

protected def submonoid (c : con M) : submonoid (M × M) :=
{ carrier := { x | c x.1 x.2 },
  one_mem' := c.iseqv.1 1,
  mul_mem' := λ x y hx hy, c.mul hx hy }

variables {M}

def of_submonoid (N : submonoid (M × M)) (H : equivalence (λ x y : M, (x, y) ∈ N)) : con M :=
{ r := λ x y : M, (x, y) ∈ N,
  r_iseqv := H,
  r_mul := λ _ _ _ _ h1 h2, N.mul_mem h1 h2 }

def ker (f : M →* P) : con M :=
{ r := λ x y, f x = f y,
  r_iseqv := ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ hx hy, eq.trans hx hy⟩,
  r_mul := λ _ _ _ _ h1 h2, by rw [f.map_mul, h1, h2, f.map_mul] }

end con

namespace submonoid

def diag : submonoid (M × M) :=
{ carrier := { x | x.1 = x.2 },
  one_mem' := rfl,
  mul_mem' := λ x y h1 h2, by simp * at * }

end submonoid

variables {M}

def monoid_hom.ker' (f : M →* P) : submonoid (M × M) := (con.ker f).submonoid M

namespace monoid_hom

lemma mem_ker' (f : M →* P) (x y : M) :
  (x, y) ∈ f.ker' ↔ f x = f y := ⟨λ h, h, λ h, h⟩

theorem injective_iff_ker'_diag (f : M →* P) :
  function.injective f ↔ f.ker' = submonoid.diag M :=
⟨λ h, submonoid.ext (λ x, ⟨λ hx, h hx, λ hx, congr_arg f $ hx⟩),
 λ h x y hf, show (x, y) ∈ submonoid.diag M, by rwa ←h⟩

theorem ker_eq_ker' {G : Type*} {H : Type*} [group G] [group H]
  (f : G →* H) {x : G} :
  (∃ y, y ∈ f.ker' ∧ x = (y : G × G).1 * y.2⁻¹) ↔ f x = 1 :=
⟨λ ⟨y, hm, hxy⟩, by
  rw [hxy, f.map_mul, f.map_inv, show f y.1 = f y.2, from hm, mul_right_inv],
 λ hx, ⟨(x,1), show f x = f 1, from f.map_one.symm ▸ hx, by simp only [mul_one, one_inv]⟩⟩

end monoid_hom

namespace con

lemma ker_rel (f : M →* P) {x y : M} : con.ker f x y ↔ f x = f y := iff.rfl

variable (c : con M)

def subtype (A : submonoid M) : con A :=
⟨λ x y, c x y, ⟨λ x, c.refl x, λ x y h, c.symm h, λ x y z h1 h2, c.trans h1 h2⟩,
 λ w x y z h1 h2, c.mul h1 h2⟩

@[simp] lemma subtype_apply {A : submonoid M} {x y : A} : c.subtype A x y ↔ c x y := iff.rfl

def setoid : setoid M := ⟨c.r, c.iseqv⟩

@[simp] lemma setoid_eq : (setoid c).r = c := rfl

def quotient := quotient $ setoid c

instance : has_coe M (c.quotient) := ⟨@quotient.mk _ c.setoid⟩

instance [d : ∀ a b : M, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq M c.setoid d

@[elab_as_eliminator, reducible]
protected def lift_on' {β : Type*} {c : con M} (q : c.quotient) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) : β := quotient.lift_on' q f h

@[elab_as_eliminator, reducible]
protected def lift_on₂' {β : Type*} {c : con M} {d : con N} (q₁ : c.quotient) (q₂ : d.quotient)
  (f : M → N → β) (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → d a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
quotient.lift_on₂' q₁ q₂ f h

variables {c}

/- Leaving these 4 in because they make the goals nicer looking but the only one I used in this file
   was induction_on₂. -/
@[elab_as_eliminator]
lemma ind {C : c.quotient → Prop} (H : ∀ (x : M), C x) : ∀ (q : c.quotient), C q :=
quotient.ind' H

@[elab_as_eliminator]
lemma ind₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (H : ∀ (x : M) (y : N), C x y) : ∀ p q, C p q :=
quotient.ind₂' H

@[elab_as_eliminator]
lemma induction_on {C : c.quotient → Prop} (q : c.quotient) (H : ∀ x : M, C x) : C q :=
quotient.induction_on' q H

@[elab_as_eliminator]
lemma induction_on₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (p : c.quotient) (q : d.quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
quotient.induction_on₂' p q H

instance : inhabited (c.quotient) := ⟨((1 : M) : c.quotient)⟩

@[simp] protected lemma eq {a b : M} : (a : c.quotient) = b ↔ c a b :=
quotient.eq'

lemma exists_rep (x : c.quotient) : ∃ y : M, (y : c.quotient) = x :=
@quotient.exists_rep _ c.setoid x

variables (c)

instance monoid : monoid (c.quotient) :=
{ one := ((1 : M) : c.quotient),
  mul := λ x y, quotient.lift_on₂' x y (λ w z, (((w*z) : M) : c.quotient))
         $ λ _ _ _ _ h1 h2, con.eq.2 $ c.mul h1 h2,
  mul_assoc := λ x y z, quotient.induction_on₃' x y z
               $ λ p q r, congr_arg coe $ mul_assoc p q r,
  mul_one := λ x, quotient.induction_on' x $ λ y, congr_arg coe $ mul_one y,
  one_mul := λ x, quotient.induction_on' x $ λ y, congr_arg coe $ one_mul y }

def mk' : M →* c.quotient := ⟨coe, rfl, λ x y, rfl⟩

variables (x y : M)

@[simp] lemma mk'_ker : con.ker c.mk' = c := ext $ λ x y, con.eq

lemma mk'_submonoid : c.mk'.ker' = c.submonoid M :=
submonoid.ext $ λ x, ⟨λ h, con.eq.1 h, λ h, con.eq.2 h⟩

@[simp] lemma mk'_one : c.mk' 1 = 1 := rfl
@[simp] lemma mk'_mul : c.mk' (x * y) = c.mk' x * c.mk' y := rfl
@[simp] lemma mk'_pow : ∀ n : ℕ, c.mk' (x ^ n) = (c.mk' x) ^ n
| 0 := c.mk'.map_one
| (m + 1) := by rw [pow_succ, c.mk'.map_mul, mk'_pow m]; refl
@[simp] lemma comp_mk'_apply (g : c.quotient →* P) {x : M} : g.comp c.mk' x = g x := rfl

@[simp] lemma coe_one : ((1 : M) : c.quotient) = 1 := rfl
@[simp] lemma coe_mul : (x : c.quotient) * (y : c.quotient) = ((x * y : M) : c.quotient)  := rfl
lemma coe_pow : ∀ (n : ℕ), (x ^ n : c.quotient) = (x : c.quotient) ^ n
| 0            := pow_zero _
| (nat.succ n) := by rw pow_succ _

@[simp] lemma lift_on_beta {β : Type*} (c : con M) (f : M → β)
  (h : ∀ (a b : M), c a b → f a = f b) (x : M) :
con.lift_on' (x : c.quotient) f h = f x := rfl

variable {f : M →* P}

lemma ker_apply_eq_preimage (m : M) : (con.ker f) m = f ⁻¹' {f m} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 (set.mem_singleton_iff.2 h.symm),
   λ h, (set.mem_singleton_iff.1 (set.mem_preimage.1 h)).symm⟩

def congr {c d : con M} (h : c = d) :  c.quotient ≃* d.quotient :=
{ map_mul' := λ x y, by rcases x; rcases y; refl,
  ..quotient.congr (equiv.refl M) $ by apply ext_iff.2 h }

open lattice

instance : has_le (con M) := ⟨λ c d, c.submonoid M ≤ d.submonoid M⟩

instance to_submonoid : has_coe (con M) (submonoid (M × M)) := ⟨λ c, c.submonoid M⟩

lemma le_def' {c d : con M} : c ≤ d ↔ (c : submonoid (M × M)) ≤ d := iff.rfl

lemma le_def (c d : con M) : c ≤ d ↔ (∀ x y, c x y → d x y) :=
⟨λ h x y hc, (submonoid.le_def ↑c ↑d).1 (le_def'.1 h) (x, y) hc,
 λ h, le_def'.2 $ (submonoid.le_def ↑c ↑d).2 $ λ x hc, h x.1 x.2 hc⟩

instance : has_mem (M × M) (con M) := ⟨λ x c, x ∈ (↑c : set (M × M))⟩

@[simp] lemma mem_coe {c : con M} {x y : M} :
  (x, y) ∈ (↑c : submonoid (M × M)) ↔ (x, y) ∈ c := iff.rfl

lemma mem_iff_rel {c : con M} {x y : M} : (x, y) ∈ c ↔ c x y := iff.rfl

theorem to_submonoid_inj (c d : con M) (H : (c : submonoid (M × M)) = d) : c = d :=
ext $ λ x y, show (x,y) ∈ (c : submonoid (M × M)) ↔ (x,y) ∈ ↑d, by rw H

instance : partial_order (con M) :=
{ le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c, le_def'.2 $ lattice.complete_lattice.le_refl ↑c,
  le_trans := λ c1 c2 c3 h1 h2, le_def'.2 $ complete_lattice.le_trans ↑c1 ↑c2 ↑c3 h1 h2,
  lt_iff_le_not_le := λ _ _, ⟨λ h, h, λ h, h⟩,
  le_antisymm := λ c d h1 h2, to_submonoid_inj c d $ complete_lattice.le_antisymm ↑c ↑d h1 h2 }

instance : has_bot (con M) :=
⟨of_submonoid (submonoid.diag M) ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩

@[simp] lemma bot_coe : ↑(⊥ : con M) = (submonoid.diag M) := rfl

@[simp] lemma mem_bot {x y : M} : (x, y) ∈ (⊥ : con M) ↔ x = y := iff.rfl

instance order_bot : order_bot (con M) :=
{ bot := @has_bot.bot (con M) _,
  bot_le := λ c, le_def'.2 $ (submonoid.le_def ↑⊥ ↑c).2 $ λ x h,
                 (show c x.1 x.2, by rw (mem_bot.1 h); apply c.refl),
  ..con.partial_order }

instance : has_top (con M) := ⟨con.ker (@monoid_hom.one M P _ _)⟩

@[simp] lemma top_coe : ↑(⊤ : con M) = (⊤ : submonoid (M × M)) :=
submonoid.ext $ λ x, ⟨λ h, submonoid.mem_top x, λ h, rfl⟩

@[simp] lemma mem_top {x y : M} : (x, y) ∈ (⊤ : con M) :=
by rw [←mem_coe, top_coe]; apply submonoid.mem_top

instance order_top : order_top (con M) :=
{ top := has_top.top (con M),
  le_top := λ c, le_def'.2 (by rw top_coe; exact complete_lattice.le_top ↑c),
  ..con.partial_order }

instance : has_inf (con M) :=
⟨λ c d, of_submonoid (↑c ⊓ ↑d)
  ⟨λ x, submonoid.mem_inf.2 ⟨c.refl x, d.refl x⟩,
   λ _ _ h, submonoid.mem_inf.2 ⟨c.symm (submonoid.mem_inf.1 h).1, d.symm (submonoid.mem_inf.1 h).2⟩,
   λ _ _ _ h1 h2, submonoid.mem_inf.2
     ⟨c.trans (submonoid.mem_inf.1 h1).1 (submonoid.mem_inf.1 h2).1,
      d.trans (submonoid.mem_inf.1 h1).2 (submonoid.mem_inf.1 h2).2⟩⟩⟩

instance : has_Inf (con M) :=
⟨λ s, of_submonoid (Inf (coe '' s))
  ⟨λ x, submonoid.mem_Inf.2 $ λ p ⟨c, hs, hc⟩, hc ▸ (mem_coe.2 $ c.refl x),
   λ _ _ h, submonoid.mem_Inf.2 $
     λ p ⟨c, hs, hc⟩, hc ▸ (mem_coe.2 $ c.symm $ submonoid.mem_Inf.1 h ↑c $ ⟨c, hs, rfl⟩),
   λ _ _ _ h1 h2, submonoid.mem_Inf.2 $ λ p ⟨c, hs, hc⟩, hc ▸ (mem_coe.2 $ c.trans
     (submonoid.mem_Inf.1 h1 ↑c ⟨c, hs, rfl⟩) $ submonoid.mem_Inf.1 h2 ↑c ⟨c, hs, rfl⟩)⟩⟩

lemma Inf_eq (s : set (con M)) :
  ((Inf (s : set (con M)) : con M) : submonoid (M × M)) = Inf (coe '' s) :=
by ext x; cases x; refl

lemma Inf_le' {s : set (con M)} : c ∈ s → Inf s ≤ c :=
λ h, le_def'.2 $ (Inf_eq s).symm ▸ (submonoid.Inf_le'
     (show (c : submonoid (M × M)) ∈ coe '' s, by {use c, exact ⟨h, rfl⟩}))

lemma le_Inf' (s : set (con M)) : (∀d ∈ s, c ≤ d) → c ≤ Inf s :=
λ h, le_def'.2 $ (Inf_eq s).symm ▸ (submonoid.le_Inf' $ λ d' ⟨d, hs, hd⟩, hd ▸ (le_def'.1 $ h d hs))

lemma Inf_iff (S : set (con M)) (x y : M) : (Inf S) x y ↔ (∀ p : con M, p ∈ S → p x y) :=
⟨λ h p hp, (le_def _ _).1 (Inf_le' p hp) x y h,
  by { rw [show Inf S x y ↔ (x, y) ∈ Inf S, from iff.rfl, ←mem_coe, Inf_eq, submonoid.mem_Inf],
       rintro h p' ⟨q, hm, hq⟩, rw ←hq, exact mem_coe.2 (h q hm) }⟩

instance : has_sup (con M) := ⟨λ c d, Inf { x | c ≤ x ∧ d ≤ x}⟩

instance : complete_lattice (con M) :=
{ sup := has_sup.sup,
  le_sup_left := λ c d, le_Inf' c { x | c ≤ x ∧ d ≤ x} $ λ x hx, hx.1,
  le_sup_right := λ c d, le_Inf' d { x | c ≤ x ∧ d ≤ x} $ λ x hx, hx.2,
  sup_le := λ _ _ c h1 h2, Inf_le' c ⟨h1, h2⟩,
  inf := has_inf.inf,
  inf_le_left := λ c d, le_def'.2 $ complete_lattice.inf_le_left ↑c ↑d,
  inf_le_right := λ c d, le_def'.2 $ complete_lattice.inf_le_right ↑c ↑d,
  le_inf := λ c1 c2 c3 h1 h2, le_def'.2 $
    complete_lattice.le_inf ↑c1 ↑c2 ↑c3 (le_def'.1 h1) (le_def'.1 h2),
  Sup := λ tt, Inf {t | ∀t'∈tt, t' ≤ t},
  Inf := has_Inf.Inf,
  le_Sup := λ _ _ hs, le_Inf' _ _ $ λ c' hc', hc' _ hs,
  Sup_le := λ _ _ hs, Inf_le' _ hs,
  Inf_le := λ  _ _, Inf_le' _,
  le_Inf := λ _ _, le_Inf' _ _,
  ..con.partial_order,
  ..con.order_top, ..con.order_bot }

variables (c f)

def lift (H : ∀ x y, c x y → f x = f y) : c.quotient →* P :=
{ to_fun := λ x, con.lift_on' x f $ λ a b h, H a b h,
  map_one' := by rw ←f.map_one; tidy,
  map_mul' := λ x y, con.induction_on₂ x y $
                λ m n, by simp only [f.map_mul, con.lift_on_beta, con.coe_mul]}

def lift_of_le_ker (H : c.submonoid M ≤ f.ker') : c.quotient →* P :=
c.lift f $ (con.le_def _ _).1 H

def ker_lift (f : M →* P) : (con.ker f).quotient →* P :=
(con.ker f).lift f $ λ x y h, h

variables {c f}

@[simp] lemma lift_mk' (H : ∀ x y, c x y → f x = f y) {m : M} :
  c.lift f H (c.mk' m) = f m := rfl

@[simp] lemma lift_coe (H : ∀ x y, c x y → f x = f y)  {m : M} :
  c.lift f H m = f m := rfl

@[simp] theorem lift_comp_mk' (H : ∀ x y, c x y → f x = f y) :
  (c.lift f H).comp c.mk' = f := by tidy

@[simp] lemma lift_apply_mk' (f : c.quotient →* P) :
  c.lift (f.comp c.mk') (λ x y h, by simp [con.eq.2 h]) = f :=
by ext; rcases x; refl

protected lemma lift.funext (f g : c.quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
by { rw [←lift_apply_mk' f, ← lift_apply_mk' g], congr' 1, ext, apply h x }

theorem lift_unique (H : ∀ x y, c x y → f x = f y) (g : c.quotient →* P)
  (Hg : g.comp c.mk' = f) : g = c.lift f H :=
lift.funext g (c.lift f H) $ λ x, by rw [lift_coe H, ←con.comp_mk'_apply, Hg]

theorem lift_range (H : ∀ x y, c x y → f x = f y) : (c.lift f H).range = f.range :=
submonoid.ext $ λ x,
  ⟨λ ⟨y, hy⟩, by revert hy; rcases y; exact
     (λ hy, ⟨y, hy.1, by rw [hy.2.symm, (lift_coe H).symm]; refl⟩),
   λ ⟨y, hy⟩, ⟨↑y, hy.1, by tidy⟩⟩

@[simp] lemma ker_lift_mk {x : M} :  ker_lift f x = f x := rfl

lemma ker_lift_range_eq : (ker_lift f).range = f.range :=
lift_range $ λ x y h, h

lemma injective_ker_lift (f : M →* P) : function.injective (ker_lift f) :=
λ x y, con.induction_on₂ x y $ λ w z h, con.eq.2 $ by rwa ker_lift_mk at h

def map (c d : con M) (h : c ≤ d) : c.quotient →* d.quotient :=
c.lift d.mk' $ λ x y hc, show (con.ker d.mk') x y, from
  (mk'_ker d).symm ▸ ((le_def c d).1 h x y hc)

@[simp] lemma map_apply {c d : con M} (h : c ≤ d) (x : c.quotient) :
  c.map d h x = c.lift d.mk'
    (λ x y, (le_def c $ con.ker d.mk').1 ((mk'_ker d).symm ▸ h) x y) x := rfl

variables (c)

lemma rel {x y : M} (h : @setoid.r M c.setoid x y) : c x y := h

def to_con (d : {d // c ≤ d}) : con c.quotient :=
{ r := λ x y, con.lift_on₂' x y d.1 $ λ p q r s hp hq, iff_iff_eq.1
         ⟨λ h', d.1.trans (d.1.symm ((le_def c d.1).1 d.2 p r $ rel c hp)) $
                d.1.trans h' ((le_def c d.1).1 d.2 q s $ rel c hq),
          λ h', d.1.trans ((le_def c d.1).1 d.2 p r $ rel c hp) (d.1.trans h' $
                d.1.symm ((le_def c d.1).1 d.2 q s $ rel c hq))⟩,
  r_iseqv := ⟨λ x, quotient.induction_on' x $ λ y, d.1.refl y,
              λ x y, quotient.induction_on₂' x y $ λ _ _ h', d.1.symm h',
              λ x y z, quotient.induction_on₃' x y z $ λ _ _ _ h1 h2, d.1.trans h1 h2⟩,
  r_mul := λ w x y z, quotient.induction_on₂' w x $
             λ _ _, quotient.induction_on₂' y z $ λ _ _ h1 h2, d.1.mul h1 h2 }

def of_con (d : con c.quotient) : con M :=
{ r := λ x y, d ↑x ↑y,
  r_iseqv := ⟨λ x, d.refl ↑x, λ _ _ h, d.symm h, λ _ _ _ h1 h2, d.trans h1 h2⟩,
  r_mul := by intros; rw [←coe_mul, ←coe_mul]; exact d.mul a a_1 }

lemma le_of_con (d : con c.quotient) : c ≤ c.of_con d :=
(le_def c $ c.of_con d).2 $ λ x y h, show d x y, from (con.eq.2 h) ▸ d.refl x

theorem left_inverse (d : {d // c ≤ d}) : c.of_con (c.to_con d) = d.1 :=
by ext; refl

theorem right_inverse (d : con c.quotient) : c.to_con ⟨(c.of_con d), (c.le_of_con d)⟩ = d :=
by ext; rcases x; rcases y; refl

variables {f}

/-- First Isomorphism Theorem-/
noncomputable def quotient_ker_equiv_range (f : M →* P) : (con.ker f).quotient ≃* f.range :=
{ map_mul' := monoid_hom.map_mul _,
  ..@equiv.of_bijective _ _
      ((mul_equiv.submonoid.to_monoid_hom (mul_equiv.submonoid_congr ker_lift_range_eq)).comp
        (ker_lift f).range_mk) $
      function.bijective_comp (equiv.bijective _)
        ⟨λ x y h, injective_ker_lift f $ by rcases x; rcases y; injections, by simp⟩ }

lemma lift_surjective_of_surjective (hf : function.surjective f) : function.surjective (ker_lift f) :=
λ y, exists.elim (hf y) $ λ w hw, ⟨w, by tidy⟩

noncomputable def quotient_ker_equiv_of_surjective (f : M →* P) (hf : function.surjective f) :
  (con.ker f).quotient ≃* P :=
{ map_mul' := monoid_hom.map_mul _,
  ..(@equiv.of_bijective _ _ (ker_lift f) ⟨injective_ker_lift f, lift_surjective_of_surjective hf⟩) }

lemma subtype_eq (A : submonoid M) : c.subtype A = con.ker (c.mk'.comp A.subtype) :=
con.ext $ λ x y,
  ⟨λ h, show ((x : M) : c.quotient) = (y : M), from con.eq.2 $ c.subtype_apply.2 h,
   λ h, by rw [subtype_apply, ←mk'_ker c]; simpa using h⟩

/-- Second Isomorphism Theorem -/
noncomputable def submonoid_quotient_equiv (A : submonoid M) :
  (c.subtype A).quotient ≃* (c.mk'.comp A.subtype).range :=
mul_equiv.trans (congr (subtype_eq c A)) $ quotient_ker_equiv_range (c.mk'.comp A.subtype)

lemma surjective_of_con_lift (d : con M) (h : c ≤ d) : function.surjective (c.map d h) :=
λ x, by rcases x; exact ⟨x, rfl⟩

/-- Third Isomorphism Theorem -/
noncomputable def quotient_quotient_equiv_quotient (c d : con M) (h : c ≤ d) :
  (con.ker (c.map d h)).quotient ≃* d.quotient :=
quotient_ker_equiv_of_surjective _ $ surjective_of_con_lift c d h

--/-- Fourth Isomorphism Theorem -/
def correspondence : ((≤) : {d // c ≤ d} → {d // c ≤ d} → Prop) ≃o
((≤) : con c.quotient → con c.quotient → Prop) :=
{ to_fun := λ d, c.to_con d,
  inv_fun := λ d, subtype.mk (c.of_con d) (c.le_of_con d),
  left_inv := λ d, by simp [c.left_inverse d],
  right_inv := λ d, by simp [c.right_inverse d],
  ord := λ a b,
    ⟨λ hle, (le_def _ _).2 $ λ x y, con.induction_on₂ x y $
       λ w z h, by apply (le_def _ _).1 hle w z h,
     λ H, (le_def _ _).2 $ λ p q h, by apply (le_def _ _).1 H (p : _) (q : _) h⟩ }

end con
