/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Ordinal arithmetic.

Ordinals are defined as equivalences of well-ordered sets by order isomorphism.
-/
import data.cardinal
noncomputable theory

open function
local attribute [instance] classical.prop_decidable

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

def is_irrefl_of_is_asymm [is_asymm α r] : is_irrefl α r :=
⟨λ a h, asymm h h⟩

def is_irrefl.swap (r) [is_irrefl α r] : is_irrefl α (swap r) :=
⟨@irrefl α r _⟩

def is_trans.swap (r) [is_trans α r] : is_trans α (swap r) :=
⟨λ a b c h₁ h₂, (trans h₂ h₁ : r c a)⟩

def is_strict_order.swap (r) [is_strict_order α r] : is_strict_order α (swap r) :=
⟨is_irrefl.swap r, is_trans.swap r⟩

@[algebra] class is_strict_total_order' (α : Type u) (lt : α → α → Prop) extends is_trichotomous α lt, is_strict_order α lt : Prop.

def is_trichotomous.swap (r) [is_trichotomous α r] : is_trichotomous α (swap r) :=
⟨λ a b, by simpa [swap, or_comm, or.left_comm] using @trichotomous _ r _ a b⟩

def is_strict_total_order'.swap (r) [is_strict_total_order' α r] : is_strict_total_order' α (swap r) :=
⟨is_trichotomous.swap r, is_strict_order.swap r⟩

@[algebra] class is_order_connected (α : Type u) (lt : α → α → Prop) : Prop :=
(conn : ∀ a b c, lt a c → lt a b ∨ lt b c)

def is_strict_weak_order_of_is_order_connected [is_asymm α r] :
  ∀ [is_order_connected α r], is_strict_weak_order α r
| ⟨H⟩ := ⟨⟨is_irrefl_of_is_asymm,
  ⟨λ a b c h₁ h₂, (H _ c _ h₁).resolve_right (asymm h₂)⟩⟩,
  ⟨λ a b c ⟨h₁, h₂⟩ ⟨h₃, h₄⟩,
    have H' : ∀ {a b c}, ¬ r a b → ¬ r b c → ¬ r a c,
    from λ a b c, by simpa [not_or_distrib] using mt (H a b c),
    ⟨H' h₁ h₃, H' h₄ h₂⟩⟩⟩

instance is_strict_total_order_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_strict_total_order α r :=
⟨by apply_instance,
 suffices is_order_connected α r,
   by exact is_strict_weak_order_of_is_order_connected,
 ⟨λ a b c h, (trichotomous _ _).imp_right (λ o,
    o.elim (λ e, e ▸ h) (λ h', trans h' h))⟩⟩

@[algebra] class is_extensional (α : Type u) (r : α → α → Prop) : Prop :=
(ext : ∀ a b, (∀ x, r x a ↔ r x b) → a = b)

instance is_extensional_of_is_strict_total_order'
  [is_strict_total_order' α r] : is_extensional α r :=
⟨λ a b H, ((@trichotomous _ r _ a b)
  .resolve_left $ mt (H _).2 (irrefl a))
  .resolve_right $ mt (H _).1 (irrefl b)⟩

@[algebra] class is_well_order (α : Type u) (r : α → α → Prop) extends is_strict_total_order' α r : Prop :=
(wf : well_founded r)

structure order_embedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends embedding α β :=
(ord : ∀ {a b}, r a b ↔ s (to_embedding a) (to_embedding b))

local infix ` ≼o `:50 := order_embedding

def order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) := s (f x) (f y)

local infix ` ⁻¹'o `:80 := order.preimage

namespace order_embedding

instance : has_coe_to_fun (r ≼o s) := ⟨λ _, α → β, λ o, o.to_embedding⟩

theorem ord' : ∀ (f : r ≼o s) {a b}, r a b ↔ s (f a) (f b)
| ⟨f, o⟩ := @o

@[simp] theorem coe_fn_mk (f : embedding α β) (o) :
  (@order_embedding.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_embedding (f : r ≼o s) : (f.to_embedding : α → β) = f := rfl

theorem eq_of_to_fun_eq : ∀ {e₁ e₂ : r ≼o s}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨⟨f₁, h₁⟩, o₁⟩ ⟨⟨f₂, h₂⟩, o₂⟩ h := by congr; exact h

@[refl] protected def refl (r : α → α → Prop) : r ≼o r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

@[trans] protected def trans : r ≼o s → s ≼o t → r ≼o t
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ := ⟨f₁.trans f₂, λ a b, by rw [o₁, o₂]; simp⟩

@[simp] theorem refl_apply (x : α) : order_embedding.refl r x = x := rfl

@[simp] theorem trans_apply : ∀ (f : r ≼o s) (g : s ≼o t) (a : α), (f.trans g) a = g (f a)
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ a := rfl

def rsymm (f : r ≼o s) : swap r ≼o swap s :=
⟨f.to_embedding, λ a b, f.ord'⟩

theorem eq_preimage (f : r ≼o s) : r = f ⁻¹'o s :=
by funext a b; exact propext f.ord'

protected def is_irrefl : ∀ (f : r ≼o s) [is_irrefl β s], is_irrefl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a h, H _ (o.1 h)⟩

protected def is_refl : ∀ (f : r ≼o s) [is_refl β s], is_refl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a, o.2 (H _)⟩

protected def is_symm : ∀ (f : r ≼o s) [is_symm β s], is_symm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h, o.2 (H _ _ (o.1 h))⟩

protected def is_asymm : ∀ (f : r ≼o s) [is_asymm β s], is_asymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (o.1 h₁) (o.1 h₂)⟩

protected def is_antisymm : ∀ (f : r ≼o s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.1 h₁) (o.1 h₂))⟩

protected def is_trans : ∀ (f : r ≼o s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.2 (H _ _ _ (o.1 h₁) (o.1 h₂))⟩

protected def is_total : ∀ (f : r ≼o s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).2 (H _ _)⟩

protected def is_preorder : ∀ (f : r ≼o s) [is_preorder β s], is_preorder α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_refl, f.is_trans⟩

protected def is_partial_order : ∀ (f : r ≼o s) [is_partial_order β s], is_partial_order α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_preorder, f.is_antisymm⟩

protected def is_linear_order : ∀ (f : r ≼o s) [is_linear_order β s], is_linear_order α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_partial_order, f.is_total⟩

protected def is_strict_order : ∀ (f : r ≼o s) [is_strict_order β s], is_strict_order α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_irrefl, f.is_trans⟩

protected def is_trichotomous : ∀ (f : r ≼o s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff.symm o)).2 (H _ _)⟩

protected def is_strict_total_order' : ∀ (f : r ≼o s) [is_strict_total_order' β s], is_strict_total_order' α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_trichotomous, f.is_strict_order⟩

protected theorem acc (f : r ≼o s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.ord'.1 h) _ rfl⟩
end

protected def well_founded : ∀ (f : r ≼o s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected def is_well_order : ∀ (f : r ≼o s) [is_well_order β s], is_well_order α r
| f ⟨H₁, H₂⟩ := by exact ⟨f.is_strict_total_order', f.well_founded H₂⟩

theorem of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) : r ≼o s :=
begin
  have := @is_irrefl_of_is_asymm β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨H _ _, λ h, _⟩⟩,
  { refine ((@trichotomous _ r _ a b).resolve_left _).resolve_right _;
    exact λ h, @irrefl _ s _ _ (by simpa [e] using H _ _ h) },
  { refine (@trichotomous _ r _ a b).resolve_right (or.rec (λ e, _) (λ h', _)),
    { subst e, exact irrefl _ h },
    { exact asymm (H _ _ h') h } }
end

theorem nat_lt [is_strict_order α r] (f : ℕ → α) (H : ∀ n:ℕ, r (f n) (f (n+1))) :
  ((<) : ℕ → ℕ → Prop) ≼o r :=
of_monotone f $ λ a b h, begin
  induction b with b IH, {exact (nat.not_lt_zero _ h).elim},
  cases nat.lt_succ_iff_lt_or_eq.1 h with h e,
  { exact trans (IH h) (H _) },
  { subst b, apply H }
end

theorem well_founded_iff_no_descending_seq [is_strict_order α r] : well_founded r ↔ ¬ nonempty (((>) : ℕ → ℕ → Prop) ≼o r) :=
⟨λ ⟨h⟩ ⟨⟨f, o⟩⟩,
  suffices ∀ a, acc r a → ∀ n, a ≠ f n, from this (f 0) (h _) 0 rfl,
  λ a ac, begin
    induction ac with a _ IH, intros n h, subst a,
    exact IH (f (n+1)) (o.1 (nat.lt_succ_self _)) _ rfl
  end,
λ N, ⟨λ a, classical.by_contradiction $ λ na,
  let ⟨f, h⟩ := classical.axiom_of_choice $
    show ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    from λ ⟨x, h⟩, classical.by_contradiction $ λ hn, h $
      ⟨_, λ y h, classical.by_contradiction $ λ na, hn ⟨⟨y, na⟩, h⟩⟩ in
  N ⟨rsymm $ @nat_lt _ _ (is_strict_order.swap r)
    (λ n, (n.foldr f ⟨a, na⟩).1) $ λ n, h _⟩⟩⟩

end order_embedding

structure order_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(ord : ∀ {a b}, r a b ↔ s (to_equiv a) (to_equiv b))

local infix ` ≃o `:50 := order_iso

namespace order_iso

instance : has_coe (r ≃o s) (r ≼o s) := ⟨λ o, ⟨o.to_equiv.to_embedding, o.ord⟩⟩

@[simp] theorem coe_coe_fn (f : r ≃o s) : ((f : r ≼o s) : α → β) = f := rfl

theorem ord' : ∀ (f : r ≃o s) {a b}, r a b ↔ s (f a) (f b)
| ⟨f, o⟩ := @o

@[simp] theorem coe_fn_mk (f : α ≃ β) (o) :
  (@order_iso.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃o s) : (f.to_equiv : α → β) = f := rfl

theorem eq_of_to_fun_eq : ∀ {e₁ e₂ : r ≃o s}, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by congr; exact equiv.eq_of_to_fun_eq h

@[refl] protected def refl (r : α → α → Prop) : r ≃o r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

@[symm] protected def symm : r ≃o s → s ≃o r
| ⟨f, o⟩ := ⟨f.symm, λ a b, by rw o; simp⟩

@[trans] protected def trans : r ≃o s → s ≃o t → r ≃o t
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ := ⟨f₁.trans f₂, λ a b, by rw [o₁, o₂]; simp⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@order_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem refl_apply (x : α) : order_iso.refl r x = x := rfl

@[simp] theorem trans_apply : ∀ (f : r ≃o s) (g : s ≃o t) (a : α), (f.trans g) a = g (f a)
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ a := equiv.trans_apply _ _ _

@[simp] theorem apply_inverse_apply : ∀ (e : r ≃o s) (x : β), e (e.symm x) = x
| ⟨f₁, o₁⟩ x := by simp

@[simp] theorem inverse_apply_apply : ∀ (e : r ≃o s) (x : α), e.symm (e x) = x
| ⟨f₁, o₁⟩ x := by simp

def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃o s := ⟨f, λ a b, iff.rfl⟩

def of_surjective (f : r ≼o s) (H : surjective f) : r ≃o s :=
⟨equiv.of_bijective ⟨f.inj, H⟩, by simp [f.ord']⟩

@[simp] theorem of_surjective_apply (f : r ≼o s) (H) (a : α) : of_surjective f H a = f a :=
by delta of_surjective; simp

end order_iso

def set_coe_embedding {α : Type*} (r : α → α → Prop) (p : set α) :
  embedding p α := ⟨subtype.val, @subtype.eq _ _⟩

structure initial_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(init : ∀ a b, s b (to_order_embedding a) → ∃ a', to_order_embedding a' = b)

local infix ` ≼i `:50 := initial_seg

namespace initial_seg

instance : has_coe (r ≼i s) (r ≼o s) := ⟨initial_seg.to_order_embedding⟩

@[simp] theorem coe_fn_mk (f : r ≼o s) (o) :
  (@initial_seg.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_order_embedding (f : r ≼i s) : (f.to_order_embedding : α → β) = f := rfl

theorem init' (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
f.init _ _

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
⟨λ h, let ⟨a', e⟩ := f.init' h in ⟨a', e, (f : r ≼o s).ord'.2 (e.symm ▸ h)⟩,
 λ ⟨a', e, h⟩, e ▸ (f : r ≼o s).ord'.1 h⟩

def of_iso (f : r ≃o s) : r ≼i s :=
⟨f, λ a b h, ⟨f.symm b, order_iso.apply_inverse_apply f _⟩⟩

@[refl] protected def refl (r : α → α → Prop) : r ≼i r :=
⟨order_embedding.refl _, λ a b h, ⟨_, rfl⟩⟩

@[trans] protected def trans : r ≼i s → s ≼i t → r ≼i t
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ := ⟨f₁.trans f₂, λ a c h, begin
  simp at h ⊢,
  rcases o₂ _ _ h with ⟨b, rfl⟩, have h := f₂.ord'.2 h,
  rcases o₁ _ _ h with ⟨a', rfl⟩, exact ⟨a', rfl⟩
end⟩

@[simp] theorem of_iso_apply (f : r ≃o s) (x : α) : of_iso f x = f x := rfl

@[simp] theorem refl_apply (x : α) : initial_seg.refl r x = x := rfl

@[simp] theorem trans_apply : ∀ (f : r ≼i s) (g : s ≼i t) (a : α), (f.trans g) a = g (f a)
| ⟨f₁, o₁⟩ ⟨f₂, o₂⟩ a := order_embedding.trans_apply _ _ _

def unique_of_extensional [is_extensional β s] :
  well_founded r → subsingleton (r ≼i s) | ⟨h⟩ :=
⟨λ f g, begin
  suffices : (f : α → β) = g, { cases f, cases g,
    congr, exact order_embedding.eq_of_to_fun_eq this },
  funext a, have := h a, induction this with a H IH,
  refine @is_extensional.ext _ s _ _ _ (λ x, ⟨λ h, _, λ h, _⟩),
  { rcases f.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw IH _ h', exact (g : r ≼o s).ord'.1 h' },
  { rcases g.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw ← IH _ h', exact (f : r ≼o s).ord'.1 h' }
end⟩

instance [is_well_order β s] : subsingleton (r ≼i s) :=
⟨λ a, @subsingleton.elim _ (unique_of_extensional
  (@order_embedding.well_founded _ _ r s a (is_well_order.wf s))) a⟩

theorem antisymm.aux [is_well_order α r] (f : r ≼i s) (g : s ≼i r) : left_inverse g f
| x := begin
  have := ((is_well_order.wf r).apply x), induction this with x _ IH,
  refine @is_extensional.ext _ r _ _ _ (λ y, _),
  simp only [g.init_iff, f.init_iff],
  split; intro h,
  { rcases h with ⟨a, rfl, b, rfl, h⟩, rwa IH _ h },
  { exact ⟨f y, IH _ h, y, rfl, h⟩ }
end

def antisymm [is_well_order β s] (f : r ≼i s) (g : s ≼i r) : r ≃o s :=
by have := f.to_order_embedding.is_well_order; exact
⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, f.ord⟩

@[simp] theorem antisymm_to_fun [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f := rfl

@[simp] theorem antisymm_symm [is_well_order α r] [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g).symm = antisymm g f :=
order_iso.eq_of_to_fun_eq $ by dunfold initial_seg.antisymm; simp

theorem eq_or_principal [is_well_order β s] (f : r ≼i s) : surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
or_iff_not_imp_right.2 $ λ h b,
acc.rec_on ((is_well_order.wf s).apply b) $ λ x H IH,
not_forall_not.1 $ λ hn,
h ⟨x, λ y, ⟨(IH _), λ ⟨a, e⟩, by rw ← e; exact
  (trichotomous _ _).resolve_right
  (not_or (hn a) (λ hl, not_exists.2 hn (f.init' hl)))⟩⟩

end initial_seg

structure principal_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(top : β)
(down : ∀ b, s b top ↔ ∃ a, to_order_embedding a = b)

local infix ` ≺i `:50 := principal_seg

namespace principal_seg

instance : has_coe (r ≺i s) (r ≼o s) := ⟨principal_seg.to_order_embedding⟩

@[simp] theorem coe_fn_mk (f : r ≼o s) (t o) :
  (@principal_seg.mk _ _ r s f t o : α → β) = f := rfl

@[simp] theorem coe_fn_to_order_embedding (f : r ≺i s) : (f.to_order_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≺i s) : ((f : r ≼o s) : α → β) = f := rfl

theorem down' (f : r ≺i s) {b : β} : s b f.top ↔ ∃ a, f a = b :=
f.down _

theorem init [is_trans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
f.down'.1 $ trans h $ f.down'.2 ⟨_, rfl⟩

instance has_coe_initial_seg [is_trans β s] : has_coe (r ≺i s) (r ≼i s) :=
⟨λ f, ⟨f.to_order_embedding, λ a b, f.init⟩⟩

@[simp] theorem coe_coe_fn' [is_trans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f := rfl

theorem init_iff [is_trans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
initial_seg.init_iff f

theorem irrefl (r : α → α → Prop) [is_well_order α r] (f : r ≺i r) : false :=
begin
  have := f.down'.2 ⟨f.top, rfl⟩,
  rw [show f f.top = f.top, from congr_arg (λ g : r ≼i r, g f.top)
    (subsingleton.elim ↑f (initial_seg.refl r))] at this,
  exact irrefl _ this
end

def lt_le [is_trans β s] (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
⟨@order_embedding.trans _ _ _ r s t f g, g f.top, λ a,
 by simp [g.init_iff, f.down', exists_and_distrib_left.symm,
          -exists_and_distrib_left, exists_swap]; refl⟩

@[simp] theorem lt_le_apply [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≼i t) (a : α) : (f.lt_le g) a = g (f a) :=
order_embedding.trans_apply _ _ _

@[trans] protected def trans [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
lt_le f g

@[simp] theorem trans_apply [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
lt_le_apply _ _ _

def equiv_lt [is_trans β s] [is_trans γ t] (f : r ≃o s) (g : s ≺i t) : r ≺i t :=
⟨@order_embedding.trans _ _ _ r s t f g, g.top, λ c,
 by simp [g.down']; exact
 ⟨λ ⟨b, h⟩, ⟨f.symm b, by simp [h]⟩, λ ⟨a, h⟩, ⟨f a, h⟩⟩⟩

@[simp] theorem equiv_lt_apply [is_trans β s] [is_trans γ t] (f : r ≃o s) (g : s ≺i t) (a : α) : (equiv_lt f g) a = g (f a) :=
by delta equiv_lt; simp

def le_lt [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) : r ≺i t :=
have h : ∃ top, ∀ b, t b top ↔ ∃ a, g (f a) = b, begin
  rcases initial_seg.eq_or_principal f with h | ⟨b, h⟩,
  { let := equiv_lt (order_iso.of_surjective ↑f h) g,
    existsi this.top, simpa using this.down },
  { let := @principal_seg.trans _ _ _ r s t _ _ ⟨f, b, h⟩ g,
    existsi g b, simpa using this.down }
end,
⟨@order_embedding.trans _ _ _ r s t f g, classical.some h,
λ b, by simp [classical.some_spec h]; refl⟩

@[simp] theorem le_lt_apply [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) (a : α) : (le_lt f g) a = g (f a) :=
order_embedding.trans_apply _ _ _

instance [is_well_order β s] : subsingleton (r ≺i s) :=
⟨λ f g, begin
  have ef : (f : α → β) = g,
  { show ((f : r ≼i s) : α → β) = g,
    rw @subsingleton.elim _ _ (f : r ≼i s) g, refl },
  have et : f.top = g.top,
  { refine @is_extensional.ext _ s _ _ _ (λ x, _),
    simp [f.down, g.down, ef] },
  cases f, cases g, simp at ef et,
  congr; [apply order_embedding.eq_of_to_fun_eq, skip]; assumption
end⟩

end principal_seg

structure Well_order : Type (u+1) :=
(α : Type u)
(r : α → α → Prop)
(wo : is_well_order α r)

namespace Well_order

protected def equiv : Well_order → Well_order → Prop
| ⟨α, r, wo⟩ ⟨β, s, wo'⟩ := nonempty (r ≃o s)

protected def le : Well_order → Well_order → Prop
| ⟨α, r, wo⟩ ⟨β, s, wo'⟩ := nonempty (r ≼i s)

protected def lt : Well_order → Well_order → Prop
| ⟨α, r, wo⟩ ⟨β, s, wo'⟩ := nonempty (r ≺i s)

end Well_order

instance ordinal.is_equivalent : setoid Well_order :=
{ r     := Well_order.equiv,
  iseqv := ⟨λ⟨α, r, _⟩, ⟨order_iso.refl _⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, ⟨e.symm⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

def ordinal : Type (u + 1) := quotient ordinal.is_equivalent

namespace ordinal

def le (a b : ordinal) : Prop :=
quotient.lift_on₂ a b Well_order.le $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
propext ⟨
  λ ⟨h⟩, ⟨(initial_seg.of_iso f.symm).trans $
    h.trans (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨(initial_seg.of_iso f).trans $
    h.trans (initial_seg.of_iso g.symm)⟩⟩

def lt (a b : ordinal) : Prop :=
quotient.lift_on₂ a b Well_order.lt $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
by exact propext ⟨
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f.symm $
    h.lt_le (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f $
    h.lt_le (initial_seg.of_iso g.symm)⟩⟩

def card (o : ordinal) : cardinal :=
quot.lift_on o (λ ⟨α, r, _⟩, ⟦α⟧) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, quotient.sound ⟨e.to_equiv⟩

end ordinal
