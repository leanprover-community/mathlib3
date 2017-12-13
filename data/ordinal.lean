/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

Ordinal arithmetic.

Ordinals are defined as equivalences of well-ordered sets by order isomorphism.
-/
import data.cardinal data.sum
noncomputable theory

open function cardinal
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

def empty_relation.is_well_order [subsingleton α] : is_well_order α empty_relation :=
⟨⟨⟨λ a b, or.inr $ or.inl $ subsingleton.elim _ _⟩,
  ⟨λ a, id⟩, ⟨λ a b c, false.elim⟩⟩,
  ⟨λ a, ⟨_, λ y, false.elim⟩⟩⟩

def sum.lex.is_well_order [is_well_order α r] [is_well_order β s] : is_well_order (α ⊕ β) (sum.lex r s) :=
⟨⟨⟨λ a b, by cases a; cases b; simp; apply trichotomous⟩,
  ⟨λ a, by cases a; simp; apply irrefl⟩,
  ⟨λ a b c, by cases a; cases b; simp; cases c; simp; apply trans⟩⟩,
  sum.lex_wf (is_well_order.wf r) (is_well_order.wf s)⟩

def prod.lex.is_well_order [is_well_order α r] [is_well_order β s] : is_well_order (α × β) (prod.lex r s) :=
⟨⟨⟨λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩, match @trichotomous _ r _ a₁ b₁ with
    | or.inl h₁ := or.inl $ prod.lex.left _ _ _ h₁
    | or.inr (or.inr h₁) := or.inr $ or.inr $ prod.lex.left _ _ _ h₁
    | or.inr (or.inl e) := e ▸  match @trichotomous _ s _ a₂ b₂ with
      | or.inl h := or.inl $ prod.lex.right _ _ h
      | or.inr (or.inr h) := or.inr $ or.inr $ prod.lex.right _ _ h
      | or.inr (or.inl e) := e ▸ or.inr $ or.inl rfl
      end
    end⟩,
  ⟨λ ⟨a₁, a₂⟩ h, by cases h with _ _ _ _ h _ _ _ h;
     [exact irrefl _ h, exact irrefl _ h]⟩,
  ⟨λ a b c h₁ h₂, begin
    cases h₁ with a₁ a₂ b₁ b₂ ab a₁ b₁ b₂ ab;
    cases h₂ with _ _ c₁ c₂ bc _ _ c₂ bc,
    { exact prod.lex.left _ _ _ (trans ab bc) },
    { exact prod.lex.left _ _ _ ab },
    { exact prod.lex.left _ _ _ bc },
    { exact prod.lex.right _ _ (trans ab bc) }
  end⟩⟩,
  prod.lex_wf (is_well_order.wf r) (is_well_order.wf s)⟩

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

def set_coe_embedding {α : Type*} (p : set α) :
  embedding p α := ⟨subtype.val, @subtype.eq _ _⟩

def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
@subtype.val _ p ⁻¹'o r 

namespace subrel

protected def order_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ≼o r := ⟨set_coe_embedding _, λ a b, iff.rfl⟩

instance (r : α → α → Prop) [is_well_order α r]
  (p : set α) : is_well_order p (subrel r p) :=
order_embedding.is_well_order (subrel.order_embedding r p)

end subrel

def order_embedding.cod_restrict (p : set β) (f : r ≼o s) (H : ∀ a, f a ∈ p) : r ≼o subrel s p :=
⟨⟨λ a, ⟨f a, H a⟩, λ a b h, f.to_embedding.inj
  (@congr_arg _ _ _ _ subtype.val h)⟩, f.ord⟩

@[simp] theorem order_embedding.cod_restrict_apply (p) (f : r ≼o s) (H a) :
  order_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl

structure initial_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ≼o s :=
(init : ∀ a b, s b (to_order_embedding a) → ∃ a', to_order_embedding a' = b)

local infix ` ≼i `:50 := initial_seg

namespace initial_seg

instance : has_coe (r ≼i s) (r ≼o s) := ⟨initial_seg.to_order_embedding⟩

@[simp] theorem coe_fn_mk (f : r ≼o s) (o) :
  (@initial_seg.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_order_embedding (f : r ≼i s) : (f.to_order_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≼i s) : ((f : r ≼o s) : α → β) = f := rfl

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

def cod_restrict (p : set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i subrel s p :=
⟨order_embedding.cod_restrict p f H, λ a ⟨b, m⟩ (h : s b (f a)),
  let ⟨a', e⟩ := f.init' h in ⟨a', by clear _let_match; subst e; refl⟩⟩

@[simp] theorem cod_restrict_apply (p) (f : r ≼i s) (H a) : cod_restrict p f H a = ⟨f a, H a⟩ := rfl

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

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
f.down'.2 ⟨_, rfl⟩

theorem init [is_trans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
f.down'.1 $ trans h $ f.lt_top _

instance has_coe_initial_seg [is_trans β s] : has_coe (r ≺i s) (r ≼i s) :=
⟨λ f, ⟨f.to_order_embedding, λ a b, f.init⟩⟩

@[simp] theorem coe_coe_fn' [is_trans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f := rfl

theorem init_iff [is_trans β s] (f : r ≺i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
initial_seg.init_iff f

theorem irrefl (r : α → α → Prop) [is_well_order α r] (f : r ≺i r) : false :=
begin
  have := f.lt_top f.top,
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

@[simp] theorem lt_le_top [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≼i t) : (f.lt_le g).top = g f.top := rfl

@[trans] protected def trans [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
lt_le f g

@[simp] theorem trans_apply [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) : (f.trans g) a = g (f a) :=
lt_le_apply _ _ _

@[simp] theorem trans_top [is_trans β s] [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : (f.trans g).top = g f.top := rfl

def equiv_lt [is_trans β s] [is_trans γ t] (f : r ≃o s) (g : s ≺i t) : r ≺i t :=
⟨@order_embedding.trans _ _ _ r s t f g, g.top, λ c,
 by simp [g.down']; exact
 ⟨λ ⟨b, h⟩, ⟨f.symm b, by simp [h]⟩, λ ⟨a, h⟩, ⟨f a, h⟩⟩⟩

@[simp] theorem equiv_lt_apply [is_trans β s] [is_trans γ t] (f : r ≃o s) (g : s ≺i t) (a : α) : (equiv_lt f g) a = g (f a) :=
by delta equiv_lt; simp

@[simp] theorem equiv_lt_top [is_trans β s] [is_trans γ t] (f : r ≃o s) (g : s ≺i t) : (equiv_lt f g).top = g.top := rfl

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

theorem top_eq [is_well_order β s] [is_well_order γ t]
  (e : r ≃o s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top :=
by rw subsingleton.elim f (principal_seg.equiv_lt e g); simp

def of_element {α : Type*} (r : α → α → Prop) [is_well_order α r] (a : α) :
  subrel r {b | r b a} ≺i r :=
⟨subrel.order_embedding _ _, a, λ b,
  ⟨λ h, ⟨⟨_, h⟩, rfl⟩, λ ⟨⟨_, h⟩, rfl⟩, h⟩⟩

@[simp] theorem of_element_apply {α : Type*} (r : α → α → Prop) [is_well_order α r] (a : α) (b) :
  of_element r a b = b.1 := rfl

@[simp] theorem of_element_top {α : Type*} (r : α → α → Prop) [is_well_order α r] (a : α) :
  (of_element r a).top = a := rfl

def cod_restrict
  (p : set β) (f : r ≺i s) (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i subrel s p :=
⟨order_embedding.cod_restrict p f H, ⟨f.top, H₂⟩, λ ⟨b, h⟩,
  f.down'.trans $ exists_congr $ λ a,
  show (⟨f a, H a⟩ : p).1 = _ ↔ _, from ⟨subtype.eq, congr_arg _⟩⟩

@[simp] theorem cod_restrict_apply (p) (f : r ≺i s) (H H₂ a) : cod_restrict p f H H₂ a = ⟨f a, H a⟩ := rfl

@[simp] theorem cod_restrict_top (p) (f : r ≺i s) (H H₂) : (cod_restrict p f H H₂).top = ⟨f.top, H₂⟩ := rfl

end principal_seg

def initial_seg.lt_or_eq [is_well_order β s] (f : r ≼i s) : r ≺i s ⊕ r ≃o s :=
if h : surjective f then sum.inr (order_iso.of_surjective f h) else
have h' : _, from (initial_seg.eq_or_principal f).resolve_left h,
sum.inl ⟨f, classical.some h', classical.some_spec h'⟩

@[simp] theorem initial_seg.lt_or_eq_apply_left [is_well_order β s]
  (f : r ≼i s) {g} (h : f.lt_or_eq = sum.inl g) (a : α) : g a = f a :=
begin
  unfold initial_seg.lt_or_eq at h,
  by_cases surjective f with sj; simp [sj] at h,
  {injection h}, {subst h, refl}
end

@[simp] theorem initial_seg.lt_or_eq_apply_right [is_well_order β s]
  (f : r ≼i s) {g} (h : f.lt_or_eq = sum.inr g) (a : α) : g a = f a :=
begin
  unfold initial_seg.lt_or_eq at h,
  by_cases surjective f with sj; simp [sj] at h,
  {subst g, simp}, {injection h}
end

def initial_seg.le_lt [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) : r ≺i t :=
match f.lt_or_eq with
| sum.inl f' := f'.trans g
| sum.inr f' := principal_seg.equiv_lt f' g
end

@[simp] theorem initial_seg.le_lt_apply [is_well_order β s] [is_trans γ t]
  (f : r ≼i s) (g : s ≺i t) (a : α) : (f.le_lt g) a = g (f a) :=
begin
  delta initial_seg.le_lt, cases h : f.lt_or_eq with f' f',
  { simp [f.lt_or_eq_apply_left h] },
  { simp [f.lt_or_eq_apply_right h] }
end

section well_ordering_thm
parameter {σ : Type*}

private def partial_wo := Σ p : set σ, {r // is_well_order p r}

private def partial_wo.le (x y : partial_wo) := ∃ f : x.2.1 ≼i y.2.1, ∀ x, (f x).1 = x.1

local infix ` ≤ `:50 := partial_wo.le

private def partial_wo.is_refl : is_refl _ (≤) :=
⟨λ a, ⟨initial_seg.refl _, λ x, rfl⟩⟩
local attribute [instance] partial_wo.is_refl

private def partial_wo.trans {a b c} : a ≤ b → b ≤ c → a ≤ c
| ⟨f, hf⟩ ⟨g, hg⟩ := ⟨f.trans g, λ a, by simp [hf, hg]⟩

private def sub_of_le {s t} : s ≤ t → s.1 ⊆ t.1
| ⟨f, hf⟩ x h := by have := (f ⟨x, h⟩).2; rwa [hf ⟨x, h⟩] at this

private def agree_of_le {s t} : s ≤ t → ∀ {a b} sa sb ta tb,
  s.2.1 ⟨a, sa⟩ ⟨b, sb⟩ ↔ t.2.1 ⟨a, ta⟩ ⟨b, tb⟩
| ⟨f, hf⟩ a b sa sb ta tb := by rw [f.to_order_embedding.ord',
  show f.to_order_embedding ⟨a, sa⟩ = ⟨a, ta⟩, from subtype.eq (hf ⟨a, sa⟩),
  show f.to_order_embedding ⟨b, sb⟩ = ⟨b, tb⟩, from subtype.eq (hf ⟨b, sb⟩)]

section
parameters {c : set partial_wo} (hc : @zorn.chain _ (≤) c)

private def U := ⋃₀ ((λ x:partial_wo, x.1) '' c)

private def R (x y : U) := ∃ a : partial_wo, a ∈ c ∧
  ∃ (hx : x.1 ∈ a.1) (hy : y.1 ∈ a.1), a.2.1 ⟨_, hx⟩ ⟨_, hy⟩

private lemma mem_U {a} : a ∈ U ↔ ∃ s : partial_wo, s ∈ c ∧ a ∈ s.1 :=
by unfold U; simp [-sigma.exists]

private lemma mem_U2 {a b} (au : a ∈ U) (bu : b ∈ U) :
  ∃ s : partial_wo, s ∈ c ∧ a ∈ s.1 ∧ b ∈ s.1 :=
let ⟨s, sc, as⟩ := mem_U.1 au, ⟨t, tc, bt⟩ := mem_U.1 bu,
    ⟨k, kc, ks, kt⟩ := hc.directed sc tc in
⟨k, kc, sub_of_le ks as, sub_of_le kt bt⟩

private lemma R_ex {s : partial_wo} (sc : s ∈ c)
  {a b : σ} (hb : b ∈ s.1) {au bu} :
  R ⟨a, au⟩ ⟨b, bu⟩ → ∃ ha, s.2.1 ⟨a, ha⟩ ⟨b, hb⟩
| ⟨t, tc, at', bt, h⟩ :=
  match hc.total_of_refl sc tc with
  | or.inr hr := ⟨sub_of_le hr at', (agree_of_le hr _ _ _ _).1 h⟩
  | or.inl hr@⟨f, hf⟩ := begin
      rw [← show (f ⟨b, hb⟩) = ⟨(subtype.mk b bu).val, bt⟩, from
        subtype.eq (hf _)] at h,
      rcases f.init_iff.1 h with ⟨a', e, h'⟩, cases a' with a' ha,
      have : a' = a,
      { have := congr_arg subtype.val e, rwa hf at this },
      subst a', exact ⟨_, h'⟩
    end
  end

private lemma R_iff {s : partial_wo} (sc : s ∈ c)
  {a b : σ} (ha hb) {au bu} :
  R ⟨a, au⟩ ⟨b, bu⟩ ↔ s.2.1 ⟨a, ha⟩ ⟨b, hb⟩ :=
⟨λ h, let ⟨_, h⟩ := R_ex sc hb h in h,
 λ h, ⟨s, sc, ha, hb, h⟩⟩

private def wo : is_well_order U R :=
⟨⟨⟨λ ⟨a, au⟩ ⟨b, bu⟩,
  let ⟨s, sc, ha, hb⟩ := mem_U2 au bu in
  by have := s.2.2; exact
  (@trichotomous _ s.2.1 _ ⟨a, ha⟩ ⟨b, hb⟩).imp
    (R_iff hc sc _ _).2
    (λ o, o.imp (λ h, by congr; injection h)
    (R_iff hc sc _ _).2)⟩,
⟨λ ⟨a, au⟩ h, let ⟨s, sc, ha⟩ := mem_U.1 au in
  by have := s.2.2; exact irrefl _ ((R_iff hc sc _ ha).1 h)⟩,
⟨λ ⟨a, au⟩ ⟨b, bu⟩ ⟨d, du⟩ ab bd,
  let ⟨s, sc, as, bs⟩ := mem_U2 au bu, ⟨t, tc, dt⟩ := mem_U.1 du,
      ⟨k, kc, ks, kt⟩ := hc.directed sc tc in begin
    simp only [R_iff hc kc, sub_of_le ks as, sub_of_le ks bs, sub_of_le kt dt] at ab bd ⊢,
    have := k.2.2, exact trans ab bd
  end⟩⟩,
⟨λ ⟨a, au⟩, let ⟨s, sc, ha⟩ := mem_U.1 au in
  suffices ∀ (a : s.1) au, acc R ⟨a.1, au⟩, from this ⟨a, ha⟩ au,
  λ a, acc.rec_on ((@is_well_order.wf _ _ s.2.2).apply a) $
  λ ⟨a, ha⟩ H IH au, ⟨_, λ ⟨b, hb⟩ h,
    let ⟨hb, h⟩ := R_ex sc ha h in IH ⟨b, hb⟩ h _⟩⟩⟩

theorem chain_ub : ∃ ub, ∀ a ∈ c, a ≤ ub :=
⟨⟨U, R, wo⟩, λ s sc, ⟨⟨⟨⟨
  λ a, ⟨a.1, mem_U.2 ⟨s, sc, a.2⟩⟩,
  λ a b h, by injection h with h; exact subtype.eq h⟩,
  λ a b, by cases a with a ha; cases b with b hb; exact
     (R_iff hc sc _ _).symm⟩,
  λ ⟨a, ha⟩ ⟨b, hb⟩ h,
    let ⟨bs, h'⟩ := R_ex sc ha h in ⟨⟨_, bs⟩, rfl⟩⟩,
  λ a, rfl⟩⟩

end

theorem well_ordering_thm : ∃ r, is_well_order σ r :=
let ⟨m, MM⟩ := zorn.zorn (λ c, chain_ub) (λ a b c, partial_wo.trans) in
suffices hf : ∀ a, a ∈ m.1, from
  let f : σ ≃ m.1 := ⟨λ a, ⟨a, hf a⟩, λ a, a.1, λ a, rfl, λ ⟨a, ha⟩, rfl⟩ in
  ⟨order.preimage f m.2.1,
    @order_embedding.is_well_order _ _ _ _ ↑(order_iso.preimage f m.2.1) m.2.2⟩,
λ a, classical.by_contradiction $ λ ha,
let f : (insert a m.1 : set σ) ≃ (m.1 ⊕ unit) :=
 ⟨λ x, if h : x.1 ∈ m.1 then sum.inl ⟨_, h⟩ else sum.inr ⟨⟩,
  λ x, sum.cases_on x (λ x, ⟨x.1, or.inr x.2⟩) (λ _, ⟨a, or.inl rfl⟩),
  λ x, match x with
    | ⟨_, or.inl rfl⟩ := by dsimp; rw [dif_neg ha]
    | ⟨x, or.inr h⟩ := by dsimp; rw [dif_pos h]
    end,
  λ x, by rcases x with ⟨x, h⟩ | ⟨⟨⟩⟩; dsimp;
    [rw [dif_pos h], rw [dif_neg ha]]⟩ in
let r' := sum.lex m.2.1 (@empty_relation unit) in
have r'wo : is_well_order _ r' :=
  @sum.lex.is_well_order _ _ _ _ m.2.2 empty_relation.is_well_order,
let m' : partial_wo := ⟨insert a m.1, order.preimage f r',
  @order_embedding.is_well_order _ _ _ _ ↑(order_iso.preimage f r') r'wo⟩ in
let g : m.2.1 ≼i r' := ⟨⟨⟨sum.inl, λ a b, sum.inl.inj⟩,
  λ a b, by simp [r']⟩,
  λ a b h, begin
    rcases b with b | ⟨⟨⟩⟩; simp [r'] at h ⊢,
    { cases b, exact ⟨_, _, rfl⟩ },
    { contradiction }
  end⟩ in
ha (sub_of_le (MM m' ⟨g.trans
  (initial_seg.of_iso (order_iso.preimage f r').symm),
  λ x, rfl⟩) (or.inl rfl))

end well_ordering_thm

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

def type (r : α → α → Prop) [wo : is_well_order α r] : ordinal :=
⟦⟨α, r, wo⟩⟧

def typein (r : α → α → Prop) [wo : is_well_order α r] (a : α) : ordinal :=
type (subrel r {b | r b a})

theorem type_def (r : α → α → Prop) [wo : is_well_order α r] :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

@[simp] theorem type_def' (r : α → α → Prop) [is_well_order α r] {wo} :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r = type s ↔ nonempty (r ≃o s) := quotient.eq

@[elab_as_eliminator] theorem induction_on {C : ordinal → Prop}
  (o : ordinal) (H : ∀ α r [is_well_order α r], C (type r)) : C o :=
quot.induction_on o $ λ ⟨α, r, wo⟩, @H α r wo

protected def le (a b : ordinal) : Prop :=
quotient.lift_on₂ a b Well_order.le $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
propext ⟨
  λ ⟨h⟩, ⟨(initial_seg.of_iso f.symm).trans $
    h.trans (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨(initial_seg.of_iso f).trans $
    h.trans (initial_seg.of_iso g.symm)⟩⟩

instance : has_le ordinal := ⟨ordinal.le⟩

theorem type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r ≤ type s ↔ nonempty (r ≼i s) := iff.rfl

def lt (a b : ordinal) : Prop :=
quotient.lift_on₂ a b Well_order.lt $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
by exact propext ⟨
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f.symm $
    h.lt_le (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f $
    h.lt_le (initial_seg.of_iso g.symm)⟩⟩
    
instance : has_lt ordinal := ⟨ordinal.lt⟩

@[simp] theorem type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r < type s ↔ nonempty (r ≺i s) := iff.rfl

instance : partial_order ordinal :=
{ le := (≤),
  lt := (<),
  le_refl := quot.ind $ by exact λ ⟨α, r, wo⟩, ⟨initial_seg.refl _⟩,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩, by exact
      ⟨λ ⟨f⟩, ⟨⟨f⟩, λ ⟨g⟩, (f.lt_le g).irrefl _⟩,
      λ ⟨⟨f⟩, h⟩, sum.rec_on f.lt_or_eq (λ g, ⟨g⟩)
       (λ g, (h ⟨initial_seg.of_iso g.symm⟩).elim)⟩,
  le_antisymm := λ x b, show x ≤ b → b ≤ x → x = b, from
    quotient.induction_on₂ x b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩,
    by exact quot.sound ⟨initial_seg.antisymm h₁ h₂⟩ }

theorem typein_lt_type (r : α → α → Prop) [is_well_order α r]
  (a : α) : typein r a < type r :=
⟨principal_seg.of_element _ _⟩

@[simp] theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : s ≺i r) :
  typein r f.top = type s :=
eq.symm $ quot.sound ⟨order_iso.of_surjective
  (order_embedding.cod_restrict _ f f.lt_top)
  (λ ⟨a, h⟩, by rcases f.down'.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩)⟩

@[simp] theorem typein_lt_typein (r : α → α → Prop) [is_well_order α r]
  {a b : α} : typein r a < typein r b ↔ r a b :=
⟨λ ⟨f⟩, begin
  have : f.top.1 = a,
  { let f' := principal_seg.of_element r a,
    let g' := f.trans (principal_seg.of_element r b),
    have : g'.top = f'.top, {rw subsingleton.elim f' g'},
    simpa [f', g'] },
  rw ← this, exact f.top.2
end, λ h, ⟨principal_seg.cod_restrict _
  (principal_seg.of_element r a)
  (λ x, @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : ∃ a, typein r a = o :=
induction_on o (λ β s _ ⟨f⟩, ⟨f.top, by simp⟩) h

theorem typein_inj (r : α → α → Prop) [is_well_order α r]
  {a b} : typein r a = typein r b ↔ a = b :=
⟨λ h, ((@trichotomous _ r _ a b)
  .resolve_left (λ hn, ne_of_lt ((typein_lt_typein r).2 hn) h))
  .resolve_right (λ hn, ne_of_gt ((typein_lt_typein r).2 hn) h),
congr_arg _⟩

def enum (r : α → α → Prop) [is_well_order α r] (o) : o < type r → α :=
quot.rec_on o (λ ⟨β, s, _⟩ h, (classical.choice h).top) $
λ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩,
begin
  refine funext (λ (H₂ : type t < type r), _),
  have H₁ : type s < type r, {rwa type_eq.2 ⟨h⟩},
  have : ∀ {o e} (H : o < type r), @@eq.rec
   (λ (o : ordinal), o < type r → α)
   (λ (h : type s < type r), (classical.choice h).top)
     e H = (classical.choice H₁).top, {intros, subst e},
  exact (this H₂).trans (principal_seg.top_eq h
    (classical.choice H₁) (classical.choice H₂))
end

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : s ≺i r)
  {h : type s < type r} : enum r (type s) h = f.top :=
principal_seg.top_eq (order_iso.refl _) _ _

@[simp] theorem enum_typein (r : α → α → Prop) [is_well_order α r] (a : α)
  {h : typein r a < type r} : enum r (typein r a) h = a :=
by simp [typein, enum_type (principal_seg.of_element r a)]

@[simp] theorem typein_enum (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : typein r (enum r o h) = o :=
let ⟨a, e⟩ := typein_surj r h in
by clear _let_match; subst e; simp

theorem enum_lt {α β} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_well_order α r] [is_well_order β s] [is_well_order γ t]
  (h₁ : type s < type r) (h₂ : type t < type r) :
  r (enum r (type s) h₁) (enum r (type t) h₂) ↔ type s < type t :=
by rw [← typein_lt_typein r, typein_enum, typein_enum]

theorem wf : @well_founded ordinal (<) :=
⟨λ a, induction_on a $ λ α r wo, by exact
suffices ∀ a, acc (<) (typein r a), from
⟨_, λ o h, let ⟨a, e⟩ := typein_surj r h in e ▸ this a⟩,
λ a, acc.rec_on (wo.wf.apply a) $ λ x H IH, ⟨_, λ o h, begin
  rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩,
  exact IH _ ((typein_lt_typein r).1 h)
end⟩⟩

def card (o : ordinal) : cardinal :=
quot.lift_on o (λ ⟨α, r, _⟩, ⟦α⟧) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, quotient.sound ⟨e.to_equiv⟩

end ordinal
