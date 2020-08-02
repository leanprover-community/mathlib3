/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.embedding
import order.rel_classes

open function

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-- An increasing function is injective -/
lemma injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

/-- An order embedding with respect to a given pair of orders `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure order_embedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β :=
(ord' : ∀ {a b}, r a b ↔ s (to_embedding a) (to_embedding b))

infix ` ≼o `:25 := order_embedding

/-- the induced order on a subtype is an embedding under the natural inclusion. -/
definition subtype.order_embedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
((subtype.val : subtype p → X) ⁻¹'o r) ≼o r :=
⟨⟨subtype.val,subtype.val_injective⟩,by intros;refl⟩

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop}
  (hs : equivalence s) : equivalence (f ⁻¹'o s) :=
⟨λ a, hs.1 _, λ a b h, hs.2.1 h, λ a b c h₁ h₂, hs.2.2 h₁ h₂⟩

namespace order_embedding

instance : has_coe_to_fun (r ≼o s) := ⟨λ _, α → β, λ o, o.to_embedding⟩

theorem injective (f : r ≼o s) : injective f := f.inj'

theorem ord (f : r ≼o s) : ∀ {a b}, r a b ↔ s (f a) (f b) := f.ord'

@[simp] theorem coe_fn_mk (f : α ↪ β) (o) :
  (@order_embedding.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_embedding (f : r ≼o s) : (f.to_embedding : α → β) = f := rfl

/-- The map `coe_fn : (r ≼o s) → (r → s)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_inj : ∀ ⦃e₁ e₂ : r ≼o s⦄, (e₁ : α → β) = e₂ → e₁ = e₂
| ⟨⟨f₁, h₁⟩, o₁⟩ ⟨⟨f₂, h₂⟩, o₂⟩ h := by { congr, exact h }

@[refl] protected def refl (r : α → α → Prop) : r ≼o r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

@[trans] protected def trans (f : r ≼o s) (g : s ≼o t) : r ≼o t :=
⟨f.1.trans g.1, λ a b, by rw [f.2, g.2]; simp⟩

@[simp] theorem refl_apply (x : α) : order_embedding.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≼o s) (g : s ≼o t) (a : α) : (f.trans g) a = g (f a) := rfl

/-- An order embedding is also an order embedding between dual orders. -/
def rsymm (f : r ≼o s) : swap r ≼o swap s :=
⟨f.to_embedding, λ a b, f.ord⟩

/-- If `f` is injective, then it is an order embedding from the
  preimage order of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ≼o s := ⟨f, λ a b, iff.rfl⟩

theorem eq_preimage (f : r ≼o s) : r = f ⁻¹'o s :=
by { ext a b, exact f.ord }

protected theorem is_irrefl : ∀ (f : r ≼o s) [is_irrefl β s], is_irrefl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a h, H _ (o.1 h)⟩

protected theorem is_refl : ∀ (f : r ≼o s) [is_refl β s], is_refl α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a, o.2 (H _)⟩

protected theorem is_symm : ∀ (f : r ≼o s) [is_symm β s], is_symm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h, o.2 (H _ _ (o.1 h))⟩

protected theorem is_asymm : ∀ (f : r ≼o s) [is_asymm β s], is_asymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (o.1 h₁) (o.1 h₂)⟩

protected theorem is_antisymm : ∀ (f : r ≼o s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_trans : ∀ (f : r ≼o s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.2 (H _ _ _ (o.1 h₁) (o.1 h₂))⟩

protected theorem is_total : ∀ (f : r ≼o s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).2 (H _ _)⟩

protected theorem is_preorder : ∀ (f : r ≼o s) [is_preorder β s], is_preorder α r
| f H := by exactI {..f.is_refl, ..f.is_trans}

protected theorem is_partial_order : ∀ (f : r ≼o s) [is_partial_order β s], is_partial_order α r
| f H := by exactI {..f.is_preorder, ..f.is_antisymm}

protected theorem is_linear_order : ∀ (f : r ≼o s) [is_linear_order β s], is_linear_order α r
| f H := by exactI {..f.is_partial_order, ..f.is_total}

protected theorem is_strict_order : ∀ (f : r ≼o s) [is_strict_order β s], is_strict_order α r
| f H := by exactI {..f.is_irrefl, ..f.is_trans}

protected theorem is_trichotomous : ∀ (f : r ≼o s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff.symm o)).2 (H _ _)⟩

protected theorem is_strict_total_order' : ∀ (f : r ≼o s) [is_strict_total_order' β s], is_strict_total_order' α r
| f H := by exactI {..f.is_trichotomous, ..f.is_strict_order}

protected theorem acc (f : r ≼o s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.ord.1 h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r ≼o s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected theorem is_well_order : ∀ (f : r ≼o s) [is_well_order β s], is_well_order α r
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order'}

/-- It suffices to prove `f` is monotone between strict orders
  to show it is an order embedding. -/
def of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) : r ≼o s :=
begin
  haveI := @is_asymm.is_irrefl β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨H _ _, λ h, _⟩⟩,
  { refine ((@trichotomous _ r _ a b).resolve_left _).resolve_right _;
    exact λ h, @irrefl _ s _ _ (by simpa [e] using H _ _ h) },
  { refine (@trichotomous _ r _ a b).resolve_right (or.rec (λ e, _) (λ h', _)),
    { subst e, exact irrefl _ h },
    { exact asymm (H _ _ h') h } }
end

@[simp] theorem of_monotone_coe [is_trichotomous α r] [is_asymm β s] (f : α → β) (H) :
  (@of_monotone _ _ r s _ _ f H : α → β) = f := rfl

-- If le is preserved by an order embedding of preorders, then lt is too
def lt_embedding_of_le_embedding [preorder α] [preorder β]
  (f : ((≤) : α → α → Prop) ≼o ((≤) : β → β → Prop)) :
(has_lt.lt : α → α → Prop) ≼o (has_lt.lt : β → β → Prop) :=
{ ord' := by intros; simp [lt_iff_le_not_le,f.ord], .. f }

end order_embedding

/-- The inclusion map `fin n → ℕ` is an order embedding. -/
def fin.val.order_embedding (n) : @order_embedding (fin n) ℕ (<) (<) :=
⟨⟨fin.val, @fin.eq_of_veq _⟩, λ a b, iff.rfl⟩

/-- The inclusion map `fin m → fin n` is an order embedding. -/
def fin_fin.order_embedding {m n} (h : m ≤ n) : @order_embedding (fin m) (fin n) (<) (<) :=
⟨⟨λ ⟨x, h'⟩, ⟨x, lt_of_lt_of_le h' h⟩,
  λ ⟨a, _⟩ ⟨b, _⟩ h, by congr; injection h⟩,
  by intros; cases a; cases b; refl⟩

instance fin.lt.is_well_order (n) : is_well_order (fin n) (<) :=
(fin.val.order_embedding _).is_well_order

/-- An order isomorphism is an equivalence that is also an order embedding. -/
structure order_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(ord' : ∀ {a b}, r a b ↔ s (to_equiv a) (to_equiv b))

infix ` ≃o `:25 := order_iso

namespace order_iso

/-- Convert an `order_iso` to an `order_embedding`. This function is also available as a coercion
but often it is easier to write `f.to_order_embedding` than to write explicitly `r` and `s`
in the target type. -/
def to_order_embedding (f : r ≃o s) : r ≼o s :=
⟨f.to_equiv.to_embedding, f.ord'⟩

instance : has_coe (r ≃o s) (r ≼o s) := ⟨to_order_embedding⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ≃o s) := ⟨λ _, α → β, λ f, f⟩

@[simp] lemma to_order_embedding_eq_coe (f : r ≃o s) : f.to_order_embedding = f := rfl

@[simp] lemma coe_coe_fn (f : r ≃o s) : ((f : r ≼o s) : α → β) = f := rfl

theorem ord (f : r ≃o s) : ∀ {a b}, r a b ↔ s (f a) (f b) := f.ord'

lemma ord'' {r : α → α → Prop} {s : β → β → Prop} (f : r ≃o s) {x y : α} :
    r x y ↔ s ((↑f : r ≼o s) x) ((↑f : r ≼o s) y) := f.ord

@[simp] theorem coe_fn_mk (f : α ≃ β) (o) :
  (@order_iso.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃o s) : (f.to_equiv : α → β) = f := rfl

theorem to_equiv_injective : injective (to_equiv : (r ≃o s) → α ≃ β)
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by { congr, exact h }

/-- The map `coe_fn : (r ≃o s) → (r → s)` is injective. We can't use `function.injective`
here but mimic its signature by using `⦃e₁ e₂⦄`. -/
theorem coe_fn_injective ⦃e₁ e₂ : r ≃o s⦄ (h : (e₁ : α → β) = e₂) : e₁ = e₂ :=
to_equiv_injective $ equiv.coe_fn_injective h

@[ext] theorem ext {e₁ e₂ : r ≃o s} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
coe_fn_injective $ funext h

/-- Identity map is an order isomorphism. -/
@[refl] protected def refl (r : α → α → Prop) : r ≃o r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

/-- Inverse map of an order isomorphism is an order isomorphism. -/
@[symm] protected def symm (f : r ≃o s) : s ≃o r :=
⟨f.to_equiv.symm, λ a b, by cases f with f o; rw o; simp⟩

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans] protected def trans (f₁ : r ≃o s) (f₂ : s ≃o t) : r ≃o t :=
⟨f₁.to_equiv.trans f₂.to_equiv, λ a b, f₁.ord.trans f₂.ord⟩

/-- An order isomorphism is also an order isomorphism between dual orders. -/
def rsymm (f : r ≃o s) : (swap r) ≃o (swap s) :=
⟨f.to_equiv, λ _ _, f.ord⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@order_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem refl_apply (x : α) : order_iso.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≃o s) (g : s ≃o t) (a : α) : (f.trans g) a = g (f a) :=
rfl

@[simp] theorem apply_symm_apply  (e : r ≃o s) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] theorem symm_apply_apply (e : r ≃o s) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

theorem rel_symm_apply (e : r ≃o s) {x y} : r x (e.symm y) ↔ s (e x) y :=
by rw [e.ord, e.apply_symm_apply]

theorem symm_apply_rel (e : r ≃o s) {x y} : r (e.symm x) y ↔ s x (e y) :=
by rw [e.ord, e.apply_symm_apply]

protected lemma bijective (e : r ≃o s) : bijective e := e.to_equiv.bijective
protected lemma injective (e : r ≃o s) : injective e := e.to_equiv.injective
protected lemma surjective (e : r ≃o s) : surjective e := e.to_equiv.surjective

/-- Any equivalence lifts to an order isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃o s := ⟨f, λ a b, iff.rfl⟩

/-- A surjective order embedding is an order isomorphism. -/
noncomputable def of_surjective (f : r ≼o s) (H : surjective f) : r ≃o s :=
⟨equiv.of_bijective f ⟨f.injective, H⟩, by simp [f.ord']⟩

@[simp] theorem of_surjective_coe (f : r ≼o s) (H) : (of_surjective f H : α → β) = f :=
rfl

def sum_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @order_iso α₁ α₂ r₁ r₂) (e₂ : @order_iso β₁ β₂ s₁ s₂) :
  sum.lex r₁ s₁ ≃o sum.lex r₂ s₂ :=
⟨equiv.sum_congr e₁.to_equiv e₂.to_equiv, λ a b,
 by cases e₁ with f hf; cases e₂ with g hg;
    cases a; cases b; simp [hf, hg]⟩

def prod_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @order_iso α₁ α₂ r₁ r₂) (e₂ : @order_iso β₁ β₂ s₁ s₂) :
  prod.lex r₁ s₁ ≃o prod.lex r₂ s₂ :=
⟨equiv.prod_congr e₁.to_equiv e₂.to_equiv,  λ a b, begin
  cases e₁ with f hf; cases e₂ with g hg,
  cases a with a₁ a₂; cases b with b₁ b₂,
  suffices : prod.lex r₁ s₁ (a₁, a₂) (b₁, b₂) ↔
    prod.lex r₂ s₂ (f a₁, g a₂) (f b₁, g b₂), {simpa [hf, hg]},
  split,
  { intro h, cases h with _ _ _ _ h _ _ _ h,
    { left, exact hf.1 h },
    { right, exact hg.1 h } },
  { generalize e : f b₁ = fb₁,
    intro h, cases h with _ _ _ _ h _ _ _ h,
    { subst e, left, exact hf.2 h },
    { have := f.injective e, subst b₁,
      right, exact hg.2 h } }
end⟩

instance : group (r ≃o r) :=
{ one := order_iso.refl r,
  mul := λ f₁ f₂, f₂.trans f₁,
  inv := order_iso.symm,
  mul_assoc := λ f₁ f₂ f₃, rfl,
  one_mul := λ f, ext $ λ _, rfl,
  mul_one := λ f, ext $ λ _, rfl,
  mul_left_inv := λ f, ext f.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : r ≃o r) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : r ≃o r) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : r ≃o r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : r ≃o r) (x) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : r ≃o r) (x) : e (e⁻¹ x) = x := e.apply_symm_apply x

end order_iso

/-- A subset `p : set α` embeds into `α` -/
def set_coe_embedding {α : Type*} (p : set α) : p ↪ α := ⟨subtype.val, @subtype.eq _ _⟩

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
@subtype.val _ p ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

protected def order_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ≼o r := ⟨set_coe_embedding _, λ a b, iff.rfl⟩

@[simp] theorem order_embedding_apply (r : α → α → Prop) (p a) :
  subrel.order_embedding r p a = a.1 := rfl

instance (r : α → α → Prop) [is_well_order α r]
  (p : set α) : is_well_order p (subrel r p) :=
order_embedding.is_well_order (subrel.order_embedding r p)

end subrel

/-- Restrict the codomain of an order embedding -/
def order_embedding.cod_restrict (p : set β) (f : r ≼o s) (H : ∀ a, f a ∈ p) : r ≼o subrel s p :=
⟨f.to_embedding.cod_restrict p H, f.ord'⟩

@[simp] theorem order_embedding.cod_restrict_apply (p) (f : r ≼o s) (H a) :
  order_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl

section lattice_isos

lemma order_iso.map_bot [order_bot α] [order_bot β]
  (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop)) :
  f ⊥ = ⊥ :=
by { rw [eq_bot_iff, ← f.apply_symm_apply ⊥, ← f.ord], apply bot_le, }

lemma order_iso.map_top [order_top α] [order_top β]
  (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop)) :
  f ⊤ = ⊤ :=
by { rw [eq_top_iff, ← f.apply_symm_apply ⊤, ← f.ord], apply le_top, }

variables {a₁ a₂ : α}

lemma order_embedding.map_inf_le [semilattice_inf α] [semilattice_inf β]
  (f : ((≤) : α → α → Prop) ≼o ((≤) : β → β → Prop)) :
  f (a₁ ⊓ a₂) ≤ f a₁ ⊓ f a₂ :=
by simp [← f.ord]

lemma order_iso.map_inf [semilattice_inf α] [semilattice_inf β]
  (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop)) :
  f (a₁ ⊓ a₂) = f a₁ ⊓ f a₂ :=
begin
  apply le_antisymm, { apply f.to_order_embedding.map_inf_le },
  rw [f.symm.ord, order_iso.symm_apply_apply],
  convert f.symm.to_order_embedding.map_inf_le; simp,
end

lemma order_embedding.le_map_sup [semilattice_sup α] [semilattice_sup β]
  (f : ((≤) : α → α → Prop) ≼o ((≤) : β → β → Prop)) :
  f a₁ ⊔ f a₂ ≤ f (a₁ ⊔ a₂) :=
by simp [← f.ord]


lemma order_iso.map_sup [semilattice_sup α] [semilattice_sup β]
  (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop)) :
  f (a₁ ⊔ a₂) = f a₁ ⊔ f a₂ :=
begin
  apply le_antisymm, swap, { apply f.to_order_embedding.le_map_sup },
  rw [f.symm.ord, order_iso.symm_apply_apply],
  convert f.symm.to_order_embedding.le_map_sup; simp,
end

end lattice_isos
