/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.group.defs
import data.equiv.set
import data.fun_like
import logic.embedding
import order.rel_classes

/-!
# Relation homomorphisms, embeddings, isomorphisms

This file defines relation homomorphisms, embeddings, isomorphisms and order embeddings and
isomorphisms.

## Main declarations

* `rel_hom`: Relation homomorphism. A `rel_hom r s` is a function `f : α → β` such that
  `r a b → s (f a) (f b)`.
* `rel_embedding`: Relation embedding. A `rel_embedding r s` is an embedding `f : α ↪ β` such that
  `r a b ↔ s (f a) (f b)`.
* `rel_iso`: Relation isomorphism. A `rel_iso r s` is an equivalence `f : α ≃ β` such that
  `r a b ↔ s (f a) (f b)`.
* `sum_lex_congr`, `prod_lex_congr`: Creates a relation homomorphism between two `sum_lex` or two
  `prod_lex` from relation homomorphisms between their arguments.

## Notation

* `→r`: `rel_hom`
* `↪r`: `rel_embedding`
* `≃r`: `rel_iso`
-/

open function

universes u v w
variables {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
@[nolint has_inhabited_instance]
structure rel_hom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) :=
(to_fun : α → β)
(map_rel' : ∀ {a b}, r a b → s (to_fun a) (to_fun b))

infix ` →r `:25 := rel_hom

/-- `rel_hom_class F r s` asserts that `F` is a type of functions such that all `f : F`
satisfy `r a b → s (f a) (f b)`.

The relations `r` and `s` are `out_param`s since figuring them out from a goal is a higher-order
matching problem that Lean usually can't do unaided.
-/
class rel_hom_class (F : Type*) {α β : out_param $ Type*}
  (r : out_param $ α → α → Prop) (s : out_param $ β → β → Prop)
  extends fun_like F α (λ _, β) :=
(map_rel : ∀ (f : F) {a b}, r a b → s (f a) (f b))
export rel_hom_class (map_rel)

-- The free parameters `r` and `s` are `out_param`s so this is not dangerous.
attribute [nolint dangerous_instance] rel_hom_class.to_fun_like

namespace rel_hom_class

variables {F : Type*}

lemma map_inf [semilattice_inf α] [linear_order β]
  [rel_hom_class F ((<) : β → β → Prop) ((<) : α → α → Prop)]
  (a : F) (m n : β) : a (m ⊓ n) = a m ⊓ a n :=
(strict_mono.monotone $ λ x y, map_rel a).map_inf m n

lemma map_sup [semilattice_sup α] [linear_order β]
  [rel_hom_class F ((>) : β → β → Prop) ((>) : α → α → Prop)]
  (a : F) (m n : β) : a (m ⊔ n) = a m ⊔ a n :=
@map_inf (order_dual α) (order_dual β) _ _ _ _ _ _ _

protected theorem is_irrefl [rel_hom_class F r s] (f : F) : ∀ [is_irrefl β s], is_irrefl α r
| ⟨H⟩ := ⟨λ a h, H _ (map_rel f h)⟩

protected theorem is_asymm [rel_hom_class F r s] (f : F) : ∀ [is_asymm β s], is_asymm α r
| ⟨H⟩ := ⟨λ a b h₁ h₂, H _ _ (map_rel f h₁) (map_rel f h₂)⟩

protected theorem acc [rel_hom_class F r s] (f : F) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (map_rel f h) _ rfl⟩
end

protected theorem well_founded [rel_hom_class F r s] (f : F) :
  ∀ (h : well_founded s), well_founded r
| ⟨H⟩ := ⟨λ a, rel_hom_class.acc f _ (H _)⟩

end rel_hom_class

namespace rel_hom

instance : rel_hom_class (r →r s) r s :=
{ coe := λ o, o.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_rel := map_rel' }

/-- Auxiliary instance if `rel_hom_class.to_fun_like.to_has_coe_to_fun` isn't found -/
instance : has_coe_to_fun (r →r s) (λ _, α → β) := ⟨λ o, o.to_fun⟩

initialize_simps_projections rel_hom (to_fun → apply)

protected theorem map_rel (f : r →r s) : ∀ {a b}, r a b → s (f a) (f b) := f.map_rel'

@[simp] theorem coe_fn_mk (f : α → β) (o) :
  (@rel_hom.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_fun (f : r →r s) : (f.to_fun : α → β) = f := rfl

/-- The map `coe_fn : (r →r s) → (α → β)` is injective. -/
theorem coe_fn_injective : @function.injective (r →r s) (α → β) coe_fn :=
fun_like.coe_injective

@[ext] theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

theorem ext_iff {f g : r →r s} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

/-- Identity map is a relation homomorphism. -/
@[refl, simps] protected def id (r : α → α → Prop) : r →r r :=
⟨λ x, x, λ a b x, x⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[trans, simps] protected def comp (g : s →r t) (f : r →r s) : r →r t :=
⟨λ x, g (f x), λ a b h, g.2 (f.2 h)⟩

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
protected def swap (f : r →r s) : swap r →r swap s :=
⟨f, λ a b, f.map_rel⟩

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s := ⟨f, λ a b, id⟩

end rel_hom

/-- An increasing function is injective -/
lemma injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀ {x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

/-- An increasing function is injective -/
lemma rel_hom.injective_of_increasing [is_trichotomous α r]
  [is_irrefl β s] (f : r →r s) : injective f :=
injective_of_increasing r s f (λ x y, f.map_rel)

-- TODO: define a `rel_iff_class` so we don't have to do all the `convert` trickery?
theorem surjective.well_founded_iff {f : α → β} (hf : surjective f)
  (o : ∀ {a b}, r a b ↔ s (f a) (f b)) : well_founded r ↔ well_founded s :=
iff.intro (begin
  refine rel_hom_class.well_founded (rel_hom.mk _ _ : s →r r),
  { exact classical.some hf.has_right_inverse },
  intros a b h, apply o.2, convert h,
  iterate 2 { apply classical.some_spec hf.has_right_inverse },
end) (rel_hom_class.well_founded (⟨f, λ _ _, o.1⟩ : r →r s))

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
structure rel_embedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β :=
(map_rel_iff' : ∀ {a b}, s (to_embedding a) (to_embedding b) ↔ r a b)

infix ` ↪r `:25 := rel_embedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
definition subtype.rel_embedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
  ((subtype.val : subtype p → X) ⁻¹'o r) ↪r r :=
⟨embedding.subtype p, λ x y, iff.rfl⟩

theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop}
  (hs : equivalence s) : equivalence (f ⁻¹'o s) :=
⟨λ a, hs.1 _, λ a b h, hs.2.1 h, λ a b c h₁ h₂, hs.2.2 h₁ h₂⟩

namespace rel_embedding

/-- A relation embedding is also a relation homomorphism -/
def to_rel_hom (f : r ↪r s) : (r →r s) :=
{ to_fun := f.to_embedding.to_fun,
  map_rel' := λ x y, (map_rel_iff' f).mpr }

instance : has_coe (r ↪r s) (r →r s) := ⟨to_rel_hom⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ↪r s) (λ _, α → β) := ⟨λ o, o.to_embedding⟩

-- TODO: define and instantiate a `rel_embedding_class` when `embedding_like` is defined
instance : rel_hom_class (r ↪r s) r s :=
{ coe := coe_fn,
  coe_injective' := λ f g h, by { rcases f with ⟨⟨⟩⟩, rcases g with ⟨⟨⟩⟩, congr' },
  map_rel := λ f a b, iff.mpr (map_rel_iff' f) }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
because it is a composition of multiple projections. -/
def simps.apply (h : r ↪r s) : α → β := h

initialize_simps_projections rel_embedding (to_embedding_to_fun → apply, -to_embedding)

@[simp] lemma to_rel_hom_eq_coe (f : r ↪r s) : f.to_rel_hom = f := rfl

@[simp] lemma coe_coe_fn (f : r ↪r s) : ((f : r →r s) : α → β) = f := rfl

theorem injective (f : r ↪r s) : injective f := f.inj'

theorem map_rel_iff (f : r ↪r s) : ∀ {a b}, s (f a) (f b) ↔ r a b := f.map_rel_iff'

@[simp] theorem coe_fn_mk (f : α ↪ β) (o) :
  (@rel_embedding.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_embedding (f : r ↪r s) : (f.to_embedding : α → β) = f := rfl

/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. -/
theorem coe_fn_injective : @function.injective (r ↪r s) (α → β) coe_fn := fun_like.coe_injective

@[ext] theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

theorem ext_iff {f g : r ↪r s} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

/-- Identity map is a relation embedding. -/
@[refl, simps] protected def refl (r : α → α → Prop) : r ↪r r :=
⟨embedding.refl _, λ a b, iff.rfl⟩

/-- Composition of two relation embeddings is a relation embedding. -/
@[trans] protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
⟨f.1.trans g.1, λ a b, by simp [f.map_rel_iff, g.map_rel_iff]⟩

instance (r : α → α → Prop) : inhabited (r ↪r r) := ⟨rel_embedding.refl _⟩

theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) := rfl

@[simp] theorem coe_trans (f : r ↪r s) (g : s ↪r t) : ⇑(f.trans g) = g ∘ f := rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
⟨f.to_embedding, λ a b, f.map_rel_iff⟩

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s := ⟨f, λ a b, iff.rfl⟩

theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s :=
by { ext a b, exact f.map_rel_iff.symm }

protected theorem is_irrefl (f : r ↪r s) [is_irrefl β s] : is_irrefl α r :=
⟨λ a, mt f.map_rel_iff.2 (irrefl (f a))⟩

protected theorem is_refl (f : r ↪r s) [is_refl β s] : is_refl α r :=
⟨λ a, f.map_rel_iff.1 $ refl _⟩

protected theorem is_symm (f : r ↪r s) [is_symm β s] : is_symm α r :=
⟨λ a b, imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

protected theorem is_asymm (f : r ↪r s) [is_asymm β s] : is_asymm α r :=
⟨λ a b h₁ h₂, asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

protected theorem is_antisymm : ∀ (f : r ↪r s) [is_antisymm β s], is_antisymm α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b h₁ h₂, f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩

protected theorem is_trans : ∀ (f : r ↪r s) [is_trans β s], is_trans α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b c h₁ h₂, o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩

protected theorem is_total : ∀ (f : r ↪r s) [is_total β s], is_total α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o o).1 (H _ _)⟩

protected theorem is_preorder : ∀ (f : r ↪r s) [is_preorder β s], is_preorder α r
| f H := by exactI {..f.is_refl, ..f.is_trans}

protected theorem is_partial_order : ∀ (f : r ↪r s) [is_partial_order β s], is_partial_order α r
| f H := by exactI {..f.is_preorder, ..f.is_antisymm}

protected theorem is_linear_order : ∀ (f : r ↪r s) [is_linear_order β s], is_linear_order α r
| f H := by exactI {..f.is_partial_order, ..f.is_total}

protected theorem is_strict_order : ∀ (f : r ↪r s) [is_strict_order β s], is_strict_order α r
| f H := by exactI {..f.is_irrefl, ..f.is_trans}

protected theorem is_trichotomous : ∀ (f : r ↪r s) [is_trichotomous β s], is_trichotomous α r
| ⟨f, o⟩ ⟨H⟩ := ⟨λ a b, (or_congr o (or_congr f.inj'.eq_iff o)).1 (H _ _)⟩

protected theorem is_strict_total_order' :
  ∀ (f : r ↪r s) [is_strict_total_order' β s], is_strict_total_order' α r
| f H := by exactI {..f.is_trichotomous, ..f.is_strict_order}

protected theorem acc (f : r ↪r s) (a : α) : acc s (f a) → acc r a :=
begin
  generalize h : f a = b, intro ac,
  induction ac with _ H IH generalizing a, subst h,
  exact ⟨_, λ a' h, IH (f a') (f.map_rel_iff.2 h) _ rfl⟩
end

protected theorem well_founded : ∀ (f : r ↪r s) (h : well_founded s), well_founded r
| f ⟨H⟩ := ⟨λ a, f.acc _ (H _)⟩

protected theorem is_well_order : ∀ (f : r ↪r s) [is_well_order β s], is_well_order α r
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order'}

/--
To define an relation embedding from an antisymmetric relation `r` to a reflexive relation `s` it
suffices to give a function together with a proof that it satisfies `s (f a) (f b) ↔ r a b`.
-/
def of_map_rel_iff (f : α → β) [is_antisymm α r] [is_refl β s]
  (hf : ∀ a b, s (f a) (f b) ↔ r a b) : r ↪r s :=
{ to_fun := f,
  inj' := λ x y h, antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _)),
  map_rel_iff' := hf }

@[simp]
lemma of_map_rel_iff_coe (f : α → β) [is_antisymm α r] [is_refl β s]
  (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
  ⇑(of_map_rel_iff f hf : r ↪r s) = f :=
rfl

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
def of_monotone [is_trichotomous α r] [is_asymm β s] (f : α → β)
  (H : ∀ a b, r a b → s (f a) (f b)) : r ↪r s :=
begin
  haveI := @is_asymm.is_irrefl β s _,
  refine ⟨⟨f, λ a b e, _⟩, λ a b, ⟨λ h, _, H _ _⟩⟩,
  { refine ((@trichotomous _ r _ a b).resolve_left _).resolve_right _;
    exact λ h, @irrefl _ s _ _ (by simpa [e] using H _ _ h) },
  { refine (@trichotomous _ r _ a b).resolve_right (or.rec (λ e, _) (λ h', _)),
    { subst e, exact irrefl _ h },
    { exact asymm (H _ _ h') h } }
end

@[simp] theorem of_monotone_coe [is_trichotomous α r] [is_asymm β s] (f : α → β) (H) :
  (@of_monotone _ _ r s _ _ f H : α → β) = f := rfl

end rel_embedding

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
structure rel_iso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β :=
(map_rel_iff' : ∀ {a b}, s (to_equiv a) (to_equiv b) ↔ r a b)

infix ` ≃r `:25 := rel_iso

namespace rel_iso

/-- Convert an `rel_iso` to an `rel_embedding`. This function is also available as a coercion
but often it is easier to write `f.to_rel_embedding` than to write explicitly `r` and `s`
in the target type. -/
def to_rel_embedding (f : r ≃r s) : r ↪r s :=
⟨f.to_equiv.to_embedding, f.map_rel_iff'⟩

theorem to_equiv_injective : injective (to_equiv : (r ≃r s) → α ≃ β)
| ⟨e₁, o₁⟩ ⟨e₂, o₂⟩ h := by { congr, exact h }

instance : has_coe (r ≃r s) (r ↪r s) := ⟨to_rel_embedding⟩
-- see Note [function coercion]
instance : has_coe_to_fun (r ≃r s) (λ _, α → β) := ⟨λ f, f⟩

-- TODO: define and instantiate a `rel_iso_class` when `equiv_like` is defined
instance : rel_hom_class (r ≃r s) r s :=
{ coe := coe_fn,
  coe_injective' := equiv.coe_fn_injective.comp to_equiv_injective,
  map_rel := λ f a b, iff.mpr (map_rel_iff' f) }

@[simp] lemma to_rel_embedding_eq_coe (f : r ≃r s) : f.to_rel_embedding = f := rfl

@[simp] lemma coe_coe_fn (f : r ≃r s) : ((f : r ↪r s) : α → β) = f := rfl

theorem map_rel_iff (f : r ≃r s) : ∀ {a b}, s (f a) (f b) ↔ r a b := f.map_rel_iff'

@[simp] theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, s (f a) (f b) ↔ r a b) :
  (rel_iso.mk f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_equiv (f : r ≃r s) : (f.to_equiv : α → β) = f := rfl

/-- The map `coe_fn : (r ≃r s) → (α → β)` is injective. Lean fails to parse
`function.injective (λ e : r ≃r s, (e : α → β))`, so we use a trick to say the same. -/
theorem coe_fn_injective : @function.injective (r ≃r s) (α → β) coe_fn := fun_like.coe_injective

@[ext] theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

theorem ext_iff {f g : r ≃r s} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
@[symm] protected def symm (f : r ≃r s) : s ≃r r :=
⟨f.to_equiv.symm, λ a b, by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (h : r ≃r s) : α → β := h
/-- See Note [custom simps projection]. -/
def simps.symm_apply (h : r ≃r s) : β → α := h.symm

initialize_simps_projections rel_iso
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply, -to_equiv)

/-- Identity map is a relation isomorphism. -/
@[refl, simps apply] protected def refl (r : α → α → Prop) : r ≃r r :=
⟨equiv.refl _, λ a b, iff.rfl⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[trans, simps apply] protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
⟨f₁.to_equiv.trans f₂.to_equiv, λ a b, f₂.map_rel_iff.trans f₁.map_rel_iff⟩

instance (r : α → α → Prop) : inhabited (r ≃r r) := ⟨rel_iso.refl _⟩

@[simp] lemma default_def (r : α → α → Prop) : default (r ≃r r) = rel_iso.refl r := rfl

/-- a relation isomorphism is also a relation isomorphism between dual relations. -/
protected def swap (f : r ≃r s) : (swap r) ≃r (swap s) :=
⟨f.to_equiv, λ _ _, f.map_rel_iff⟩

@[simp] theorem coe_fn_symm_mk (f o) : ((@rel_iso.mk _ _ r s f o).symm : β → α) = f.symm :=
rfl

@[simp] theorem apply_symm_apply (e : r ≃r s) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] theorem symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y :=
by rw [← e.map_rel_iff, e.apply_symm_apply]

theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) :=
by rw [← e.map_rel_iff, e.apply_symm_apply]

protected lemma bijective (e : r ≃r s) : bijective e := e.to_equiv.bijective
protected lemma injective (e : r ≃r s) : injective e := e.to_equiv.injective
protected lemma surjective (e : r ≃r s) : surjective e := e.to_equiv.surjective

@[simp] lemma range_eq (e : r ≃r s) : set.range e = set.univ := e.surjective.range_eq

@[simp] lemma eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
f.injective.eq_iff

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s := ⟨f, λ a b, iff.rfl⟩

/-- A surjective relation embedding is a relation isomorphism. -/
@[simps apply]
noncomputable def of_surjective (f : r ↪r s) (H : surjective f) : r ≃r s :=
⟨equiv.of_bijective f ⟨f.injective, H⟩, λ a b, f.map_rel_iff⟩

/--
Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
def sum_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @rel_iso α₁ β₁ r₁ s₁) (e₂ : @rel_iso α₂ β₂ r₂ s₂) :
  sum.lex r₁ r₂ ≃r sum.lex s₁ s₂ :=
⟨equiv.sum_congr e₁.to_equiv e₂.to_equiv, λ a b,
 by cases e₁ with f hf; cases e₂ with g hg;
    cases a; cases b; simp [hf, hg]⟩

/--
Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
def prod_lex_congr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂}
  (e₁ : @rel_iso α₁ β₁ r₁ s₁) (e₂ : @rel_iso α₂ β₂ r₂ s₂) :
  prod.lex r₁ r₂ ≃r prod.lex s₁ s₂ :=
⟨equiv.prod_congr e₁.to_equiv e₂.to_equiv,
  λ a b, by simp [prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff]⟩

instance : group (r ≃r r) :=
{ one := rel_iso.refl r,
  mul := λ f₁ f₂, f₂.trans f₁,
  inv := rel_iso.symm,
  mul_assoc := λ f₁ f₂ f₃, rfl,
  one_mul := λ f, ext $ λ _, rfl,
  mul_one := λ f, ext $ λ _, rfl,
  mul_left_inv := λ f, ext f.symm_apply_apply }

@[simp] lemma coe_one : ⇑(1 : r ≃r r) = id := rfl

@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl

lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp] lemma inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x := e.symm_apply_apply x

@[simp] lemma apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x := e.apply_symm_apply x

end rel_iso

/-- `subrel r p` is the inherited relation on a subset. -/
def subrel (r : α → α → Prop) (p : set α) : p → p → Prop :=
(coe : p → α) ⁻¹'o r

@[simp] theorem subrel_val (r : α → α → Prop) (p : set α)
  {a b} : subrel r p a b ↔ r a.1 b.1 := iff.rfl

namespace subrel

/-- The relation embedding from the inherited relation on a subset. -/
protected def rel_embedding (r : α → α → Prop) (p : set α) :
  subrel r p ↪r r := ⟨embedding.subtype _, λ a b, iff.rfl⟩

@[simp] theorem rel_embedding_apply (r : α → α → Prop) (p a) :
  subrel.rel_embedding r p a = a.1 := rfl

instance (r : α → α → Prop) [is_well_order α r]
  (p : set α) : is_well_order p (subrel r p) :=
rel_embedding.is_well_order (subrel.rel_embedding r p)

end subrel

/-- Restrict the codomain of a relation embedding. -/
def rel_embedding.cod_restrict (p : set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r subrel s p :=
⟨f.to_embedding.cod_restrict p H, f.map_rel_iff'⟩

@[simp] theorem rel_embedding.cod_restrict_apply (p) (f : r ↪r s) (H a) :
  rel_embedding.cod_restrict p f H a = ⟨f a, H a⟩ := rfl
