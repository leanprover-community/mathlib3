/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fun_like.basic
import logic.embedding.basic
import order.rel_classes

/-!
# Relation homomorphisms, embeddings, isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
variables {α β γ δ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} {u : δ → δ → Prop}

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
@[nolint has_nonempty_instance]
structure rel_hom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) :=
(to_fun : α → β)
(map_rel' : ∀ {a b}, r a b → s (to_fun a) (to_fun b))

infix ` →r `:25 := rel_hom

section
set_option old_structure_cmd true

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

end

namespace rel_hom_class

variables {F : Type*}

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

protected theorem map_rel (f : r →r s) {a b} : r a b → s (f a) (f b) := f.map_rel'

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

@[simp] theorem inj (f : r ↪r s) {a b} : f a = f b ↔ a = b := f.injective.eq_iff

theorem map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b := f.map_rel_iff'

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

protected theorem is_strict_total_order :
  ∀ (f : r ↪r s) [is_strict_total_order β s], is_strict_total_order α r
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
| f H := by exactI {wf := f.well_founded H.wf, ..f.is_strict_total_order}

/-- `quotient.out` as a relation embedding between the lift of a relation and the relation. -/
@[simps] noncomputable def _root_.quotient.out_rel_embedding [s : setoid α] {r : α → α → Prop} (H) :
  quotient.lift₂ r H ↪r r :=
⟨embedding.quotient_out α, begin
  refine λ x y, quotient.induction_on₂ x y (λ a b, _),
  apply iff_iff_eq.2 (H _ _ _ _ _ _);
  apply quotient.mk_out
end⟩

/-- A relation is well founded iff its lift to a quotient is. -/
@[simp] theorem _root_.well_founded_lift₂_iff [s : setoid α] {r : α → α → Prop} {H} :
  well_founded (quotient.lift₂ r H) ↔ well_founded r :=
⟨λ hr, begin
  suffices : ∀ {x : quotient s} {a : α}, ⟦a⟧ = x → acc r a,
  { exact ⟨λ a, this rfl⟩ },
  { refine λ x, hr.induction x _,
    rintros x IH a rfl,
    exact ⟨_, λ b hb, IH ⟦b⟧ hb rfl⟩ }
end, (quotient.out_rel_embedding H).well_founded⟩

alias _root_.well_founded_lift₂_iff ↔
  _root_.well_founded.of_quotient_lift₂ _root_.well_founded.quotient_lift₂

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

/-- A relation embedding from an empty type. -/
def of_is_empty (r : α → α → Prop) (s : β → β → Prop) [is_empty α] : r ↪r s :=
⟨embedding.of_is_empty, is_empty_elim⟩

/-- `sum.inl` as a relation embedding into `sum.lift_rel r s`. -/
@[simps] def sum_lift_rel_inl (r : α → α → Prop) (s : β → β → Prop) : r ↪r sum.lift_rel r s :=
{ to_fun := sum.inl,
  inj' := sum.inl_injective,
  map_rel_iff' := λ a b, sum.lift_rel_inl_inl }

/-- `sum.inr` as a relation embedding into `sum.lift_rel r s`. -/
@[simps] def sum_lift_rel_inr (r : α → α → Prop) (s : β → β → Prop) : s ↪r sum.lift_rel r s :=
{ to_fun := sum.inr,
  inj' := sum.inr_injective,
  map_rel_iff' := λ a b, sum.lift_rel_inr_inr }

/-- `sum.map` as a relation embedding between `sum.lift_rel` relations. -/
@[simps] def sum_lift_rel_map (f : r ↪r s) (g : t ↪r u) : sum.lift_rel r t ↪r sum.lift_rel s u :=
{ to_fun := sum.map f g,
  inj' := f.injective.sum_map g.injective,
  map_rel_iff' := by { rintro (a | b) (c | d); simp [f.map_rel_iff, g.map_rel_iff] } }

/-- `sum.inl` as a relation embedding into `sum.lex r s`. -/
@[simps] def sum_lex_inl (r : α → α → Prop) (s : β → β → Prop) : r ↪r sum.lex r s :=
{ to_fun := sum.inl,
  inj' := sum.inl_injective,
  map_rel_iff' := λ a b, sum.lex_inl_inl }

/-- `sum.inr` as a relation embedding into `sum.lex r s`. -/
@[simps] def sum_lex_inr (r : α → α → Prop) (s : β → β → Prop) : s ↪r sum.lex r s :=
{ to_fun := sum.inr,
  inj' := sum.inr_injective,
  map_rel_iff' := λ a b, sum.lex_inr_inr }

/-- `sum.map` as a relation embedding between `sum.lex` relations. -/
@[simps] def sum_lex_map (f : r ↪r s) (g : t ↪r u) : sum.lex r t ↪r sum.lex s u :=
{ to_fun := sum.map f g,
  inj' := f.injective.sum_map g.injective,
  map_rel_iff' := by { rintro (a | b) (c | d); simp [f.map_rel_iff, g.map_rel_iff] } }

/-- `λ b, prod.mk a b` as a relation embedding. -/
@[simps] def prod_lex_mk_left (s : β → β → Prop) {a : α} (h : ¬ r a a) : s ↪r prod.lex r s :=
{ to_fun := prod.mk a,
  inj' := prod.mk.inj_left a,
  map_rel_iff' := λ b₁ b₂, by simp [prod.lex_def, h] }

/-- `λ a, prod.mk a b` as a relation embedding. -/
@[simps] def prod_lex_mk_right (r : α → α → Prop) {b : β} (h : ¬ s b b) : r ↪r prod.lex r s :=
{ to_fun := λ a, (a, b),
  inj' := prod.mk.inj_right b,
  map_rel_iff' := λ a₁ a₂, by simp [prod.lex_def, h] }

/-- `prod.map` as a relation embedding. -/
@[simps] def prod_lex_map (f : r ↪r s) (g : t ↪r u) : prod.lex r t ↪r prod.lex s u :=
{ to_fun := prod.map f g,
  inj' := f.injective.prod_map g.injective,
  map_rel_iff' := λ a b, by simp [prod.lex_def, f.map_rel_iff, g.map_rel_iff] }

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
⟨f.to_equiv.to_embedding, λ _ _, f.map_rel_iff'⟩

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

theorem map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b := f.map_rel_iff'

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

@[simp] lemma default_def (r : α → α → Prop) : default = rel_iso.refl r := rfl

/-- A relation isomorphism between equal relations on equal types. -/
@[simps to_equiv apply] protected def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  (h₁ : α = β) (h₂ : r == s) : r ≃r s :=
⟨equiv.cast h₁, λ a b, by { subst h₁, rw eq_of_heq h₂, refl }⟩

@[simp] protected theorem cast_symm {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  (h₁ : α = β) (h₂ : r == s) : (rel_iso.cast h₁ h₂).symm = rel_iso.cast h₁.symm h₂.symm := rfl

@[simp] protected theorem cast_refl {α : Type u} {r : α → α → Prop}
  (h₁ : α = α := rfl) (h₂ : r == r := heq.rfl) : rel_iso.cast h₁ h₂ = rel_iso.refl r := rfl

@[simp] protected theorem cast_trans {α β γ : Type u}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (h₁ : α = β) (h₁' : β = γ)
  (h₂ : r == s) (h₂' : s == t): (rel_iso.cast h₁ h₂).trans (rel_iso.cast h₁' h₂') =
  rel_iso.cast (h₁.trans h₁') (h₂.trans h₂') :=
ext $ λ x, by { subst h₁, refl }

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

@[simp] lemma eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
f.injective.eq_iff

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s := ⟨f, λ a b, iff.rfl⟩

instance is_well_order.preimage {α : Type u} (r : α → α → Prop) [is_well_order α r] (f : β ≃ α) :
  is_well_order β (f ⁻¹'o r) :=
@rel_embedding.is_well_order _ _ (f ⁻¹'o r) r (rel_iso.preimage f r) _

instance is_well_order.ulift {α : Type u} (r : α → α → Prop) [is_well_order α r] :
  is_well_order (ulift α) (ulift.down ⁻¹'o r) :=
is_well_order.preimage r equiv.ulift

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

/-- Two relations on empty types are isomorphic. -/
def rel_iso_of_is_empty (r : α → α → Prop) (s : β → β → Prop) [is_empty α] [is_empty β] : r ≃r s :=
⟨equiv.equiv_of_is_empty α β, is_empty_elim⟩

/-- Two irreflexive relations on a unique type are isomorphic. -/
def rel_iso_of_unique_of_irrefl (r : α → α → Prop) (s : β → β → Prop)
  [is_irrefl α r] [is_irrefl β s] [unique α] [unique β] : r ≃r s :=
⟨equiv.equiv_of_unique α β,
  λ x y, by simp [not_rel_of_subsingleton r, not_rel_of_subsingleton s]⟩

/-- Two reflexive relations on a unique type are isomorphic. -/
def rel_iso_of_unique_of_refl (r : α → α → Prop) (s : β → β → Prop)
  [is_refl α r] [is_refl β s] [unique α] [unique β] : r ≃r s :=
⟨equiv.equiv_of_unique α β,
  λ x y, by simp [rel_of_subsingleton r, rel_of_subsingleton s]⟩

end rel_iso
