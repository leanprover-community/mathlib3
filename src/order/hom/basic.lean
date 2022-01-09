/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import order.rel_iso
import tactic.monotonicity.basic

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
 * `order_hom α β` a.k.a. `α →o β`: Preorder homomorphism.
    An `order_hom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
 * `order_embedding α β` a.k.a. `α ↪o β`: Relation embedding.
    An `order_embedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_embedding α β (≤) (≤)`.
* `order_iso`: Relation isomorphism.
    An `order_iso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_iso α β (≤) (≤)`.

We also define many `order_hom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `order_hom.compₘ` and `order_hom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `order_hom.id`: identity map as `α →o α`;
* `order_hom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `order_hom.comp`: composition of two bundled monotone maps;
* `order_hom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `order_hom.const`: constant function as a bundled monotone map;
* `order_hom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `order_hom.prodₘ`: a more bundled version of `order_hom.prod`;
* `order_hom.prod_iso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `order_hom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `order_hom.on_diag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `order_hom.fst`: projection `prod.fst : α × β → α` as a bundled monotone map;
* `order_hom.snd`: projection `prod.snd : α × β → β` as a bundled monotone map;
* `order_hom.prod_map`: `prod.map f g` as a bundled monotone map;
* `pi.eval_order_hom`: evaluation of a function at a point `function.eval i` as a bundled
  monotone map;
* `order_hom.coe_fn_hom`: coercion to function as a bundled monotone map;
* `order_hom.apply`: application of a `order_hom` at a point as a bundled monotone map;
* `order_hom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `order_hom.pi_iso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `order_hom.subtyle.val`: embedding `subtype.val : subtype p → α` as a bundled monotone map;
* `order_hom.dual`: reinterpret a monotone map `α →o β` as a monotone map
  `order_dual α →o order_dual β`;
* `order_hom.dual_iso`: order isomorphism between `α →o β` and
  `order_dual (order_dual α →o order_dual β)`;

We also define two functions to convert other bundled maps to `α →o β`:

* `order_embedding.to_order_hom`: convert `α ↪o β` to `α →o β`;
* `rel_hom.to_order_hom`: conver a `rel_hom` between strict orders to a `order_hom`.

## Tags

monotone map, bundled morphism
-/

/-- Bundled monotone (aka, increasing) function -/
structure order_hom (α β : Type*) [preorder α] [preorder β] :=
(to_fun   : α → β)
(monotone' : monotone to_fun)

infixr ` →o `:25 := order_hom

/-- `order_hom_class F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
abbreviation order_hom_class (F : Type*) (α β : out_param Type*) [preorder α] [preorder β] :=
rel_hom_class F ((≤) : α → α → Prop) ((≤) : β → β → Prop).

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
abbreviation order_embedding (α β : Type*) [has_le α] [has_le β] :=
@rel_embedding α β (≤) (≤)

infix ` ↪o `:25 := order_embedding

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_iso (≤) (≤)`. -/
abbreviation order_iso (α β : Type*) [has_le α] [has_le β] := @rel_iso α β (≤) (≤)

infix ` ≃o `:25 := order_iso

variables {α β γ δ : Type*}

namespace order_hom_class

variables {F : Type*} [preorder α] [preorder β] [order_hom_class F α β]

protected lemma monotone (f : F) : monotone (f : α → β) := λ _ _, map_rel f
protected lemma mono (f : F) : monotone (f : α → β) := λ _ _, map_rel f

end order_hom_class

namespace order_hom
variables [preorder α] [preorder β] [preorder γ] [preorder δ]

instance : has_coe_to_fun (α →o β) (λ _, α → β) := ⟨order_hom.to_fun⟩

initialize_simps_projections order_hom (to_fun → coe)

protected lemma monotone (f : α →o β) : monotone f := f.monotone'
protected lemma mono (f : α →o β) : monotone f := f.monotone

instance : order_hom_class (α →o β) α β :=
{ coe := to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_rel := λ f, f.monotone }

@[simp] lemma to_fun_eq_coe {f : α →o β} : f.to_fun = f := rfl
@[simp] lemma coe_fun_mk {f : α → β} (hf : _root_.monotone f) : (mk f hf : α → β) = f := rfl

@[ext] -- See library note [partially-applied ext lemmas]
lemma ext (f g : α →o β) (h : (f : α → β) = g) : f = g := fun_like.coe_injective h

/-- One can lift an unbundled monotone function to a bundled one. -/
instance : can_lift (α → β) (α →o β) :=
{ coe := coe_fn,
  cond := monotone,
  prf := λ f h, ⟨⟨f, h⟩, rfl⟩ }

/-- The identity function as bundled monotone function. -/
@[simps {fully_applied := ff}]
def id : α →o α := ⟨id, monotone_id⟩

instance : inhabited (α →o α) := ⟨id⟩

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : preorder (α →o β) :=
@preorder.lift (α →o β) (α → β) _ coe_fn

instance {β : Type*} [partial_order β] : partial_order (α →o β) :=
@partial_order.lift (α →o β) (α → β) _ coe_fn ext

lemma le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x := iff.rfl

@[simp, norm_cast] lemma coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl

@[simp] lemma mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g := iff.rfl

@[mono] lemma apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) :
  f x ≤ g y :=
(h₁ x).trans $ g.mono h₂

/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
def curry : (α × β →o γ) ≃o (α →o β →o γ) :=
{ to_fun := λ f, ⟨λ x, ⟨function.curry f x, λ y₁ y₂ h, f.mono ⟨le_rfl, h⟩⟩,
    λ x₁ x₂ h y, f.mono ⟨h, le_rfl⟩⟩,
  inv_fun := λ f, ⟨function.uncurry (λ x, f x), λ x y h, (f.mono h.1 x.2).trans $ (f y.1).mono h.2⟩,
  left_inv := λ f, by { ext ⟨x, y⟩, refl },
  right_inv := λ f, by { ext x y, refl },
  map_rel_iff' := λ f g, by simp [le_def] }

@[simp] lemma curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) := rfl

@[simp] lemma curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 := rfl

/-- The composition of two bundled monotone functions. -/
@[simps {fully_applied := ff}]
def comp (g : β →o γ) (f : α →o β) : α →o γ := ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono] lemma comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
  g₁.comp f₁ ≤ g₂.comp f₂ :=
λ x, (hg _).trans (g₂.mono $ hf _)

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps {fully_applied := ff}]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
curry ⟨λ f : (β →o γ) × (α →o β), f.1.comp f.2, λ f₁ f₂ h, comp_mono h.1 h.2⟩

@[simp] lemma comp_id (f : α →o β) : comp f id = f :=
by { ext, refl }

@[simp] lemma id_comp (f : α →o β) : comp id f = f :=
by { ext, refl }

/-- Constant function bundled as a `order_hom`. -/
@[simps {fully_applied := ff}]
def const (α : Type*) [preorder α] {β : Type*} [preorder β] : β →o α →o β :=
{ to_fun := λ b, ⟨function.const α b, λ _ _ _, le_rfl⟩,
  monotone' := λ b₁ b₂ h x, h }

@[simp] lemma const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c := rfl

@[simp] lemma comp_const (γ : Type*) [preorder γ] (f : α →o β) (c : α) :
  f.comp (const γ c) = const γ (f c) := rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. -/
@[simps] protected def prod (f : α →o β) (g : α →o γ) : α →o (β × γ) :=
⟨λ x, (f x, g x), λ x y h, ⟨f.mono h, g.mono h⟩⟩

@[mono] lemma prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
  f₁.prod g₁ ≤ f₂.prod g₂ :=
λ x, prod.le_def.2 ⟨hf _, hg _⟩

lemma comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
  (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. This is a fully bundled version. -/
@[simps] def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
curry ⟨λ f : (α →o β) × (α →o γ), f.1.prod f.2, λ f₁ f₂ h, prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as a `order_hom`. -/
@[simps] def diag : α →o α × α := id.prod id

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps {simp_rhs := tt}] def on_diag (f : α →o α →o β) : α →o β := (curry.symm f).comp diag

/-- `prod.fst` as a `order_hom`. -/
@[simps] def fst : α × β →o α := ⟨prod.fst, λ x y h, h.1⟩

/-- `prod.snd` as a `order_hom`. -/
@[simps] def snd : α × β →o β := ⟨prod.snd, λ x y h, h.2⟩

@[simp] lemma fst_prod_snd : (fst : α × β →o α).prod snd = id :=
by { ext ⟨x, y⟩ : 2, refl }

@[simp] lemma fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.prod g) = f := ext _ _ rfl

@[simp] lemma snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.prod g) = g := ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps] def prod_iso : (α →o β × γ) ≃o (α →o β) × (α →o γ) :=
{ to_fun := λ f, (fst.comp f, snd.comp f),
  inv_fun := λ f, f.1.prod f.2,
  left_inv := λ f, by ext; refl,
  right_inv := λ f, by ext; refl,
  map_rel_iff' := λ f g, forall_and_distrib.symm }

/-- `prod.map` of two `order_hom`s as a `order_hom`. -/
@[simps] def prod_map (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
⟨prod.map f g, λ x y h, ⟨f.mono h.1, g.mono h.2⟩⟩

variables {ι : Type*} {π : ι → Type*} [Π i, preorder (π i)]

/-- Evaluation of an unbundled function at a point (`function.eval`) as a `order_hom`. -/
@[simps {fully_applied := ff}]
def _root_.pi.eval_order_hom (i : ι) : (Π j, π j) →o π i :=
⟨function.eval i, function.monotone_eval i⟩

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps {fully_applied := ff}] def coe_fn_hom : (α →o β) →o (α → β) :=
{ to_fun := λ f, f,
  monotone' := λ x y h, h }

/-- Function application `λ f, f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `pi.eval_order_hom`.  -/
@[simps {fully_applied := ff}] def apply (x : α) : (α →o β) →o β :=
(pi.eval_order_hom x).comp coe_fn_hom

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps] def pi (f : Π i, α →o π i) : α →o (Π i, π i) :=
⟨λ x i, f i x, λ x y h i, (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps] def pi_iso : (α →o Π i, π i) ≃o Π i, α →o π i :=
{ to_fun := λ f i, (pi.eval_order_hom i).comp f,
  inv_fun := pi,
  left_inv := λ f, by { ext x i, refl },
  right_inv := λ f, by { ext x i, refl },
  map_rel_iff' := λ f g, forall_swap }

/-- `subtype.val` as a bundled monotone function.  -/
@[simps {fully_applied := ff}]
def subtype.val (p : α → Prop) : subtype p →o α :=
⟨subtype.val, λ x y h, h⟩

-- TODO[gh-6025]: make this a global instance once safe to do so
/-- There is a unique monotone map from a subsingleton to itself. -/
local attribute [instance]
def unique [subsingleton α] : unique (α →o α) :=
{ default := order_hom.id, uniq := λ a, ext _ _ (subsingleton.elim _ _) }

lemma order_hom_eq_id [subsingleton α] (g : α →o α) : g = order_hom.id :=
subsingleton.elim _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps] protected def dual : (α →o β) ≃ (order_dual α →o order_dual β) :=
{ to_fun := λ f, ⟨order_dual.to_dual ∘ f ∘ order_dual.of_dual, f.mono.dual⟩,
  inv_fun := λ f, ⟨order_dual.of_dual ∘ f ∘ order_dual.to_dual, f.mono.dual⟩,
  left_inv := λ f, ext _ _ rfl,
  right_inv := λ f, ext _ _ rfl }

/-- `order_hom.dual` as an order isomorphism. -/
def dual_iso (α β : Type*) [preorder α] [preorder β] :
  (α →o β) ≃o order_dual (order_dual α →o order_dual β) :=
{ to_equiv := order_hom.dual.trans order_dual.to_dual,
  map_rel_iff' := λ f g, iff.rfl }

end order_hom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
def rel_embedding.order_embedding_of_lt_embedding [partial_order α] [partial_order β]
  (f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)) :
  α ↪o β :=
{ map_rel_iff' := by { intros, simp [le_iff_lt_or_eq,f.map_rel_iff, f.injective.eq_iff] }, .. f }

@[simp]
lemma rel_embedding.order_embedding_of_lt_embedding_apply [partial_order α] [partial_order β]
  {f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)} {x : α} :
  rel_embedding.order_embedding_of_lt_embedding f x = f x := rfl

namespace order_embedding

variables [preorder α] [preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
def lt_embedding : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop) :=
{ map_rel_iff' := by intros; simp [lt_iff_le_not_le, f.map_rel_iff], .. f }

@[simp] lemma lt_embedding_apply (x : α) : f.lt_embedding x = f x := rfl

@[simp] theorem le_iff_le {a b} : (f a) ≤ (f b) ↔ a ≤ b := f.map_rel_iff

@[simp] theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
f.lt_embedding.map_rel_iff

@[simp] lemma eq_iff_eq {a b} : f a = f b ↔ a = b := f.injective.eq_iff

protected theorem monotone : monotone f := order_hom_class.monotone f

protected theorem strict_mono : strict_mono f := λ x y, f.lt_iff_lt.2

protected theorem acc (a : α) : acc (<) (f a) → acc (<) a :=
f.lt_embedding.acc a

protected theorem well_founded :
  well_founded ((<) : β → β → Prop) → well_founded ((<) : α → α → Prop) :=
f.lt_embedding.well_founded

protected theorem is_well_order [is_well_order β (<)] : is_well_order α (<) :=
f.lt_embedding.is_well_order

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : order_dual α ↪o order_dual β :=
⟨f.to_embedding, λ a b, f.map_rel_iff⟩

/--
To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def of_map_le_iff {α β} [partial_order α] [preorder β] (f : α → β)
  (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) : α ↪o β :=
rel_embedding.of_map_rel_iff f hf

@[simp] lemma coe_of_map_le_iff {α β} [partial_order α] [preorder β] {f : α → β} (h) :
  ⇑(of_map_le_iff f h) = f := rfl

/-- A strictly monotone map from a linear order is an order embedding. --/
def of_strict_mono {α β} [linear_order α] [preorder β] (f : α → β)
  (h : strict_mono f) : α ↪o β :=
of_map_le_iff f (λ _ _, h.le_iff_le)

@[simp] lemma coe_of_strict_mono {α β} [linear_order α] [preorder β] {f : α → β}
  (h : strict_mono f) : ⇑(of_strict_mono f h) = f := rfl

/-- Embedding of a subtype into the ambient type as an `order_embedding`. -/
@[simps {fully_applied := ff}] def subtype (p : α → Prop) : subtype p ↪o α :=
⟨function.embedding.subtype p, λ x y, iff.rfl⟩

/-- Convert an `order_embedding` to a `order_hom`. -/
@[simps {fully_applied := ff}]
def to_order_hom {X Y : Type*} [preorder X] [preorder Y] (f : X ↪o Y) : X →o Y :=
{ to_fun := f,
  monotone' := f.monotone }

end order_embedding
section rel_hom

variables [partial_order α] [preorder β]

namespace rel_hom

variables (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps {fully_applied := ff}]
def to_order_hom : α →o β :=
{ to_fun    := f,
  monotone' := strict_mono.monotone (λ x y, f.map_rel), }

end rel_hom

lemma rel_embedding.to_order_hom_injective (f : ((<) : α → α → Prop) ↪r ((<) : β → β → Prop)) :
  function.injective (f : ((<) : α → α → Prop) →r ((<) : β → β → Prop)).to_order_hom :=
λ _ _ h, f.injective h

end rel_hom

namespace order_iso

section has_le

variables [has_le α] [has_le β] [has_le γ]

/-- Reinterpret an order isomorphism as an order embedding. -/
def to_order_embedding (e : α ≃o β) : α ↪o β :=
e.to_rel_embedding

@[simp] lemma coe_to_order_embedding (e : α ≃o β) :
  ⇑(e.to_order_embedding) = e := rfl

protected lemma bijective (e : α ≃o β) : function.bijective e := e.to_equiv.bijective
protected lemma injective (e : α ≃o β) : function.injective e := e.to_equiv.injective
protected lemma surjective (e : α ≃o β) : function.surjective e := e.to_equiv.surjective

@[simp] lemma range_eq (e : α ≃o β) : set.range e = set.univ := e.surjective.range_eq

@[simp] lemma apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
e.to_equiv.apply_eq_iff_eq

/-- Identity order isomorphism. -/
def refl (α : Type*) [has_le α] : α ≃o α := rel_iso.refl (≤)

@[simp] lemma coe_refl : ⇑(refl α) = id := rfl

lemma refl_apply (x : α) : refl α x = x := rfl

@[simp] lemma refl_to_equiv : (refl α).to_equiv = equiv.refl α := rfl

/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α := e.symm

@[simp] lemma apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
e.to_equiv.apply_symm_apply x

@[simp] lemma symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

@[simp] lemma symm_refl (α : Type*) [has_le α] : (refl α).symm = refl α := rfl

lemma apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
e.to_equiv.symm_apply_eq

@[simp] lemma symm_symm (e : α ≃o β) : e.symm.symm = e := by { ext, refl }

lemma symm_injective : function.injective (symm : (α ≃o β) → (β ≃o α)) :=
λ e e' h, by rw [← e.symm_symm, h, e'.symm_symm]

@[simp] lemma to_equiv_symm (e : α ≃o β) : e.to_equiv.symm = e.symm.to_equiv := rfl

@[simp] lemma symm_image_image (e : α ≃o β) (s : set α) : e.symm '' (e '' s) = s :=
e.to_equiv.symm_image_image s

@[simp] lemma image_symm_image (e : α ≃o β) (s : set β) : e '' (e.symm '' s) = s :=
e.to_equiv.image_symm_image s

lemma image_eq_preimage (e : α ≃o β) (s : set α) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s

@[simp] lemma preimage_symm_preimage (e : α ≃o β) (s : set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
e.to_equiv.preimage_symm_preimage s

@[simp] lemma symm_preimage_preimage (e : α ≃o β) (s : set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
e.to_equiv.symm_preimage_preimage s

@[simp] lemma image_preimage (e : α ≃o β) (s : set β) : e '' (e ⁻¹' s) = s :=
e.to_equiv.image_preimage s

@[simp] lemma preimage_image (e : α ≃o β) (s : set α) : e ⁻¹' (e '' s) = s :=
e.to_equiv.preimage_image s

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans] def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ := e.trans e'

@[simp] lemma coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e := rfl

lemma trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) := rfl

@[simp] lemma refl_trans (e : α ≃o β) : (refl α).trans e = e := by { ext x, refl }

@[simp] lemma trans_refl (e : α ≃o β) : e.trans (refl β) = e := by { ext x, refl }

end has_le

open set

section le

variables [has_le α] [has_le β] [has_le γ]

@[simp] lemma le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y := e.map_rel_iff

lemma le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
e.rel_symm_apply

lemma symm_apply_le (e : α ≃o β) {x : α} {y : β} : e.symm y ≤ x ↔ y ≤ e x :=
e.symm_apply_rel

end le

variables [preorder α] [preorder β] [preorder γ]

protected lemma monotone (e : α ≃o β) : monotone e := e.to_order_embedding.monotone

protected lemma strict_mono (e : α ≃o β) : strict_mono e := e.to_order_embedding.strict_mono

@[simp] lemma lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
e.to_order_embedding.lt_iff_lt

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. --/
def of_cmp_eq_cmp {α β} [linear_order α] [linear_order β] (f : α → β) (g : β → α)
  (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
have gf : ∀ (a : α), a = g (f a) := by { intro, rw [←cmp_eq_eq_iff, h, cmp_self_eq_eq] },
{ to_fun := f,
  inv_fun := g,
  left_inv := λ a, (gf a).symm,
  right_inv := by { intro, rw [←cmp_eq_eq_iff, ←h, cmp_self_eq_eq] },
  map_rel_iff' := by { intros, apply le_iff_le_of_cmp_eq_cmp, convert (h _ _).symm, apply gf } }

/-- Order isomorphism between two equal sets. -/
def set_congr (s t : set α) (h : s = t) : s ≃o t :=
{ to_equiv := equiv.set_congr h,
  map_rel_iff' := λ x y, iff.rfl }

/-- Order isomorphism between `univ : set α` and `α`. -/
def set.univ : (set.univ : set α) ≃o α :=
{ to_equiv := equiv.set.univ α,
  map_rel_iff' := λ x y, iff.rfl }

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps to_equiv apply] def fun_unique (α β : Type*) [unique α] [preorder β] :
  (α → β) ≃o β :=
{ to_equiv := equiv.fun_unique α β,
  map_rel_iff' := λ f g, by simp [pi.le_def, unique.forall_iff] }

@[simp] lemma fun_unique_symm_apply {α β : Type*} [unique α] [preorder β] :
  ((fun_unique α β).symm : β → α → β) = function.const α := rfl

end order_iso

namespace equiv

variables [preorder α] [preorder β]

/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
def to_order_iso (e : α ≃ β) (h₁ : monotone e) (h₂ : monotone e.symm) :
  α ≃o β :=
⟨e, λ x y, ⟨λ h, by simpa only [e.symm_apply_apply] using h₂ h, λ h, h₁ h⟩⟩

@[simp] lemma coe_to_order_iso (e : α ≃ β) (h₁ : monotone e) (h₂ : monotone e.symm) :
  ⇑(e.to_order_iso h₁ h₂) = e := rfl

@[simp] lemma to_order_iso_to_equiv (e : α ≃ β) (h₁ : monotone e) (h₂ : monotone e.symm) :
  (e.to_order_iso h₁ h₂).to_equiv = e := rfl

end equiv

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def strict_mono_on.order_iso {α β} [linear_order α] [preorder β]
  (f : α → β) (s : set α) (hf : strict_mono_on f s) :
  s ≃o f '' s :=
{ to_equiv := hf.inj_on.bij_on_image.equiv _,
  map_rel_iff' := λ x y, hf.le_iff_le x.2 y.2 }

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
protected noncomputable def strict_mono.order_iso {α β} [linear_order α] [preorder β] (f : α → β)
  (h_mono : strict_mono f) : α ≃o set.range f :=
{ to_equiv := equiv.of_injective f h_mono.injective,
  map_rel_iff' := λ a b, h_mono.le_iff_le }

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def strict_mono.order_iso_of_surjective {α β} [linear_order α] [preorder β]
  (f : α → β) (h_mono : strict_mono f) (h_surj : function.surjective f) : α ≃o β :=
(h_mono.order_iso f).trans $ (order_iso.set_congr _ _ h_surj.range_eq).trans order_iso.set.univ

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
def strict_mono.order_iso_of_right_inverse {α β} [linear_order α] [preorder β]
  (f : α → β) (h_mono : strict_mono f) (g : β → α) (hg : function.right_inverse g f) : α ≃o β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ x, h_mono.injective $ hg _,
  right_inv := hg,
  .. order_embedding.of_strict_mono f h_mono }

/-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def order_iso.dual [has_le α] [has_le β] (f : α ≃o β) :
  order_dual α ≃o order_dual β := ⟨f.to_equiv, λ _ _, f.map_rel_iff⟩

section lattice_isos

lemma order_iso.map_bot' [has_le α] [partial_order β] (f : α ≃o β) {x : α} {y : β}
  (hx : ∀ x', x ≤ x') (hy : ∀ y', y ≤ y') : f x = y :=
by { refine le_antisymm _ (hy _), rw [← f.apply_symm_apply y, f.map_rel_iff], apply hx }

lemma order_iso.map_bot [has_le α] [partial_order β] [order_bot α] [order_bot β] (f : α ≃o β) :
  f ⊥ = ⊥ :=
f.map_bot' (λ _, bot_le) (λ _, bot_le)

lemma order_iso.map_top' [has_le α] [partial_order β] (f : α ≃o β) {x : α} {y : β}
  (hx : ∀ x', x' ≤ x) (hy : ∀ y', y' ≤ y) : f x = y :=
f.dual.map_bot' hx hy

lemma order_iso.map_top [has_le α] [partial_order β] [order_top α] [order_top β] (f : α ≃o β) :
  f ⊤ = ⊤ :=
f.dual.map_bot

lemma order_embedding.map_inf_le [semilattice_inf α] [semilattice_inf β]
  (f : α ↪o β) (x y : α) :
  f (x ⊓ y) ≤ f x ⊓ f y :=
f.monotone.map_inf_le x y

lemma order_iso.map_inf [semilattice_inf α] [semilattice_inf β]
  (f : α ≃o β) (x y : α) :
  f (x ⊓ y) = f x ⊓ f y :=
begin
  refine (f.to_order_embedding.map_inf_le x y).antisymm _,
  simpa [← f.symm.le_iff_le] using f.symm.to_order_embedding.map_inf_le (f x) (f y)
end

/-- Note that this goal could also be stated `(disjoint on f) a b` -/
lemma disjoint.map_order_iso [semilattice_inf α] [order_bot α] [semilattice_inf β] [order_bot β]
  {a b : α} (f : α ≃o β) (ha : disjoint a b) : disjoint (f a) (f b) :=
begin
  rw [disjoint, ←f.map_inf, ←f.map_bot],
  exact f.monotone ha,
end

@[simp] lemma disjoint_map_order_iso_iff [semilattice_inf α] [order_bot α] [semilattice_inf β]
  [order_bot β] {a b : α} (f : α ≃o β) : disjoint (f a) (f b) ↔ disjoint a b :=
⟨λ h, f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_order_iso f.symm, λ h, h.map_order_iso f⟩

lemma order_embedding.le_map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ↪o β) (x y : α) :
  f x ⊔ f y ≤ f (x ⊔ y) :=
f.monotone.le_map_sup x y

lemma order_iso.map_sup [semilattice_sup α] [semilattice_sup β]
  (f : α ≃o β) (x y : α) :
  f (x ⊔ y) = f x ⊔ f y :=
f.dual.map_inf x y

section bounded_order

variables [lattice α] [lattice β] [bounded_order α] [bounded_order β] (f : α ≃o β)
include f

lemma order_iso.is_compl {x y : α} (h : is_compl x y) : is_compl (f x) (f y) :=
⟨by { rw [← f.map_bot, ← f.map_inf, f.map_rel_iff], exact h.1 },
  by { rw [← f.map_top, ← f.map_sup, f.map_rel_iff], exact h.2 }⟩

theorem order_iso.is_compl_iff {x y : α} :
  is_compl x y ↔ is_compl (f x) (f y) :=
⟨f.is_compl, λ h, begin
  rw [← f.symm_apply_apply x, ← f.symm_apply_apply y],
  exact f.symm.is_compl h,
end⟩

lemma order_iso.is_complemented
  [is_complemented α] : is_complemented β :=
⟨λ x, begin
  obtain ⟨y, hy⟩ := exists_is_compl (f.symm x),
  rw ← f.symm_apply_apply y at hy,
  refine ⟨f y, f.symm.is_compl_iff.2 hy⟩,
end⟩

theorem order_iso.is_complemented_iff :
  is_complemented α ↔ is_complemented β :=
⟨by { introI, exact f.is_complemented }, by { introI, exact f.symm.is_complemented }⟩

end bounded_order
end lattice_isos
