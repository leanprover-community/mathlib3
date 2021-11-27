/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.fun_like
import data.multiset.basic

/-!
# Freiman homomorphisms

In this file, we define Freiman homomorphisms. A `n`-Freiman homomorphism is a function `f : α → β`
such that `f (x₁) * ... * f (xₙ) = f (y₁) * ... * f (yₙ)` for all `x₁, ..., xₙ, y₁, ..., yₙ` such
that `x₁ * ... * xₙ = y₁ * ... * yₙ`. In particular, any `mul_hom` is a Freiman homomorphism.

They are of interest in additive combinatorics.

## Main declaration

* `freiman_hom`: Freiman homomorphism.
* `add_freiman_hom`: Additive Freiman homomorphism.

## Notation

* `α →*[n] β`: Multiplicative `n`-Freiman homomorphism
* `α →+[n] β`: Additive`n`-Freiman homomorphism

## TODO

`monoid_hom.to_freiman_hom` could be relaxed to `mul_hom.to_freiman_hom` by proving
`(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.
-/

open multiset

variables {F α β γ δ G : Type*}

/-- An additive `n`-Freiman homomorphism is a map which preserves sums of `n` elements. -/
structure add_freiman_hom (α β : Type*) [add_comm_monoid α] [add_comm_monoid β] (n : ℕ) :=
(to_fun : α → β)
(map_sum_eq_map_sum' {s t : multiset α} (hs : s.card = n) (ht : t.card = n) (h : s.sum = t.sum) :
  (s.map to_fun).sum = (t.map to_fun).sum)

/-- A `n`-Freiman homomorphism is a map which preserves products of `n` elements. -/
@[to_additive add_freiman_hom]
structure freiman_hom (α β : Type*) [comm_monoid α] [comm_monoid β] (n : ℕ) :=
(to_fun : α → β)
(map_prod_eq_map_prod' {s t : multiset α} (hs : s.card = n) (ht : t.card = n)
  (h : s.prod = t.prod) : (s.map to_fun).prod = (t.map to_fun).prod)

notation α ` →+[`:25 n:25 `] `:0 β:0 := add_freiman_hom α β n
notation α ` →*[`:25 n:25 `] `:0 β:0 := freiman_hom α β n

/-- `add_freiman_hom_class F α β n` states that `F` is a type of `n`-ary sums-preserving morphisms.
You should extend this class when you extend `add_freiman_hom`. -/
class add_freiman_hom_class (F : Type*) (α β : out_param $ Type*) [add_comm_monoid α]
  [add_comm_monoid β] (n : ℕ) extends fun_like F α (λ _, β) :=
(map_sum_eq_map_sum' (f : F) {s t : multiset α} (hs : s.card = n) (ht : t.card = n)
  (h : s.sum = t.sum) : (s.map f).sum = (t.map f).sum)

/-- `freiman_hom_class F α β n` states that `F` is a type of `n`-ary products-preserving morphisms.
You should extend this class when you extend `freiman_hom`. -/
@[to_additive add_freiman_hom_class]
class freiman_hom_class (F : Type*) (α β : out_param $ Type*) [comm_monoid α] [comm_monoid β]
  (n : out_param ℕ)
  extends fun_like F α (λ _, β) :=
(map_prod_eq_map_prod' (f : F) {s t : multiset α} (hs : s.card = n) (ht : t.card = n)
  (h : s.prod = t.prod) : (s.map f).prod = (t.map f).prod)

-- `dangerous_instance` yields a false positive because `n` is an `out_param`.
attribute [nolint dangerous_instance] freiman_hom_class.to_fun_like
attribute [nolint dangerous_instance] add_freiman_hom_class.to_fun_like

section comm_monoid
variables [comm_monoid α] [comm_monoid β] [comm_monoid γ] [comm_monoid δ] [comm_group G] {n : ℕ}

@[to_additive]
lemma map_prod_eq_map_prod [freiman_hom_class F α β n] (f : F) {s t : multiset α} (hs : s.card = n)
  (ht : t.card = n) (h : s.prod = t.prod) :
  (s.map f).prod = (t.map f).prod :=
freiman_hom_class.map_prod_eq_map_prod' f hs ht h

namespace freiman_hom

@[to_additive]
instance freiman_hom_class : freiman_hom_class (α →*[n] β) α β n :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_prod_eq_map_prod' := map_prod_eq_map_prod' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn` directly. -/
@[to_additive]
instance : has_coe_to_fun (α →*[n] β) (λ _, α → β) := ⟨to_fun⟩

@[to_additive]
protected lemma map_prod (f : α →*[n] β) {s t : multiset α} (hs : s.card = n) (ht : t.card = n)
  (h : s.prod = t.prod) :
  (s.map f).prod = (t.map f).prod :=
f.map_prod_eq_map_prod' hs ht h

initialize_simps_projections freiman_hom (to_fun → apply)

@[simp, to_additive]
lemma to_fun_eq_coe (f : α →*[n] β) : f.to_fun = f := rfl

@[ext, to_additive]
lemma ext ⦃f g : α →*[n] β⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[to_additive]
lemma ext_iff {f g : α →*[n] β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp, to_additive]
lemma coe_mk (f : α → β) (h : ∀ s t : multiset α, s.card = n → t.card = n →
  s.prod = t.prod → (s.map f).prod = (t.map f).prod) :
  ⇑(mk f h) = f := rfl

@[simp, to_additive] lemma mk_coe (f : α →*[n] β) (h) : mk f h = f := ext $ λ _, rfl

/-- The identity map from a commutative monoid to itself. -/
@[to_additive "The identity map from an additive commutative monoid to itself.", simps]
protected def id (α : Type*) [comm_monoid α] (n : ℕ) : α →*[n] α  :=
{ to_fun := λ x, x, map_prod_eq_map_prod' := λ s t _ _ h, by rw [map_id', map_id', h] }

/-- Composition of Freiman homomorphisms as a Freiman homomorphism. -/
@[to_additive "Composition of additive Freiman homomorphisms as an additive Freiman homomorphism."]
protected def comp (f : β →*[n] γ) (g : α →*[n] β) : α →*[n] γ :=
{ to_fun := f ∘ g,
  map_prod_eq_map_prod' := λ s t hs ht h, by rw [←map_map,
    f.map_prod ((s.card_map _).trans hs) ((t.card_map _).trans ht) (g.map_prod hs ht h), map_map] }

@[simp, to_additive]
lemma coe_comp (f : β →*[n] γ) (g : α →*[n] β) : ⇑(f.comp g) = f ∘ g := rfl

@[to_additive]
lemma comp_apply (f : β →*[n] γ) (g : α →*[n] β) (x : α) : f.comp g x = f (g x) := rfl

@[to_additive]
lemma comp_assoc (f : α →*[n] β) (g : β →*[n] γ) (h : γ →*[n] δ) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[to_additive]
lemma cancel_right {g₁ g₂ : β →*[n] γ} {f : α →*[n] β} (hf : function.surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, ext $ (forall_iff_forall_surj hf).1 (ext_iff.1 h), λ h, h ▸ rfl⟩

@[to_additive]
lemma cancel_left {g : β →*[n] γ} {f₁ f₂ : α →*[n] β} (hg : function.injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply],
  λ h, h ▸ rfl⟩

@[simp, to_additive] lemma comp_id (f : α →*[n] β) : f.comp (freiman_hom.id α n) = f :=
ext $ λ x, rfl

@[simp, to_additive] lemma id_comp (f : α →*[n] β) : (freiman_hom.id β n).comp f = f :=
ext $ λ x, rfl

/-- `freiman_hom.const b` is the Freiman homomorphism sending everything to `b`. -/
@[to_additive "`add_freiman_hom.const b` is the Freiman homomorphism sending everything to `b`."]
def const (n : ℕ) (b : β) : α →*[n] β :=
{ to_fun := λ _, b,
  map_prod_eq_map_prod' := λ s t hs ht _,
    by rw [multiset.map_const, multiset.map_const, prod_repeat, prod_repeat, hs, ht] }

@[simp, to_additive] lemma const_apply (n : ℕ) (b : β) (x : α) : const n b x = b := rfl

@[simp, to_additive] lemma const_comp (n : ℕ) (b : γ) (f : α →*[n] β) :
  (const n b).comp f = const n b := rfl

/-- `1` is the Freiman homomorphism sending everything to `1`. -/
@[to_additive "`0` is the Freiman homomorphism sending everything to `0`."]
instance : has_one (α →*[n] β) :=
⟨{ to_fun := λ _, 1, map_prod_eq_map_prod' := λ s t _ _ _, by rw [prod_map_one, prod_map_one] }⟩

@[simp, to_additive] lemma one_apply (x : α) : (1 : α →*[n] β) x = 1 := rfl

@[simp, to_additive] lemma one_comp (f : α →*[n] β) : (1 : β →*[n] γ).comp f = 1 := rfl

@[to_additive] instance : inhabited (α →*[n] β) := ⟨1⟩

/-- `f * g` is the Freiman homomorphism  sends `x` to `f x * g x`. -/
@[to_additive "`f + g` is the Freiman homomorphism sending `x` to `f x + g x`."]
instance : has_mul (α →*[n] β) :=
⟨λ f g, { to_fun := λ x, f x * g x,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_mul, prod_map_mul, f.map_prod hs ht h, g.map_prod hs ht h] }⟩

@[simp, to_additive] lemma mul_apply (f g : α →*[n] β) (x : α) : (f * g) x = f x * g x := rfl

@[to_additive] lemma mul_comp (g₁ g₂ : β →*[n] γ) (f : α →*[n] β) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

/-- If `f` is a Freiman homomorphism to a commutative group, then `f⁻¹` is the Freiman homomorphism
sending `x` to `(f x)⁻¹`. -/
@[to_additive]
instance : has_inv (α →*[n] G) :=
⟨λ f, { to_fun := λ x, (f x)⁻¹,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_inv', prod_map_inv', f.map_prod hs ht h] }⟩

@[simp, to_additive] lemma inv_apply (f : α →*[n] G) (x : α) : f⁻¹ x = (f x)⁻¹ := rfl

@[simp, to_additive] lemma inv_comp (f : β →*[n] G) (g : α →*[n] β) : f⁻¹.comp g = (f.comp g)⁻¹ :=
ext $ λ x, rfl

/-- If `f` and `g` are Freiman homomorphisms to a commutative group, then `f / g` is the Freiman
homomorphism sending `x` to `f x / g x`. -/
@[to_additive "If `f` and `g` are additive Freiman homomorphisms to an additive commutative group,
then `f - g` is the additive Freiman homomorphism sending `x` to `f x - g x`"]
instance : has_div (α →*[n] G) :=
⟨λ f g, { to_fun := λ x, f x / g x,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_div, prod_map_div, f.map_prod hs ht h, g.map_prod hs ht h] }⟩

@[simp, to_additive] lemma div_apply (f g : α →*[n] G) (x : α) : (f / g) x = f x / g x := rfl

@[simp, to_additive] lemma div_comp (f₁ f₂ : β →*[n] G) (g : α →*[n] β) :
  (f₁ / f₂).comp g = f₁.comp g / f₂.comp g :=
ext $ λ x, rfl

/-! ### Instances -/

/-- `α →*[n] β` is a `comm_monoid`. -/
@[to_additive "`α →+[n] β` is an `add_comm_monoid`."]
instance : comm_monoid (α →*[n] β) :=
{ mul := (*),
  mul_assoc := λ a b c, by { ext, apply mul_assoc },
  one := 1,
  one_mul := λ a, by { ext, apply one_mul },
  mul_one := λ a, by { ext, apply mul_one },
  mul_comm :=  λ a b, by { ext, apply mul_comm },
  npow := λ m f,
  { to_fun := λ x, f x ^ m,
    map_prod_eq_map_prod' := λ s t hs ht h,
      by rw [prod_map_pow_right, prod_map_pow_right, f.map_prod hs ht h] },
  npow_zero' := λ f, by { ext x, exact pow_zero _ },
  npow_succ' := λ n f, by { ext x, exact pow_succ _ _ } }

/-- If `β` is a commutative group, then `α →*[n] β` is a commutative group too. -/
@[to_additive "If `β` is an additive commutative group, then `α →*[n] β` is an additive commutative
group too."]
instance {β} [comm_group β] : comm_group (α →*[n] β) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { intros, ext, apply div_eq_mul_inv },
  mul_left_inv := by { intros, ext, apply mul_left_inv },
  zpow := λ n f, { to_fun := λ x, (f x) ^ n,
    map_prod_eq_map_prod' := λ s t hs ht h,
      by rw [prod_map_zpow_right, prod_map_zpow_right, f.map_prod hs ht h] },
  zpow_zero' := λ f, by { ext x, exact zpow_zero _ },
  zpow_succ' := λ n f, by { ext x, simp_rw [zpow_of_nat, pow_succ, mul_apply, coe_mk] },
  zpow_neg'  := λ n f, by { ext x, simp_rw [zpow_neg_succ_of_nat, zpow_coe_nat], refl },
  ..freiman_hom.comm_monoid }

end freiman_hom

/-! ### Hom hierarchy -/

--TODO: change to `monoid_hom_class F α β → freiman_hom_class F α β n` once #9888 is merged
instance monoid_hom.freiman_hom_class : freiman_hom_class (α →* β) α β n :=
{ coe := coe_fn,
  coe_injective' := λ f g h, by { cases f, cases g, cases h, refl },
  map_prod_eq_map_prod' := λ f s t hs ht h, by rw [←f.map_multiset_prod, h, f.map_multiset_prod] }

/-- A `monoid_hom` is naturally a `freiman_hom`. -/
@[to_additive add_monoid_hom.to_add_freiman_hom "An `add_monoid_hom` is naturally an
`add_freiman_hom`"]
def monoid_hom.to_freiman_hom (n : ℕ) (f : α →* β) : α →*[n] β :=
{ to_fun := f,
  map_prod_eq_map_prod' := λ s t hs ht hst, by rw [←f.map_multiset_prod, hst, f.map_multiset_prod] }

@[simp, to_additive]
lemma monoid_hom.to_freiman_hom_coe (f : α →* β) : (f.to_freiman_hom n : α → β) = f := rfl

@[to_additive]
lemma monoid_hom.to_freiman_hom_injective :
  function.injective (monoid_hom.to_freiman_hom n : (α →* β) → α →*[n] β) :=
λ f g h, monoid_hom.ext $ freiman_hom.ext_iff.mp h

end comm_monoid

section cancel_comm_monoid
variables [comm_monoid α] [cancel_comm_monoid β] {m n : ℕ}

@[to_additive]
lemma freiman_hom.map_prod_of_le (f : α →*[n] β) {s t : multiset α} (hs : s.card = m)
  (ht : t.card = m) (hst : s.prod = t.prod) (h : m ≤ n) :
  (s.map f).prod = (t.map f).prod :=
begin
  suffices : ((s + repeat 1 (n - m)).map f).prod = ((t + repeat 1 (n - m)).map f).prod,
  { simp_rw [map_add, prod_add] at this,
    exact mul_right_cancel this },
  refine f.map_prod _ _ _,
  { rw [card_add, hs, card_repeat, add_tsub_cancel_of_le h] },
  { rw [card_add, ht, card_repeat, add_tsub_cancel_of_le h] },
  { rw [prod_add, prod_add, hst] }
end

@[to_additive]
lemma map_prod_eq_map_prod_of_le [freiman_hom_class F α β n] (f : F) {s t : multiset α}
  (hs : s.card = m) (ht : t.card = m) (hst : s.prod = t.prod) (h : m ≤ n) :
  (s.map f).prod = (t.map f).prod :=
begin
  suffices : ((s + repeat 1 (n - m)).map f).prod = ((t + repeat 1 (n - m)).map f).prod,
  { simp_rw [map_add, prod_add] at this,
    exact mul_right_cancel this },
  refine map_prod_eq_map_prod f _ _ _,
  { rw [card_add, hs, card_repeat, add_tsub_cancel_of_le h] },
  { rw [card_add, ht, card_repeat, add_tsub_cancel_of_le h] },
  { rw [prod_add, prod_add, hst] }
end

/-- `α →*[m] β` is naturally included in  `α →*[n] β` for any `m ≤ n`. -/
@[to_additive add_freiman_hom.to_add_freiman_hom "`α →+[m] β` is naturally included in  `α →+[n] β`
for any `m ≤ n`"]
def freiman_hom.to_freiman_hom (h : m ≤ n) (f : α →*[n] β) : α →*[m] β :=
{ to_fun := f,
  map_prod_eq_map_prod' := λ s t hs ht hst, f.map_prod_of_le hs ht hst h }

/-- A `n`-Freiman homomorphism is also a `m`-Freiman homomorphism for any `m ≤ n`. -/
@[to_additive add_freiman_hom.add_freiman_hom_class_of_le "An additive `n`-Freiman homomorphism is
also an additive `m`-Freiman homomorphism for any `m ≤ n`."]
def freiman_hom.freiman_hom_class_of_le (h : m ≤ n) : freiman_hom_class (α →*[n] β) α β m :=
{ coe := coe_fn,
  coe_injective' := fun_like.coe_injective,
  map_prod_eq_map_prod' := λ f s t hs ht hst, map_prod_eq_map_prod_of_le f hs ht hst h }

@[simp, to_additive add_freiman_hom.to_add_freiman_hom_coe]
lemma freiman_hom.to_freiman_hom_coe (h : m ≤ n) (f : α →*[n] β) :
  (f.to_freiman_hom h : α → β) = f := rfl

@[to_additive]
lemma freiman_hom.to_freiman_hom_injective (h : m ≤ n) :
  function.injective (freiman_hom.to_freiman_hom h : (α →*[n] β) → α →*[m] β) :=
λ f g hfg, freiman_hom.ext $ by convert freiman_hom.ext_iff.1 hfg

end cancel_comm_monoid
