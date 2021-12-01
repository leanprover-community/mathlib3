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

* `A →*[n] β`: Multiplicative `n`-Freiman homomorphism
* `α →+[n] β`: Additive`n`-Freiman homomorphism

## References

[Yufei Zhao, *Graph Theory and Additivite Combinatorics][https://yufeizhao.com/gtac/]

## TODO

`monoid_hom.to_freiman_hom` could be relaxed to `mul_hom.to_freiman_hom` by proving
`(s.map f).prod = (t.map f).prod` directly by induction instead of going through `f s.prod`.

Define `n`-Freiman isomorphisms.

Affine maps induce Freiman homs. Concretely, provide the `add_freiman_hom_class (α →ₐ[𝕜] β) A β n`
instance.
-/

open multiset

variables {F α β γ δ G : Type*}

/-- An additive `n`-Freiman homomorphism is a map which preserves sums of `n` elements. -/
structure add_freiman_hom (A : set α) (β : Type*) [add_comm_monoid α] [add_comm_monoid β] (n : ℕ) :=
(to_fun : α → β)
(map_sum_eq_map_sum' {s t : multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
  (hs : s.card = n) (ht : t.card = n) (h : s.sum = t.sum) :
  (s.map to_fun).sum = (t.map to_fun).sum)

/-- A `n`-Freiman homomorphism is a map which preserves products of `n` elements. -/
@[to_additive add_freiman_hom]
structure freiman_hom (A : set α) (β : Type*) [comm_monoid α] [comm_monoid β] (n : ℕ) :=
(to_fun : α → β)
(map_prod_eq_map_prod' {s t : multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A)
  (hs : s.card = n) (ht : t.card = n) (h : s.prod = t.prod) :
  (s.map to_fun).prod = (t.map to_fun).prod)

notation A ` →+[`:25 n:25 `] `:0 β:0 := add_freiman_hom A β n
notation A ` →*[`:25 n:25 `] `:0 β:0 := freiman_hom A β n

/-- `add_freiman_hom_class F s β n` states that `F` is a type of `n`-ary sums-preserving morphisms.
You should extend this class when you extend `add_freiman_hom`. -/
class add_freiman_hom_class (F : Type*) (A : out_param $ set α) (β : out_param $ Type*)
  [add_comm_monoid α] [add_comm_monoid β] (n : ℕ) [fun_like F α (λ _, β)] :=
(map_sum_eq_map_sum' (f : F) {s t : multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
  (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n) (h : s.sum = t.sum) :
  (s.map f).sum = (t.map f).sum)

/-- `freiman_hom_class F A β n` states that `F` is a type of `n`-ary products-preserving morphisms.
You should extend this class when you extend `freiman_hom`. -/
@[to_additive add_freiman_hom_class]
class freiman_hom_class (F : Type*) (A : out_param $ set α) (β : out_param $ Type*) [comm_monoid α]
  [comm_monoid β] (n : ℕ) [fun_like F α (λ _, β)] :=
(map_prod_eq_map_prod' (f : F) {s t : multiset α} (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A)
  (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n) (h : s.prod = t.prod) :
  (s.map f).prod = (t.map f).prod)

variables [fun_like F α (λ _, β)]

section comm_monoid
variables [comm_monoid α] [comm_monoid β] [comm_monoid γ] [comm_monoid δ] [comm_group G] {A : set α}
  {B : set β} {C : set γ} {n : ℕ}

@[to_additive]
lemma map_prod_eq_map_prod [freiman_hom_class F A β n] (f : F) {s t : multiset α}
  (hsA : ∀ ⦃x⦄, x ∈ s → x ∈ A) (htA : ∀ ⦃x⦄, x ∈ t → x ∈ A) (hs : s.card = n) (ht : t.card = n)
  (h : s.prod = t.prod) :
  (s.map f).prod = (t.map f).prod :=
freiman_hom_class.map_prod_eq_map_prod' f hsA htA hs ht h

namespace freiman_hom

@[to_additive]
instance fun_like : fun_like (A →*[n] β) α (λ _, β) :=
{ coe := to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

@[to_additive]
instance freiman_hom_class : freiman_hom_class (A →*[n] β) A β n :=
{ map_prod_eq_map_prod' := map_prod_eq_map_prod' }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
@[to_additive]
instance : has_coe_to_fun (A →*[n] β) (λ _, α → β) := ⟨to_fun⟩

initialize_simps_projections freiman_hom (to_fun → apply)

@[simp, to_additive]
lemma to_fun_eq_coe (f : A →*[n] β) : f.to_fun = f := rfl

@[ext, to_additive]
lemma ext ⦃f g : A →*[n] β⦄ (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[simp, to_additive]
lemma coe_mk (f : α → β) (h : ∀ s t : multiset α, (∀ ⦃x⦄, x ∈ s → x ∈ A) → (∀ ⦃x⦄, x ∈ t → x ∈ A) →
  s.card = n → t.card = n → s.prod = t.prod → (s.map f).prod = (t.map f).prod) :
  ⇑(mk f h) = f := rfl

@[simp, to_additive] lemma mk_coe (f : A →*[n] β) (h) : mk f h = f := ext $ λ _, rfl

/-- The identity map from a commutative monoid to itself. -/
@[to_additive "The identity map from an additive commutative monoid to itself.", simps]
protected def id (A : set α) (n : ℕ) : A →*[n] α  :=
{ to_fun := λ x, x, map_prod_eq_map_prod' := λ s t _ _ _ _ h, by rw [map_id', map_id', h] }

/-- Composition of Freiman homomorphisms as a Freiman homomorphism. -/
@[to_additive "Composition of additive Freiman homomorphisms as an additive Freiman homomorphism."]
protected def comp (f : B →*[n] γ) (g : A →*[n] β) (hAB : A.maps_to g B) : A →*[n] γ :=
{ to_fun := f ∘ g,
  map_prod_eq_map_prod' := λ s t hsA htA hs ht h, begin
    rw [←map_map,
    map_prod_eq_map_prod f _ _ ((s.card_map _).trans hs) ((t.card_map _).trans ht)
      (map_prod_eq_map_prod g hsA htA hs ht h), map_map],
    { rintro x hx,
      rw mem_map at hx,
      obtain ⟨x, hx, rfl⟩ := hx,
      exact hAB (hsA hx) },
    { rintro x hx,
      rw mem_map at hx,
      obtain ⟨x, hx, rfl⟩ := hx,
      exact hAB (htA hx) }
  end }

@[simp, to_additive]
lemma coe_comp (f : B →*[n] γ) (g : A →*[n] β) {hfg} : ⇑(f.comp g hfg) = f ∘ g := rfl

@[to_additive]
lemma comp_apply (f : B →*[n] γ) (g : A →*[n] β) {hfg} (x : α) : f.comp g hfg x = f (g x) := rfl

@[to_additive]
lemma comp_assoc (f : A →*[n] β) (g : B →*[n] γ) (h : C →*[n] δ) {hf} {hhg} {hgf}
  {hh : A.maps_to (g.comp f hgf) C} :
  (h.comp g hhg).comp f hf = h.comp (g.comp f hgf) hh := rfl

@[to_additive]
lemma cancel_right {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : function.surjective f) {hg₁} {hg₂} :
  g₁.comp f hg₁ = g₂.comp f hg₂ ↔ g₁ = g₂ :=
⟨λ h, ext $ (forall_iff_forall_surj hf).1 (fun_like.ext_iff.1 h), λ h, h ▸ rfl⟩

@[to_additive]
lemma cancel_left {g : B →*[n] γ} {f₁ f₂ : A →*[n] β} (hg : function.injective g) {hf₁} {hf₂} :
  g.comp f₁ hf₁ = g.comp f₂ hf₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply],
  λ h, h ▸ rfl⟩

@[to_additive]
lemma cancel_right_on {g₁ g₂ : B →*[n] γ} {f : A →*[n] β} (hf : A.surj_on f B) {hg₁} {hg₂} :
  A.eq_on (g₁.comp f hg₁) (g₂.comp f hg₂) ↔ B.eq_on g₁ g₂ :=
⟨λ h, begin

end, λ h, h ▸ rfl⟩

@[to_additive]
lemma cancel_left {g : B →*[n] γ} {f₁ f₂ : A →*[n] β} (hg : function.injective g) {hg₁} {hg₂} :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, ext $ λ x, hg $ by rw [← comp_apply, h, comp_apply],
  λ h, h ▸ rfl⟩

@[simp, to_additive] lemma comp_id (f : A →*[n] β) {hf} : f.comp (freiman_hom.id A n) hf = f :=
ext $ λ x, rfl

@[simp, to_additive] lemma id_comp (f : A →*[n] β) {hf} : (freiman_hom.id B n).comp f hf = f :=
ext $ λ x, rfl

/-- `freiman_hom.const A n b` is the Freiman homomorphism sending everything to `b`. -/
@[to_additive "`add_freiman_hom.const n b` is the Freiman homomorphism sending everything to `b`."]
def const (A : set α) (n : ℕ) (b : β) : A →*[n] β :=
{ to_fun := λ _, b,
  map_prod_eq_map_prod' := λ s t hs ht _,
    by rw [multiset.map_const, multiset.map_const, prod_repeat, prod_repeat, hs, ht] }

@[simp, to_additive] lemma const_apply (n : ℕ) (b : β) (x : α) : const n b x = b := rfl

@[simp, to_additive] lemma const_comp (n : ℕ) (b : γ) (f : A →*[n] β) :
  (const n b).comp f = const n b := rfl

/-- `1` is the Freiman homomorphism sending everything to `1`. -/
@[to_additive "`0` is the Freiman homomorphism sending everything to `0`."]
instance : has_one (A →*[n] β) := ⟨const A n 1⟩

@[simp, to_additive] lemma one_apply (x : α) : (1 : A →*[n] β) x = 1 := rfl

@[simp, to_additive] lemma one_comp (f : A →*[n] β) : (1 : B →*[n] γ).comp f = 1 := rfl

@[to_additive] instance : inhabited (A →*[n] β) := ⟨1⟩

/-- `f * g` is the Freiman homomorphism  sends `x` to `f x * g x`. -/
@[to_additive "`f + g` is the Freiman homomorphism sending `x` to `f x + g x`."]
instance : has_mul (A →*[n] β) :=
⟨λ f g, { to_fun := λ x, f x * g x,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_mul, prod_map_mul, map_prod_eq_map_prod f hs ht h,
           map_prod_eq_map_prod g hs ht h] }⟩

@[simp, to_additive] lemma mul_apply (f g : A →*[n] β) (x : α) : (f * g) x = f x * g x := rfl

@[to_additive] lemma mul_comp (g₁ g₂ : B →*[n] γ) (f : A →*[n] β) :
  (g₁ * g₂).comp f = g₁.comp f * g₂.comp f := rfl

/-- If `f` is a Freiman homomorphism to a commutative group, then `f⁻¹` is the Freiman homomorphism
sending `x` to `(f x)⁻¹`. -/
@[to_additive]
instance : has_inv (α →*[n] G) :=
⟨λ f, { to_fun := λ x, (f x)⁻¹,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_inv', prod_map_inv', map_prod_eq_map_prod f hs ht h] }⟩

@[simp, to_additive] lemma inv_apply (f : α →*[n] G) (x : α) : f⁻¹ x = (f x)⁻¹ := rfl

@[simp, to_additive] lemma inv_comp (f : β →*[n] G) (g : A →*[n] β) : f⁻¹.comp g = (f.comp g)⁻¹ :=
ext $ λ x, rfl

/-- If `f` and `g` are Freiman homomorphisms to a commutative group, then `f / g` is the Freiman
homomorphism sending `x` to `f x / g x`. -/
@[to_additive "If `f` and `g` are additive Freiman homomorphisms to an additive commutative group,
then `f - g` is the additive Freiman homomorphism sending `x` to `f x - g x`"]
instance : has_div (α →*[n] G) :=
⟨λ f g, { to_fun := λ x, f x / g x,
  map_prod_eq_map_prod' := λ s t hs ht h,
    by rw [prod_map_div, prod_map_div, map_prod_eq_map_prod f hs ht h,
           map_prod_eq_map_prod g hs ht h] }⟩

@[simp, to_additive] lemma div_apply (f g : α →*[n] G) (x : α) : (f / g) x = f x / g x := rfl

@[simp, to_additive] lemma div_comp (f₁ f₂ : β →*[n] G) (g : A →*[n] β) :
  (f₁ / f₂).comp g = f₁.comp g / f₂.comp g :=
ext $ λ x, rfl

/-! ### Instances -/

/-- `A →*[n] β` is a `comm_monoid`. -/
@[to_additive "`α →+[n] β` is an `add_comm_monoid`."]
instance : comm_monoid (A →*[n] β) :=
{ mul := (*),
  mul_assoc := λ a b c, by { ext, apply mul_assoc },
  one := 1,
  one_mul := λ a, by { ext, apply one_mul },
  mul_one := λ a, by { ext, apply mul_one },
  mul_comm :=  λ a b, by { ext, apply mul_comm },
  npow := λ m f,
  { to_fun := λ x, f x ^ m,
    map_prod_eq_map_prod' := λ s t hs ht h,
      by rw [prod_map_pow_right, prod_map_pow_right, map_prod_eq_map_prod f hs ht h] },
  npow_zero' := λ f, by { ext x, exact pow_zero _ },
  npow_succ' := λ n f, by { ext x, exact pow_succ _ _ } }

/-- If `β` is a commutative group, then `A →*[n] β` is a commutative group too. -/
@[to_additive "If `β` is an additive commutative group, then `A →*[n] β` is an additive commutative
group too."]
instance {β} [comm_group β] : comm_group (A →*[n] β) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { intros, ext, apply div_eq_mul_inv },
  mul_left_inv := by { intros, ext, apply mul_left_inv },
  zpow := λ n f, { to_fun := λ x, (f x) ^ n,
    map_prod_eq_map_prod' := λ s t hs ht h,
      by rw [prod_map_zpow_right, prod_map_zpow_right, map_prod_eq_map_prod f hs ht h] },
  zpow_zero' := λ f, by { ext x, exact zpow_zero _ },
  zpow_succ' := λ n f, by { ext x, simp_rw [zpow_of_nat, pow_succ, mul_apply, coe_mk] },
  zpow_neg'  := λ n f, by { ext x, simp_rw [zpow_neg_succ_of_nat, zpow_coe_nat], refl },
  ..freiman_hom.comm_monoid }

end freiman_hom

/-! ### Hom hierarchy -/

--TODO: merge this with `monoid_hom_class.fun_like` once #9888 is merged
@[to_additive]
instance monoid_hom.fun_like : fun_like (α →* β) α (λ _, β) :=
{ coe := coe_fn,
  coe_injective' := λ f g h, by { cases f, cases g, cases h, refl } }

--TODO: change to `monoid_hom_class F A β → freiman_hom_class F A β n` once #9888 is merged
@[to_additive]
instance monoid_hom.freiman_hom_class : freiman_hom_class (α →* β) α β n :=
{ map_prod_eq_map_prod' := λ f s t hs ht h, by rw [←f.map_multiset_prod, h, f.map_multiset_prod] }

/-- A `monoid_hom` is naturally a `freiman_hom`. -/
@[to_additive add_monoid_hom.to_add_freiman_hom "An `add_monoid_hom` is naturally an
`add_freiman_hom`"]
def monoid_hom.to_freiman_hom (n : ℕ) (f : α →* β) : A →*[n] β :=
{ to_fun := f,
  map_prod_eq_map_prod' := λ s t, map_prod_eq_map_prod f }

@[simp, to_additive]
lemma monoid_hom.to_freiman_hom_coe (f : α →* β) : (f.to_freiman_hom n : α → β) = f := rfl

@[to_additive]
lemma monoid_hom.to_freiman_hom_injective :
  function.injective (monoid_hom.to_freiman_hom n : (α →* β) → A →*[n] β) :=
λ f g h, monoid_hom.ext $ show _, from fun_like.ext_iff.mp h

end comm_monoid

section cancel_comm_monoid
variables [comm_monoid α] [cancel_comm_monoid β] {m n : ℕ}

@[to_additive]
lemma map_prod_eq_map_prod_of_le [freiman_hom_class F A β n] (f : F) {s t : multiset α}
  (hs : s.card = m) (ht : t.card = m) (hst : s.prod = t.prod) (h : m ≤ n) :
  (s.map f).prod = (t.map f).prod :=
begin
  suffices : ((s + repeat 1 (n - m)).map f).prod = ((t + repeat 1 (n - m)).map f).prod,
  { simp_rw [map_add, prod_add] at this,
    exact mul_right_cancel this },
  refine map_prod_eq_map_prod f _ _ _,
  swap, assumption, -- Can't infer `n` from the context, so do it manually.
  { rw [card_add, hs, card_repeat, add_tsub_cancel_of_le h] },
  { rw [card_add, ht, card_repeat, add_tsub_cancel_of_le h] },
  { rw [prod_add, prod_add, hst] }
end

/-- `α →*[m] β` is naturally included in  `A →*[n] β` for any `m ≤ n`. -/
@[to_additive add_freiman_hom.to_add_freiman_hom "`α →+[m] β` is naturally included in  `α →+[n] β`
for any `m ≤ n`"]
def freiman_hom.to_freiman_hom (h : m ≤ n) (f : A →*[n] β) : α →*[m] β :=
{ to_fun := f,
  map_prod_eq_map_prod' := λ s t hs ht hst, map_prod_eq_map_prod_of_le f hs ht hst h }

/-- A `n`-Freiman homomorphism is also a `m`-Freiman homomorphism for any `m ≤ n`. -/
@[to_additive add_freiman_hom.add_freiman_hom_class_of_le "An additive `n`-Freiman homomorphism is
also an additive `m`-Freiman homomorphism for any `m ≤ n`."]
def freiman_hom.freiman_hom_class_of_le [freiman_hom_class F A β n] (h : m ≤ n) :
  freiman_hom_class F A β m :=
{ map_prod_eq_map_prod' := λ f s t hs ht hst, map_prod_eq_map_prod_of_le f hs ht hst h }

@[simp, to_additive add_freiman_hom.to_add_freiman_hom_coe]
lemma freiman_hom.to_freiman_hom_coe (h : m ≤ n) (f : A →*[n] β) :
  (f.to_freiman_hom h : α → β) = f := rfl

@[to_additive]
lemma freiman_hom.to_freiman_hom_injective (h : m ≤ n) :
  function.injective (freiman_hom.to_freiman_hom h : (A →*[n] β) → α →*[m] β) :=
λ f g hfg, freiman_hom.ext $ by convert fun_like.ext_iff.1 hfg

end cancel_comm_monoid
