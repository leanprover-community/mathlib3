/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.group.type_tags
import algebra.group_with_zero.basic
import data.pi.algebra

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

* ``infix ` ≃* `:25 := mul_equiv``
* ``infix ` ≃+ `:25 := add_equiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/

variables {F α β A B M N P Q G H : Type*}

/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive inverse from a bijection which preserves addition."]
def mul_hom.inverse [has_mul M] [has_mul N] (f : M →ₙ* N) (g : N → M)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) : N →ₙ* M :=
{ to_fun   := g,
  map_mul' := λ x y,
    calc g (x * y) = g (f (g x) * f (g y)) : by rw [h₂ x, h₂ y]
               ... = g (f (g x * g y)) : by rw f.map_mul
               ... = g x * g y : h₁ _, }

/-- The inverse of a bijective `monoid_hom` is a `monoid_hom`. -/
@[to_additive "The inverse of a bijective `add_monoid_hom` is an `add_monoid_hom`.", simps]
def monoid_hom.inverse {A B : Type*} [monoid A] [monoid B] (f : A →* B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  B →* A :=
{ to_fun   := g,
  map_one' := by rw [← f.map_one, h₁],
  .. (f : A →ₙ* B).inverse g h₁ h₂, }

set_option old_structure_cmd true

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
@[ancestor equiv add_hom]
structure add_equiv (A B : Type*) [has_add A] [has_add B] extends A ≃ B, add_hom A B

/-- `add_equiv_class F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `add_equiv`. -/
class add_equiv_class (F A B : Type*) [has_add A] [has_add B]
  extends equiv_like F A B :=
(map_add : ∀ (f : F) a b, f (a + b) = f a + f b)

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc add_equiv.to_equiv
/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc add_equiv.to_add_hom

/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[ancestor equiv mul_hom, to_additive]
structure mul_equiv (M N : Type*) [has_mul M] [has_mul N] extends M ≃ N, M →ₙ* N

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc mul_equiv.to_equiv
/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc mul_equiv.to_mul_hom

/-- `mul_equiv_class F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `mul_equiv`. -/
@[to_additive]
class mul_equiv_class (F A B : Type*) [has_mul A] [has_mul B]
  extends equiv_like F A B :=
(map_mul : ∀ (f : F) a b, f (a * b) = f a * f b)

infix ` ≃* `:25 := mul_equiv
infix ` ≃+ `:25 := add_equiv

namespace mul_equiv_class
variables (F)

@[priority 100, -- See note [lower instance priority]
  to_additive]
instance [has_mul M] [has_mul N] [h : mul_equiv_class F M N] : mul_hom_class F M N :=
{ coe := (coe : F → M → N),
  coe_injective' := @fun_like.coe_injective F _ _ _,
  .. h }

@[priority 100, -- See note [lower instance priority]
  to_additive]
instance [mul_one_class M] [mul_one_class N] [mul_equiv_class F M N] :
  monoid_hom_class F M N :=
{ coe := (coe : F → M → N),
  map_one := λ e,
  calc e 1 = e 1 * 1 : (mul_one _).symm
       ... = e 1 * e (inv e (1 : N) : M) : congr_arg _ (right_inv e 1).symm
       ... = e (inv e (1 : N)) : by rw [← map_mul, one_mul]
       ... = 1 : right_inv e 1,
  .. mul_equiv_class.mul_hom_class F }

@[priority 100] -- See note [lower instance priority]
instance to_monoid_with_zero_hom_class {α β : Type*} [mul_zero_one_class α]
  [mul_zero_one_class β] [mul_equiv_class F α β] : monoid_with_zero_hom_class F α β :=
{ map_zero := λ e, calc e 0 = e 0 * e (equiv_like.inv e 0) : by rw [←map_mul, zero_mul]
                        ... = 0 : by { convert mul_zero _, exact equiv_like.right_inv e _ }
  ..mul_equiv_class.monoid_hom_class _ }

variables {F}

@[simp, to_additive]
lemma map_eq_one_iff {M N} [mul_one_class M] [mul_one_class N] [mul_equiv_class F M N]
  (h : F) {x : M} : h x = 1 ↔ x = 1 :=
map_eq_one_iff h (equiv_like.injective h)

@[to_additive]
lemma map_ne_one_iff {M N} [mul_one_class M] [mul_one_class N] [mul_equiv_class F M N]
  (h : F) {x : M} :
  h x ≠ 1 ↔ x ≠ 1 :=
map_ne_one_iff h (equiv_like.injective h)

end mul_equiv_class

@[to_additive] instance [has_mul α] [has_mul β] [mul_equiv_class F α β] : has_coe_t F (α ≃* β) :=
⟨λ f, { to_fun := f, inv_fun := equiv_like.inv f, left_inv := equiv_like.left_inv f,
  right_inv := equiv_like.right_inv f, map_mul' := map_mul f }⟩

namespace mul_equiv

@[to_additive]
instance [has_mul M] [has_mul N] : has_coe_to_fun (M ≃* N) (λ _, M → N) := ⟨mul_equiv.to_fun⟩

@[to_additive]
instance [has_mul M] [has_mul N] : mul_equiv_class (M ≃* N) M N :=
{ coe := to_fun, inv := inv_fun, left_inv := left_inv, right_inv := right_inv,
  coe_injective' := λ f g h₁ h₂, by { cases f, cases g, congr' },
  map_mul := map_mul' }

variables [has_mul M] [has_mul N] [has_mul P] [has_mul Q]

@[simp, to_additive]
lemma to_equiv_eq_coe (f : M ≃* N) : f.to_equiv = f := rfl

@[simp, to_additive]
lemma to_fun_eq_coe {f : M ≃* N} : f.to_fun = f := rfl

@[simp, to_additive]
lemma coe_to_equiv {f : M ≃* N} : ⇑(f : M ≃ N) = f := rfl

@[simp, to_additive]
lemma coe_to_mul_hom {f : M ≃* N} : ⇑f.to_mul_hom = f := rfl

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive "An additive isomorphism preserves addition."]
protected lemma map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y := map_mul f

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N :=
⟨f.1, f.2, f.3, f.4, h⟩

@[to_additive]
protected lemma bijective (e : M ≃* N) : function.bijective e := equiv_like.bijective e

@[to_additive]
protected lemma injective (e : M ≃* N) : function.injective e := equiv_like.injective e

@[to_additive]
protected lemma surjective (e : M ≃* N) : function.surjective e := equiv_like.surjective e

/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive "The identity map is an additive isomorphism."]
def refl (M : Type*) [has_mul M] : M ≃* M :=
{ map_mul' := λ _ _, rfl,
..equiv.refl _}

@[to_additive]
instance : inhabited (M ≃* M) := ⟨refl M⟩

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive "The inverse of an isomorphism is an isomorphism."]
def symm (h : M ≃* N) : N ≃* M :=
{ map_mul' := (h.to_mul_hom.inverse h.to_equiv.symm h.left_inv h.right_inv).map_mul,
  .. h.to_equiv.symm}

@[simp, to_additive]
lemma inv_fun_eq_symm {f : M ≃* N} : f.inv_fun = f.symm := rfl

/-- See Note [custom simps projection] -/
-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.
@[to_additive "See Note custom simps projection"]
def simps.symm_apply (e : M ≃* N) : N → M := e.symm

initialize_simps_projections add_equiv (to_fun → apply, inv_fun → symm_apply)
initialize_simps_projections mul_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp, to_additive]
theorem to_equiv_symm (f : M ≃* N) : f.symm.to_equiv = f.to_equiv.symm := rfl

@[simp, to_additive]
theorem coe_mk (f : M → N) (g h₁ h₂ h₃) : ⇑(mul_equiv.mk f g h₁ h₂ h₃) = f := rfl

@[simp, to_additive]
lemma to_equiv_mk (f : M → N) (g : N → M) (h₁ h₂ h₃) :
  (mk f g h₁ h₂ h₃).to_equiv = ⟨f, g, h₁, h₂⟩ := rfl

@[simp, to_additive]
lemma symm_symm : ∀ (f : M ≃* N), f.symm.symm = f
| ⟨f, g, h₁, h₂, h₃⟩ := rfl

@[to_additive]
lemma symm_bijective : function.bijective (symm : (M ≃* N) → (N ≃* M)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp, to_additive]
theorem symm_mk (f : M → N) (g h₁ h₂ h₃) :
  (mul_equiv.mk f g h₁ h₂ h₃).symm =
  { to_fun := g, inv_fun := f, ..(mul_equiv.mk f g h₁ h₂ h₃).symm} := rfl

@[simp, to_additive]
theorem refl_symm : (refl M).symm = refl M := rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : (M ≃* P) :=
{ map_mul' := λ x y, show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y),
    by rw [h1.map_mul, h2.map_mul],
  ..h1.to_equiv.trans h2.to_equiv }

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[simp, to_additive "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
lemma apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
e.to_equiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[simp, to_additive "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
lemma symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
e.to_equiv.symm_apply_apply x

@[simp, to_additive]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id := funext e.symm_apply_apply

@[simp, to_additive]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp, to_additive]
theorem coe_refl : ⇑(refl M) = id := rfl

@[simp, to_additive]
theorem refl_apply (m : M) : refl M m = m := rfl

@[simp, to_additive]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[simp, to_additive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[simp, to_additive] theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
  (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

@[simp, to_additive] theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
e.injective.eq_iff

@[to_additive]
lemma apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

@[to_additive]
lemma symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
e.to_equiv.symm_apply_eq

@[to_additive]
lemma eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
e.to_equiv.eq_symm_apply

@[to_additive] lemma eq_comp_symm {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
  f = g ∘ e.symm ↔ f ∘ e = g := e.to_equiv.eq_comp_symm f g

@[to_additive] lemma comp_symm_eq {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
  g ∘ e.symm = f ↔ g = f ∘ e := e.to_equiv.comp_symm_eq f g

@[to_additive] lemma eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
  f = e.symm ∘ g ↔ e ∘ f = g := e.to_equiv.eq_symm_comp f g

@[to_additive] lemma symm_comp_eq {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
  e.symm ∘ g = f ↔ g = e ∘ f := e.to_equiv.symm_comp_eq f g

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext, to_additive
  "Two additive isomorphisms agree if they are defined by the same underlying function."]
lemma ext {f g : mul_equiv M N} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

@[to_additive] lemma ext_iff {f g : mul_equiv M N} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[simp, to_additive] lemma mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) :
  (⟨e, e', h₁, h₂, h₃⟩ : M ≃* N) = e := ext $ λ _, rfl

@[simp, to_additive] lemma mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) :
  (mul_equiv.mk f ⇑e h₁ h₂ h₃ : N ≃* M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[to_additive] protected lemma congr_arg {f : mul_equiv M N} {x x' : M} : x = x' → f x = f x' :=
fun_like.congr_arg f

@[to_additive] protected lemma congr_fun {f g : mul_equiv M N} (h : f = g) (x : M) : f x = g x :=
fun_like.congr_fun h x

/-- The `mul_equiv` between two monoids with a unique element. -/
@[to_additive "The `add_equiv` between two add_monoids with a unique element."]
def mul_equiv_of_unique_of_unique {M N}
  [unique M] [unique N] [has_mul M] [has_mul N] : M ≃* N :=
{ map_mul' := λ _ _, subsingleton.elim _ _,
  ..equiv_of_unique_of_unique }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive
  "There is a unique additive monoid homomorphism between two additive monoids with
a unique element."]
instance {M N} [unique M] [unique N] [has_mul M] [has_mul N] : unique (M ≃* N) :=
{ default := mul_equiv_of_unique_of_unique ,
  uniq := λ _, ext $ λ x, subsingleton.elim _ _}

/-!
## Monoids
-/

/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive "An additive isomorphism of additive monoids sends `0` to `0`
(and is hence an additive monoid isomorphism)."]
protected lemma map_one {M N} [mul_one_class M] [mul_one_class N] (h : M ≃* N) : h 1 = 1 :=
map_one h

@[to_additive]
protected lemma map_eq_one_iff {M N} [mul_one_class M] [mul_one_class N] (h : M ≃* N) {x : M} :
  h x = 1 ↔ x = 1 :=
mul_equiv_class.map_eq_one_iff h

@[to_additive]
lemma map_ne_one_iff {M N} [mul_one_class M] [mul_one_class N] (h : M ≃* N) {x : M} :
  h x ≠ 1 ↔ x ≠ 1 :=
mul_equiv_class.map_ne_one_iff h

/-- A bijective `semigroup` homomorphism is an isomorphism -/
@[to_additive "A bijective `add_semigroup` homomorphism is an isomorphism"]
noncomputable def of_bijective {M N F} [has_mul M] [has_mul N] [mul_hom_class F M N] (f : F)
  (hf : function.bijective f) : M ≃* N :=
{ map_mul' := map_mul f,
  ..equiv.of_bijective f hf }

/--
Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive "Extract the forward direction of an additive equivalence
as an addition-preserving function."]
def to_monoid_hom {M N} [mul_one_class M] [mul_one_class N] (h : M ≃* N) : (M →* N) :=
{ map_one' := h.map_one, .. h }

@[simp, to_additive]
lemma coe_to_monoid_hom {M N} [mul_one_class M] [mul_one_class N] (e : M ≃* N) :
  ⇑e.to_monoid_hom = e :=
rfl

@[to_additive] lemma to_monoid_hom_injective {M N} [mul_one_class M] [mul_one_class N] :
  function.injective (to_monoid_hom : (M ≃* N) → M →* N) :=
λ f g h, mul_equiv.ext (monoid_hom.ext_iff.1 h)


/--
A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive "An additive analogue of `equiv.arrow_congr`,
where the equivalence between the targets is additive.", simps apply]
def arrow_congr {M N P Q : Type*} [has_mul P] [has_mul Q]
  (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q) :=
{ to_fun := λ h n, g (h (f.symm n)),
  inv_fun := λ k m, g.symm (k (f m)),
  left_inv := λ h, by { ext, simp, },
  right_inv := λ k, by { ext, simp, },
  map_mul' := λ h k, by { ext, simp, }, }

/--
A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive "An additive analogue of `equiv.arrow_congr`,
for additive maps from an additive monoid to a commutative additive monoid.", simps apply]
def monoid_hom_congr {M N P Q} [mul_one_class M] [mul_one_class N] [comm_monoid P] [comm_monoid Q]
  (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q) :=
{ to_fun := λ h,
  g.to_monoid_hom.comp (h.comp f.symm.to_monoid_hom),
  inv_fun := λ k,
  g.symm.to_monoid_hom.comp (k.comp f.to_monoid_hom),
  left_inv := λ h, by { ext, simp, },
  right_inv := λ k, by { ext, simp, },
  map_mul' := λ h k, by { ext, simp, }, }

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `mul_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`mul_equiv.arrow_congr`.
-/
@[to_additive add_equiv.Pi_congr_right "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `add_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`add_equiv.arrow_congr`.", simps apply]
def Pi_congr_right {η : Type*}
  {Ms Ns : η → Type*} [Π j, has_mul (Ms j)] [Π j, has_mul (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) : (Π j, Ms j) ≃* (Π j, Ns j) :=
{ to_fun := λ x j, es j (x j),
  inv_fun := λ x j, (es j).symm (x j),
  map_mul' := λ x y, funext $ λ j, (es j).map_mul (x j) (y j),
  .. equiv.Pi_congr_right (λ j, (es j).to_equiv) }

@[simp]
lemma Pi_congr_right_refl {η : Type*} {Ms : η → Type*} [Π j, has_mul (Ms j)] :
  Pi_congr_right (λ j, mul_equiv.refl (Ms j)) = mul_equiv.refl _ := rfl

@[simp]
lemma Pi_congr_right_symm {η : Type*}
  {Ms Ns : η → Type*} [Π j, has_mul (Ms j)] [Π j, has_mul (Ns j)]
  (es : ∀ j, Ms j ≃* Ns j) : (Pi_congr_right es).symm = (Pi_congr_right $ λ i, (es i).symm) := rfl

@[simp]
lemma Pi_congr_right_trans {η : Type*}
  {Ms Ns Ps : η → Type*} [Π j, has_mul (Ms j)] [Π j, has_mul (Ns j)]
  [Π j, has_mul (Ps j)]
  (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
  (Pi_congr_right es).trans (Pi_congr_right fs) = (Pi_congr_right $ λ i, (es i).trans (fs i)) := rfl

/-- A family indexed by a nonempty subsingleton type is equivalent to the element at the single
index. -/
@[to_additive add_equiv.Pi_subsingleton "A family indexed by a nonempty subsingleton type is
equivalent to the element at the single index.", simps]
def Pi_subsingleton
  {ι : Type*} (M : ι → Type*) [Π j, has_mul (M j)] [subsingleton ι] (i : ι) :
  (Π j, M j) ≃* M i :=
{ map_mul' := λ f1 f2, pi.mul_apply _ _ _, ..equiv.Pi_subsingleton M i }

/-!
# Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected lemma map_inv [group G] [division_monoid H] (h : G ≃* H) (x : G) : h x⁻¹ = (h x)⁻¹ :=
map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected lemma map_div [group G] [division_monoid H] (h : G ≃* H) (x y : G) :
  h (x / y) = h x / h y :=
map_div h x y

end mul_equiv

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive /-"Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
and `f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
monoid homomorphisms."-/, simps {fully_applied := ff}]
def monoid_hom.to_mul_equiv [mul_one_class M] [mul_one_class N] (f : M →* N) (g : N →* M)
  (h₁ : g.comp f = monoid_hom.id _) (h₂ : f.comp g = monoid_hom.id _) :
  M ≃* N :=
{ to_fun := f,
  inv_fun := g,
  left_inv := monoid_hom.congr_fun h₁,
  right_inv := monoid_hom.congr_fun h₂,
  map_mul' := f.map_mul }

/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def to_units [group G] : G ≃* Gˣ :=
{ to_fun := λ x, ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩,
  inv_fun := coe,
  left_inv := λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

@[simp, to_additive] lemma coe_to_units [group G] (g : G) :
  (to_units g : G) = g := rfl

@[to_additive]
protected lemma group.is_unit {G} [group G] (x : G) : is_unit x := (to_units x).is_unit

namespace units

variables [monoid M] [monoid N] [monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
{ inv_fun := map h.symm.to_monoid_hom,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  .. map h.to_monoid_hom }

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps apply {fully_applied := ff}]
def mul_left (u : Mˣ) : equiv.perm M :=
{ to_fun    := λx, u * x,
  inv_fun   := λx, ↑u⁻¹ * x,
  left_inv  := u.inv_mul_cancel_left,
  right_inv := u.mul_inv_cancel_left }

@[simp, to_additive]
lemma mul_left_symm (u : Mˣ) : u.mul_left.symm = u⁻¹.mul_left :=
equiv.ext $ λ x, rfl

@[to_additive]
lemma mul_left_bijective (a : Mˣ) : function.bijective ((*) a : M → M) :=
(mul_left a).bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps apply {fully_applied := ff}]
def mul_right (u : Mˣ) : equiv.perm M :=
{ to_fun    := λx, x * u,
  inv_fun   := λx, x * ↑u⁻¹,
  left_inv  := λ x, mul_inv_cancel_right x u,
  right_inv := λ x, inv_mul_cancel_right x u }

@[simp, to_additive]
lemma mul_right_symm (u : Mˣ) : u.mul_right.symm = u⁻¹.mul_right :=
equiv.ext $ λ x, rfl

@[to_additive]
lemma mul_right_bijective (a : Mˣ) : function.bijective ((* a) : M → M) :=
(mul_right a).bijective

end units

namespace equiv

section has_involutive_neg

variables (G) [has_involutive_inv G]

/-- Inversion on a `group` or `group_with_zero` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type.",
  simps apply {fully_applied := ff}]
protected def inv : perm G := inv_involutive.to_perm _

variable {G}

@[simp, to_additive]
lemma inv_symm : (equiv.inv G).symm = equiv.inv G := rfl

end has_involutive_neg

section group
variables [group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mul_left (a : G) : perm G := (to_units a).mul_left

@[simp, to_additive]
lemma coe_mul_left (a : G) : ⇑(equiv.mul_left a) = (*) a := rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
lemma mul_left_symm_apply (a : G) : ((equiv.mul_left a).symm : G → G) = (*) a⁻¹ := rfl

@[simp, to_additive]
lemma mul_left_symm (a : G) : (equiv.mul_left a).symm = equiv.mul_left a⁻¹ :=
ext $ λ x, rfl

@[to_additive]
lemma _root_.group.mul_left_bijective (a : G) : function.bijective ((*) a) :=
(equiv.mul_left a).bijective

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mul_right (a : G) : perm G := (to_units a).mul_right

@[simp, to_additive]
lemma coe_mul_right (a : G) : ⇑(equiv.mul_right a) = λ x, x * a := rfl

@[simp, to_additive]
lemma mul_right_symm (a : G) : (equiv.mul_right a).symm = equiv.mul_right a⁻¹ :=
ext $ λ x, rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
lemma mul_right_symm_apply (a : G) : ((equiv.mul_right a).symm : G → G) = λ x, x * a⁻¹ := rfl

@[to_additive]
lemma _root_.group.mul_right_bijective (a : G) : function.bijective (* a) :=
(equiv.mul_right a).bijective

/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive /-" A version of `equiv.add_left a (-b)` that is defeq to `a - b`. "-/, simps]
protected def div_left (a : G) : G ≃ G :=
{ to_fun := λ b, a / b,
  inv_fun := λ b, b⁻¹ * a,
  left_inv := λ b, by simp [div_eq_mul_inv],
  right_inv := λ b, by simp [div_eq_mul_inv] }

@[to_additive]
lemma div_left_eq_inv_trans_mul_left (a : G) :
  equiv.div_left a = (equiv.inv G).trans (equiv.mul_left a) :=
ext $ λ _, div_eq_mul_inv _ _

/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive /-" A version of `equiv.add_right (-a) b` that is defeq to `b - a`. "-/, simps]
protected def div_right (a : G) : G ≃ G :=
{ to_fun := λ b, b / a,
  inv_fun := λ b, b * a,
  left_inv := λ b, by simp [div_eq_mul_inv],
  right_inv := λ b, by simp [div_eq_mul_inv] }

@[to_additive]
lemma div_right_eq_mul_right_inv (a : G) : equiv.div_right a = equiv.mul_right a⁻¹ :=
ext $ λ _, div_eq_mul_inv _ _

end group

section group_with_zero
variables [group_with_zero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps {fully_applied := ff}]
protected def mul_left₀ (a : G) (ha : a ≠ 0) : perm G :=
(units.mk0 a ha).mul_left

lemma _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) :
  function.bijective ((*) a : G → G) :=
(equiv.mul_left₀ a ha).bijective

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps {fully_applied := ff}]
protected def mul_right₀ (a : G) (ha : a ≠ 0) : perm G :=
(units.mk0 a ha).mul_right

lemma _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) :
  function.bijective ((* a) : G → G) :=
(equiv.mul_right₀ a ha).bijective

end group_with_zero

end equiv

/-- When the group is commutative, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`."]
def mul_equiv.inv (G : Type*) [comm_group G] : G ≃* G :=
{ to_fun   := has_inv.inv,
  inv_fun  := has_inv.inv,
  map_mul' := mul_inv,
  ..equiv.inv G }

/-- When the group with zero is commutative, `equiv.inv₀` is a `mul_equiv`. -/
@[simps apply] def mul_equiv.inv₀ (G : Type*) [comm_group_with_zero G] : G ≃* G :=
{ to_fun   := has_inv.inv,
  inv_fun  := has_inv.inv,
  map_mul' := mul_inv,
  ..equiv.inv G }

@[simp] lemma mul_equiv.inv₀_symm (G : Type*) [comm_group_with_zero G] :
  (mul_equiv.inv₀ G).symm = mul_equiv.inv₀ G := rfl

section type_tags

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative [add_zero_class G] [add_zero_class H] :
  (G ≃+ H) ≃ (multiplicative G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative,
                  f.symm.to_add_monoid_hom.to_multiplicative, f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
def mul_equiv.to_additive [mul_one_class G] [mul_one_class H] :
  (G ≃* H) ≃ (additive G ≃+ additive H) :=
{ to_fun := λ f, ⟨f.to_monoid_hom.to_additive, f.symm.to_monoid_hom.to_additive, f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_add_monoid_hom, f.symm.to_add_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
def add_equiv.to_multiplicative' [mul_one_class G] [add_zero_class H] :
  (additive G ≃+ H) ≃ (G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative',
                  f.symm.to_add_monoid_hom.to_multiplicative'', f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
def mul_equiv.to_additive' [mul_one_class G] [add_zero_class H] :
  (G ≃* multiplicative H) ≃ (additive G ≃+ H) :=
add_equiv.to_multiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
def add_equiv.to_multiplicative'' [add_zero_class G] [mul_one_class H] :
  (G ≃+ additive H) ≃ (multiplicative G ≃* H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative'',
                  f.symm.to_add_monoid_hom.to_multiplicative', f.3, f.4, f.5⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom, f.symm.to_monoid_hom, f.3, f.4, f.5⟩,
  left_inv := λ x, by { ext, refl, },
  right_inv := λ x, by { ext, refl, }, }

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
def mul_equiv.to_additive'' [add_zero_class G] [mul_one_class H] :
  (multiplicative G ≃* H) ≃ (G ≃+ additive H) :=
add_equiv.to_multiplicative''.symm

end type_tags
