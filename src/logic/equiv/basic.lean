/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import logic.equiv.defs
import data.option.basic
import data.prod.basic
import data.sigma.basic
import data.subtype
import data.sum.basic
import logic.function.conjugate

/-!
# Equivalence between types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we continue the work on equivalences begun in `logic/equiv/defs.lean`, defining

* canonical isomorphisms between various types: e.g.,

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/

open function

universes u v w z
variables {α : Sort u} {β : Sort v} {γ : Sort w}

namespace equiv

/-- `pprod α β` is equivalent to `α × β` -/
@[simps apply symm_apply]
def pprod_equiv_prod {α β : Type*} : pprod α β ≃ α × β :=
{ to_fun := λ x, (x.1, x.2),
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

/-- Product of two equivalences, in terms of `pprod`. If `α ≃ β` and `γ ≃ δ`, then
`pprod α γ ≃ pprod β δ`. -/
@[congr, simps apply]
def pprod_congr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : pprod α γ ≃ pprod β δ :=
{ to_fun := λ x, ⟨e₁ x.1, e₂ x.2⟩,
  inv_fun := λ x, ⟨e₁.symm x.1, e₂.symm x.2⟩,
  left_inv := λ ⟨x, y⟩, by simp,
  right_inv := λ ⟨x, y⟩, by simp }

/-- Combine two equivalences using `pprod` in the domain and `prod` in the codomain. -/
@[simps apply symm_apply]
def pprod_prod {α₁ β₁ : Sort*} {α₂ β₂ : Type*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
  pprod α₁ β₁ ≃ α₂ × β₂ :=
(ea.pprod_congr eb).trans pprod_equiv_prod

/-- Combine two equivalences using `pprod` in the codomain and `prod` in the domain. -/
@[simps apply symm_apply]
def prod_pprod {α₁ β₁ : Type*} {α₂ β₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) :
  α₁ × β₁ ≃ pprod α₂ β₂ :=
(ea.symm.pprod_prod eb.symm).symm

/-- `pprod α β` is equivalent to `plift α × plift β` -/
@[simps apply symm_apply]
def pprod_equiv_prod_plift {α β : Sort*} : pprod α β ≃ plift α × plift β :=
equiv.plift.symm.pprod_prod equiv.plift.symm

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. This is
`prod.map` as an equivalence. -/
@[congr, simps apply { fully_applied := ff }]
def prod_congr {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
⟨prod.map e₁ e₂, prod.map e₁.symm e₂.symm, λ ⟨a, b⟩, by simp, λ ⟨a, b⟩, by simp⟩

@[simp] theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (prod_congr e₁ e₂).symm = prod_congr e₁.symm e₂.symm :=
rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. This is `prod.swap` as an
equivalence.-/
def prod_comm (α β : Type*) : α × β ≃ β × α :=
⟨prod.swap, prod.swap, prod.swap_swap, prod.swap_swap⟩

@[simp] lemma coe_prod_comm (α β : Type*) : ⇑(prod_comm α β) = prod.swap := rfl
@[simp] lemma prod_comm_apply {α β : Type*} (x : α × β) : prod_comm α β x = x.swap := rfl

@[simp] lemma prod_comm_symm (α β) : (prod_comm α β).symm = prod_comm β α := rfl

/-- Type product is associative up to an equivalence. -/
@[simps] def prod_assoc (α β γ : Sort*) : (α × β) × γ ≃ α × (β × γ) :=
⟨λ p, (p.1.1, p.1.2, p.2), λ p, ((p.1, p.2.1), p.2.2), λ ⟨⟨a, b⟩, c⟩, rfl, λ ⟨a, ⟨b, c⟩⟩, rfl⟩

/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps {fully_applied := ff}] def curry (α β γ : Type*) :
  (α × β → γ) ≃ (α → β → γ) :=
{ to_fun := curry,
  inv_fun := uncurry,
  left_inv := uncurry_curry,
  right_inv := curry_uncurry }

section
/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps] def prod_punit (α : Type*) : α × punit.{u+1} ≃ α :=
⟨λ p, p.1, λ a, (a, punit.star), λ ⟨_, punit.star⟩, rfl, λ a, rfl⟩

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps] def punit_prod (α : Type*) : punit.{u+1} × α ≃ α :=
calc punit × α ≃ α × punit : prod_comm _ _
           ... ≃ α         : prod_punit _

/-- Any `unique` type is a right identity for type product up to equivalence. -/
def prod_unique (α β : Type*) [unique β] : α × β ≃ α :=
((equiv.refl α).prod_congr $ equiv_punit β).trans $ prod_punit α

@[simp] lemma coe_prod_unique {α β : Type*} [unique β] :
  ⇑(prod_unique α β) = prod.fst := rfl

lemma prod_unique_apply {α β : Type*} [unique β] (x : α × β) :
  prod_unique α β x = x.1 := rfl

@[simp] lemma prod_unique_symm_apply {α β : Type*} [unique β] (x : α) :
  (prod_unique α β).symm x = (x, default) := rfl

/-- Any `unique` type is a left identity for type product up to equivalence. -/
def unique_prod (α β : Type*) [unique β] : β × α ≃ α :=
((equiv_punit β).prod_congr $ equiv.refl α).trans $ punit_prod α

@[simp] lemma coe_unique_prod {α β : Type*} [unique β] :
  ⇑(unique_prod α β) = prod.snd := rfl

lemma unique_prod_apply {α β : Type*} [unique β] (x : β × α) :
  unique_prod α β x = x.2 := rfl

@[simp] lemma unique_prod_symm_apply {α β : Type*} [unique β] (x : α) :
  (unique_prod α β).symm x = (default, x) := rfl

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prod_empty (α : Type*) : α × empty ≃ empty :=
equiv_empty _

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def empty_prod (α : Type*) : empty × α ≃ empty :=
equiv_empty _

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prod_pempty (α : Type*) : α × pempty ≃ pempty :=
equiv_pempty _

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pempty_prod (α : Type*) : pempty × α ≃ pempty :=
equiv_pempty _
end

section
open sum

/-- `psum` is equivalent to `sum`. -/
def psum_equiv_sum (α β : Type*) : psum α β ≃ α ⊕ β :=
{ to_fun := λ s, psum.cases_on s inl inr,
  inv_fun := sum.elim psum.inl psum.inr,
  left_inv := λ s, by cases s; refl,
  right_inv := λ s, by cases s; refl }

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. This is `sum.map` as an equivalence. -/
@[simps apply]
def sum_congr {α₁ β₁ α₂ β₂ : Type*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ :=
⟨sum.map ea eb, sum.map ea.symm eb.symm, λ x, by simp, λ x, by simp⟩

/-- If `α ≃ α'` and `β ≃ β'`, then `psum α β ≃ psum α' β'`. -/
def psum_congr {δ : Sort z} (e₁ : α ≃ β) (e₂ : γ ≃ δ) : psum α γ ≃ psum β δ :=
{ to_fun := λ x, psum.cases_on x (psum.inl ∘ e₁) (psum.inr ∘ e₂),
  inv_fun := λ x, psum.cases_on x (psum.inl ∘ e₁.symm) (psum.inr ∘ e₂.symm),
  left_inv := by rintro (x|x); simp,
  right_inv := by rintro (x|x); simp }

/-- Combine two `equiv`s using `psum` in the domain and `sum` in the codomain. -/
def psum_sum {α₁ β₁ : Sort*} {α₂ β₂ : Type*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : psum α₁ β₁ ≃ α₂ ⊕ β₂ :=
(ea.psum_congr eb).trans (psum_equiv_sum _ _)

/-- Combine two `equiv`s using `sum` in the domain and `psum` in the codomain. -/
def sum_psum {α₁ β₁ : Type*} {α₂ β₂ : Sort*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ psum α₂ β₂ :=
(ea.symm.psum_sum eb.symm).symm

@[simp] lemma sum_congr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*}
  (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
  (equiv.sum_congr e f).trans (equiv.sum_congr g h) = (equiv.sum_congr (e.trans g) (f.trans h)) :=
by { ext i, cases i; refl }

@[simp] lemma sum_congr_symm {α β γ δ : Sort*} (e : α ≃ β) (f : γ ≃ δ) :
  (equiv.sum_congr e f).symm = (equiv.sum_congr (e.symm) (f.symm)) :=
rfl

@[simp] lemma sum_congr_refl {α β : Sort*} :
  equiv.sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) :=
by { ext i, cases i; refl }

namespace perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sum_congr {α β : Type*} (ea : equiv.perm α) (eb : equiv.perm β) : equiv.perm (α ⊕ β) :=
equiv.sum_congr ea eb

@[simp] lemma sum_congr_apply {α β : Type*} (ea : equiv.perm α) (eb : equiv.perm β) (x : α ⊕ β) :
  sum_congr ea eb x = sum.map ⇑ea ⇑eb x := equiv.sum_congr_apply ea eb x

@[simp] lemma sum_congr_trans {α β : Sort*}
  (e : equiv.perm α) (f : equiv.perm β) (g : equiv.perm α) (h : equiv.perm β) :
  (sum_congr e f).trans (sum_congr g h) = sum_congr (e.trans g) (f.trans h) :=
equiv.sum_congr_trans e f g h

@[simp] lemma sum_congr_symm {α β : Sort*} (e : equiv.perm α) (f : equiv.perm β) :
  (sum_congr e f).symm = sum_congr (e.symm) (f.symm) :=
equiv.sum_congr_symm e f

@[simp] lemma sum_congr_refl {α β : Sort*} :
  sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) :=
equiv.sum_congr_refl

end perm

/-- `bool` is equivalent the sum of two `punit`s. -/
def bool_equiv_punit_sum_punit : bool ≃ punit.{u+1} ⊕ punit.{v+1} :=
⟨λ b, cond b (inr punit.star) (inl punit.star),
 sum.elim (λ _, ff) (λ _, tt),
 λ b, by cases b; refl,
 λ s, by rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩; refl⟩

/-- Sum of types is commutative up to an equivalence. This is `sum.swap` as an equivalence. -/
@[simps apply {fully_applied := ff}]
def sum_comm (α β : Type*) : α ⊕ β ≃ β ⊕ α :=
⟨sum.swap, sum.swap, sum.swap_swap, sum.swap_swap⟩

@[simp] lemma sum_comm_symm (α β) : (sum_comm α β).symm = sum_comm β α := rfl

/-- Sum of types is associative up to an equivalence. -/
def sum_assoc (α β γ : Type*) : (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ) :=
⟨sum.elim (sum.elim sum.inl (sum.inr ∘ sum.inl)) (sum.inr ∘ sum.inr),
  sum.elim (sum.inl ∘ sum.inl) $ sum.elim (sum.inl ∘ sum.inr) sum.inr,
  by rintros (⟨_ | _⟩ | _); refl,
  by rintros (_ | ⟨_ | _⟩); refl⟩

@[simp] lemma sum_assoc_apply_inl_inl {α β γ} (a) : sum_assoc α β γ (inl (inl a)) = inl a := rfl

@[simp] lemma sum_assoc_apply_inl_inr {α β γ} (b) : sum_assoc α β γ (inl (inr b)) = inr (inl b) :=
rfl

@[simp] lemma sum_assoc_apply_inr {α β γ} (c) : sum_assoc α β γ (inr c) = inr (inr c) := rfl

@[simp] lemma sum_assoc_symm_apply_inl {α β γ} (a) : (sum_assoc α β γ).symm (inl a) = inl (inl a) :=
rfl

@[simp] lemma sum_assoc_symm_apply_inr_inl {α β γ} (b) :
  (sum_assoc α β γ).symm (inr (inl b)) = inl (inr b) := rfl

@[simp] lemma sum_assoc_symm_apply_inr_inr {α β γ} (c) :
  (sum_assoc α β γ).symm (inr (inr c)) = inr c := rfl


/-- Sum with `empty` is equivalent to the original type. -/
@[simps symm_apply] def sum_empty (α β : Type*) [is_empty β] : α ⊕ β ≃ α :=
⟨sum.elim id is_empty_elim,
 inl,
 λ s, by { rcases s with _ | x, refl, exact is_empty_elim x },
 λ a, rfl⟩

@[simp] lemma sum_empty_apply_inl {α β : Type*} [is_empty β] (a : α) :
  sum_empty α β (sum.inl a) = a := rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symm_apply] def empty_sum (α β : Type*) [is_empty α] : α ⊕ β ≃ β :=
(sum_comm _ _).trans $ sum_empty _ _

@[simp] lemma empty_sum_apply_inr {α β : Type*} [is_empty α] (b : β) :
  empty_sum α β (sum.inr b) = b := rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def option_equiv_sum_punit (α : Type*) : option α ≃ α ⊕ punit.{u+1} :=
⟨λ o, o.elim (inr punit.star) inl,
 λ s, s.elim some (λ _, none),
 λ o, by cases o; refl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl⟩

@[simp] lemma option_equiv_sum_punit_none {α} :
  option_equiv_sum_punit α none = sum.inr punit.star := rfl
@[simp] lemma option_equiv_sum_punit_some {α} (a) :
  option_equiv_sum_punit α (some a) = sum.inl a := rfl

@[simp] lemma option_equiv_sum_punit_coe {α} (a : α) :
  option_equiv_sum_punit α a = sum.inl a := rfl

@[simp] lemma option_equiv_sum_punit_symm_inl {α} (a) :
  (option_equiv_sum_punit α).symm (sum.inl a) = a :=
rfl

@[simp] lemma option_equiv_sum_punit_symm_inr {α} (a) :
  (option_equiv_sum_punit α).symm (sum.inr a) = none :=
rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps] def option_is_some_equiv (α : Type*) : {x : option α // x.is_some} ≃ α :=
{ to_fun := λ o, option.get o.2,
  inv_fun := λ x, ⟨some x, dec_trivial⟩,
  left_inv := λ o, subtype.eq $ option.some_get _,
  right_inv := λ x, option.get_some _ _ }

/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps] def pi_option_equiv_prod {α : Type*} {β : option α → Type*} :
  (Π a : option α, β a) ≃ (β none × Π a : α, β (some a)) :=
{ to_fun := λ f, (f none, λ a, f (some a)),
  inv_fun := λ x a, option.cases_on a x.fst x.snd,
  left_inv := λ f, funext $ λ a, by cases a; refl,
  right_inv := λ x, by simp }

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sum_equiv_sigma_bool (α β : Type u) : α ⊕ β ≃ (Σ b: bool, cond b α β) :=
⟨λ s, s.elim (λ x, ⟨tt, x⟩) (λ x, ⟨ff, x⟩),
 λ s, match s with ⟨tt, a⟩ := inl a | ⟨ff, b⟩ := inr b end,
 λ s, by cases s; refl,
 λ s, by rcases s with ⟨_|_, _⟩; refl⟩

/-- `sigma_fiber_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
-- See also `equiv.sigma_preimage_equiv`.
@[simps]
def sigma_fiber_equiv {α β : Type*} (f : α → β) :
  (Σ y : β, {x // f x = y}) ≃ α :=
⟨λ x, ↑x.2, λ x, ⟨f x, x, rfl⟩, λ ⟨y, x, rfl⟩, rfl, λ x, rfl⟩

end

section sum_compl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sum_compl {α : Type*} (p : α → Prop) [decidable_pred p] :
  {a // p a} ⊕ {a // ¬ p a} ≃ α :=
{ to_fun := sum.elim coe coe,
  inv_fun := λ a, if h : p a then sum.inl ⟨a, h⟩ else sum.inr ⟨a, h⟩,
  left_inv := by { rintros (⟨x,hx⟩|⟨x,hx⟩); dsimp; [rw dif_pos, rw dif_neg], },
  right_inv := λ a, by { dsimp, split_ifs; refl } }

@[simp] lemma sum_compl_apply_inl {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // p a}) :
  sum_compl p (sum.inl x) = x := rfl

@[simp] lemma sum_compl_apply_inr {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // ¬ p a}) :
  sum_compl p (sum.inr x) = x := rfl

@[simp] lemma sum_compl_apply_symm_of_pos {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : p a) :
  (sum_compl p).symm a = sum.inl ⟨a, h⟩ := dif_pos h

@[simp] lemma sum_compl_apply_symm_of_neg {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : ¬ p a) :
  (sum_compl p).symm a = sum.inr ⟨a, h⟩ := dif_neg h

/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtype_congr {α : Type*} {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) : perm α :=
(sum_compl p).symm.trans ((sum_congr e f).trans
  (sum_compl q))

open equiv

variables {ε : Type*} {p : ε → Prop} [decidable_pred p]
variables (ep ep' : perm {a // p a}) (en en' : perm {a // ¬ p a})

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def perm.subtype_congr : equiv.perm ε :=
perm_congr (sum_compl p) (sum_congr ep en)

lemma perm.subtype_congr.apply (a : ε) :
  ep.subtype_congr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ :=
by { by_cases h : p a; simp [perm.subtype_congr, h] }

@[simp] lemma perm.subtype_congr.left_apply {a : ε} (h : p a) :
  ep.subtype_congr en a = ep ⟨a, h⟩ :=
by simp [perm.subtype_congr.apply, h]

@[simp] lemma perm.subtype_congr.left_apply_subtype (a : {a // p a}) :
  ep.subtype_congr en a = ep a :=
by { convert perm.subtype_congr.left_apply _ _ a.property, simp }

@[simp] lemma perm.subtype_congr.right_apply {a : ε} (h : ¬ p a) :
  ep.subtype_congr en a = en ⟨a, h⟩ :=
by simp [perm.subtype_congr.apply, h]

@[simp] lemma perm.subtype_congr.right_apply_subtype (a : {a // ¬ p a}) :
  ep.subtype_congr en a = en a :=
by { convert perm.subtype_congr.right_apply _ _ a.property, simp }

@[simp] lemma perm.subtype_congr.refl :
  perm.subtype_congr (equiv.refl {a // p a}) (equiv.refl {a // ¬ p a}) = equiv.refl ε :=
by { ext x, by_cases h : p x; simp [h] }

@[simp] lemma perm.subtype_congr.symm :
  (ep.subtype_congr en).symm = perm.subtype_congr ep.symm en.symm :=
begin
  ext x,
  by_cases h : p x,
  { have : p (ep.symm ⟨x, h⟩) := subtype.property _,
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] },
  { have : ¬ p (en.symm ⟨x, h⟩) := subtype.property (en.symm _),
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] }
end

@[simp] lemma perm.subtype_congr.trans :
  (ep.subtype_congr en).trans (ep'.subtype_congr en') =
    perm.subtype_congr (ep.trans ep') (en.trans en') :=
begin
  ext x,
  by_cases h : p x,
  { have : p (ep ⟨x, h⟩) := subtype.property _,
    simp [perm.subtype_congr.apply, h, this] },
  { have : ¬ p (en ⟨x, h⟩) := subtype.property (en _),
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] }
end

end sum_compl

section subtype_preimage

variables (p : α → Prop) [decidable_pred p] (x₀ : {a // p a} → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtype_preimage :
  {x : α → β // x ∘ coe = x₀} ≃ ({a // ¬ p a} → β) :=
{ to_fun := λ (x : {x : α → β // x ∘ coe = x₀}) a, (x : α → β) a,
  inv_fun := λ x, ⟨λ a, if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩,
    funext $ λ ⟨a, h⟩, dif_pos h⟩,
  left_inv := λ ⟨x, hx⟩, subtype.val_injective $ funext $ λ a,
    (by { dsimp, split_ifs; [ rw ← hx, skip ]; refl }),
  right_inv := λ x, funext $ λ ⟨a, h⟩,
    show dite (p a) _ _ = _, by { dsimp, rw [dif_neg h] } }

lemma subtype_preimage_symm_apply_coe_pos (x : {a // ¬ p a} → β) (a : α) (h : p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
dif_pos h

lemma subtype_preimage_symm_apply_coe_neg (x : {a // ¬ p a} → β) (a : α) (h : ¬ p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
dif_neg h

end subtype_preimage

section

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def Pi_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Π a, β₁ a) ≃ (Π a, β₂ a) :=
⟨λ H a, F a (H a), λ H a, (F a).symm (H a),
 λ H, funext $ by simp, λ H, funext $ by simp⟩

/-- Given `φ : α → β → Sort*`, we have an equivalence between `Π a b, φ a b` and `Π b a, φ a b`.
This is `function.swap` as an `equiv`. -/
@[simps apply]
def Pi_comm {α β} (φ : α → β → Sort*) : (Π a b, φ a b) ≃ (Π b a, φ a b) :=
⟨swap, swap, λ x, rfl, λ y, rfl⟩

@[simp] lemma Pi_comm_symm {α β} {φ : α → β → Sort*} :
  (Pi_comm φ).symm = (Pi_comm $ swap φ) :=
rfl

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def Pi_curry {α} {β : α → Sort*} (γ : Π a, β a → Sort*) :
  (Π x : Σ i, β i, γ x.1 x.2) ≃ (Π a b, γ a b) :=
{ to_fun := sigma.curry,
  inv_fun := sigma.uncurry,
  left_inv := sigma.uncurry_curry,
  right_inv := sigma.curry_uncurry }

end

section prod_congr

variables {α₁ β₁ β₂ : Type*} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prod_congr_left : β₁ × α₁ ≃ β₂ × α₁ :=
{ to_fun := λ ab, ⟨e ab.2 ab.1, ab.2⟩,
  inv_fun := λ ab, ⟨(e ab.2).symm ab.1, ab.2⟩,
  left_inv := by { rintros ⟨a, b⟩, simp },
  right_inv := by { rintros ⟨a, b⟩, simp } }

@[simp] lemma prod_congr_left_apply (b : β₁) (a : α₁) :
prod_congr_left e (b, a) = (e a b, a) := rfl

lemma prod_congr_refl_right (e : β₁ ≃ β₂) :
  prod_congr e (equiv.refl α₁) = prod_congr_left (λ _, e) :=
by { ext ⟨a, b⟩ : 1, simp }

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prod_congr_right : α₁ × β₁ ≃ α₁ × β₂ :=
{ to_fun := λ ab, ⟨ab.1, e ab.1 ab.2⟩,
  inv_fun := λ ab, ⟨ab.1, (e ab.1).symm ab.2⟩,
  left_inv := by { rintros ⟨a, b⟩, simp },
  right_inv := by { rintros ⟨a, b⟩, simp } }

@[simp] lemma prod_congr_right_apply (a : α₁) (b : β₁) :
  prod_congr_right e (a, b) = (a, e a b) := rfl

lemma prod_congr_refl_left (e : β₁ ≃ β₂) :
  prod_congr (equiv.refl α₁) e = prod_congr_right (λ _, e) :=
by { ext ⟨a, b⟩ : 1, simp }

@[simp] lemma prod_congr_left_trans_prod_comm :
  (prod_congr_left e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_right e) :=
by { ext ⟨a, b⟩ : 1, simp }

@[simp] lemma prod_congr_right_trans_prod_comm :
  (prod_congr_right e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_left e) :=
by { ext ⟨a, b⟩ : 1, simp }

lemma sigma_congr_right_sigma_equiv_prod :
  (sigma_congr_right e).trans (sigma_equiv_prod α₁ β₂) =
    (sigma_equiv_prod α₁ β₁).trans (prod_congr_right e) :=
by { ext ⟨a, b⟩ : 1, simp }

lemma sigma_equiv_prod_sigma_congr_right :
  (sigma_equiv_prod α₁ β₁).symm.trans (sigma_congr_right e) =
    (prod_congr_right e).trans (sigma_equiv_prod α₁ β₂).symm :=
by { ext ⟨a, b⟩ : 1, simp }

/-- A family of equivalences between fibers gives an equivalence between domains. -/
-- See also `equiv.of_preimage_equiv`.
@[simps]
def of_fiber_equiv {α β γ : Type*} {f : α → γ} {g : β → γ}
  (e : Π c, {a // f a = c} ≃ {b // g b = c}) :
  α ≃ β :=
(sigma_fiber_equiv f).symm.trans $ (equiv.sigma_congr_right e).trans (sigma_fiber_equiv g)

lemma of_fiber_equiv_map {α β γ} {f : α → γ} {g : β → γ}
  (e : Π c, {a // f a = c} ≃ {b // g b = c}) (a : α) : g (of_fiber_equiv e a) = f a :=
(_ : {b // g b = _}).prop

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps {fully_applied := ff}]
def prod_shear {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
{ to_fun := λ x : α₁ × β₁, (e₁ x.1, e₂ x.1 x.2),
  inv_fun := λ y : α₂ × β₂, (e₁.symm y.1, (e₂ $ e₁.symm y.1).symm y.2),
  left_inv := by { rintro ⟨x₁, y₁⟩, simp only [symm_apply_apply] },
  right_inv := by { rintro ⟨x₁, y₁⟩, simp only [apply_symm_apply] } }

end prod_congr

namespace perm

variables {α₁ β₁ β₂ : Type*} [decidable_eq α₁] (a : α₁) (e : perm β₁)

/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prod_extend_right : perm (α₁ × β₁) :=
{ to_fun := λ ab, if ab.fst = a then (a, e ab.snd) else ab,
  inv_fun := λ ab, if ab.fst = a then (a, e.symm ab.snd) else ab,
  left_inv := by { rintros ⟨k', x⟩, dsimp only, split_ifs with h; simp [h] },
  right_inv := by { rintros ⟨k', x⟩, dsimp only, split_ifs with h; simp [h] } }

@[simp] lemma prod_extend_right_apply_eq (b : β₁) :
  prod_extend_right a e (a, b) = (a, e b) := if_pos rfl

lemma prod_extend_right_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) :
  prod_extend_right a e (a', b) = (a', b) := if_neg h

lemma eq_of_prod_extend_right_ne {e : perm β₁} {a a' : α₁} {b : β₁}
  (h : prod_extend_right a e (a', b) ≠ (a', b)) : a' = a :=
by { contrapose! h, exact prod_extend_right_apply_ne _ h _ }

@[simp] lemma fst_prod_extend_right (ab : α₁ × β₁) :
  (prod_extend_right a e ab).fst = ab.fst :=
begin
  rw [prod_extend_right, coe_fn_mk],
  split_ifs with h,
  { rw h },
  { refl }
end

end perm

section
/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrow_prod_equiv_prod_arrow (α β γ : Type*) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
⟨λ f, (λ c, (f c).1, λ c, (f c).2),
 λ p c, (p.1 c, p.2 c),
 λ f, funext $ λ c, prod.mk.eta,
 λ p, by { cases p, refl }⟩

open sum
/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ (α → γ) × (β → γ) :=
⟨λ f, (f ∘ inl, f ∘ inr),
 λ p, sum.elim p.1 p.2,
 λ f, by { ext ⟨⟩; refl },
 λ p, by { cases p, refl }⟩

@[simp] lemma sum_arrow_equiv_prod_arrow_apply_fst {α β γ} (f : (α ⊕ β) → γ) (a : α) :
  (sum_arrow_equiv_prod_arrow α β γ f).1 a = f (inl a) := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_apply_snd {α β γ} (f : (α ⊕ β) → γ) (b : β) :
  (sum_arrow_equiv_prod_arrow α β γ f).2 b = f (inr b) := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inl a) = f a := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inr b) = g b := rfl

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sum_prod_distrib (α β γ : Sort*) : (α ⊕ β) × γ ≃ (α × γ) ⊕ (β × γ) :=
⟨λ p, p.1.map (λ x, (x, p.2)) (λ x, (x, p.2)),
 λ s, s.elim (prod.map inl id) (prod.map inr id),
 by rintro ⟨_ | _, _⟩; refl,
 by rintro (⟨_, _⟩ | ⟨_, _⟩); refl⟩

@[simp] theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) :
   sum_prod_distrib α β γ (sum.inl a, c) = sum.inl (a, c) := rfl
@[simp] theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) :
   sum_prod_distrib α β γ (sum.inr b, c) = sum.inr (b, c) := rfl
@[simp] theorem sum_prod_distrib_symm_apply_left {α β γ} (a : α × γ) :
  (sum_prod_distrib α β γ).symm (inl a) = (inl a.1, a.2) := rfl
@[simp] theorem sum_prod_distrib_symm_apply_right {α β γ} (b : β × γ) :
  (sum_prod_distrib α β γ).symm (inr b) = (inr b.1, b.2) := rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prod_sum_distrib (α β γ : Sort*) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ) :=
calc α × (β ⊕ γ) ≃ (β ⊕ γ) × α       : prod_comm _ _
            ...   ≃ (β × α) ⊕ (γ × α) : sum_prod_distrib _ _ _
            ...   ≃ (α × β) ⊕ (α × γ) : sum_congr (prod_comm _ _) (prod_comm _ _)

@[simp] theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) :
   prod_sum_distrib α β γ (a, sum.inl b) = sum.inl (a, b) := rfl
@[simp] theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) :
   prod_sum_distrib α β γ (a, sum.inr c) = sum.inr (a, c) := rfl
@[simp] theorem prod_sum_distrib_symm_apply_left {α β γ} (a : α × β) :
  (prod_sum_distrib α β γ).symm (inl a) = (a.1, inl a.2) := rfl
@[simp] theorem prod_sum_distrib_symm_apply_right {α β γ} (a : α × γ) :
  (prod_sum_distrib α β γ).symm (inr a) = (a.1, inr a.2) := rfl

/-- An indexed sum of disjoint sums of types is equivalent to the sum of the indexed sums. -/
@[simps] def sigma_sum_distrib {ι : Type*} (α β : ι → Type*) :
  (Σ i, α i ⊕ β i) ≃ (Σ i, α i) ⊕ Σ i, β i :=
⟨λ p, p.2.map (sigma.mk p.1) (sigma.mk p.1),
  sum.elim (sigma.map id (λ _, sum.inl)) (sigma.map id (λ _, sum.inr)),
  λ p, by { rcases p with ⟨i, (a | b)⟩; refl },
  λ p, by { rcases p with (⟨i, a⟩ | ⟨i, b⟩); refl }⟩

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigma_prod_distrib {ι : Type*} (α : ι → Type*) (β : Type*) :
  ((Σ i, α i) × β) ≃ (Σ i, (α i × β)) :=
⟨λ p, ⟨p.1.1, (p.1.2, p.2)⟩,
 λ p, (⟨p.1, p.2.1⟩, p.2.2),
 λ p, by { rcases p with ⟨⟨_, _⟩, _⟩, refl },
 λ p, by { rcases p with ⟨_, ⟨_, _⟩⟩, refl }⟩

/-- An equivalence that separates out the 0th fiber of `(Σ (n : ℕ), f n)`. -/
def sigma_nat_succ (f : ℕ → Type u) :
  (Σ n, f n) ≃ f 0 ⊕ Σ n, f (n + 1) :=
⟨λ x, @sigma.cases_on ℕ f (λ _, f 0 ⊕ Σ n, f (n + 1)) x (λ n, @nat.cases_on (λ i, f i → (f 0 ⊕
  Σ (n : ℕ), f (n + 1))) n (λ (x : f 0), sum.inl x) (λ (n : ℕ) (x : f n.succ), sum.inr ⟨n, x⟩)),
  sum.elim (sigma.mk 0) (sigma.map nat.succ (λ _, id)),
  by { rintro ⟨(n | n), x⟩; refl }, by { rintro (x | ⟨n, x⟩); refl }⟩

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
@[simps] def bool_prod_equiv_sum (α : Type u) : bool × α ≃ α ⊕ α :=
{ to_fun := λ p, cond p.1 (inr p.2) (inl p.2),
  inv_fun := sum.elim (prod.mk ff) (prod.mk tt),
  left_inv := by rintro ⟨(_|_), _⟩; refl,
  right_inv := by rintro (_|_); refl }

/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps] def bool_arrow_equiv_prod (α : Type u) : (bool → α) ≃ α × α :=
{ to_fun := λ f, (f tt, f ff),
  inv_fun := λ p b, cond b p.1 p.2,
  left_inv := λ f, funext $ bool.forall_bool.2 ⟨rfl, rfl⟩,
  right_inv := λ ⟨x, y⟩, rfl }

end

section
open sum nat
/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def nat_equiv_nat_sum_punit : ℕ ≃ ℕ ⊕ punit.{u+1} :=
{ to_fun := λ n, nat.cases_on n (inr punit.star) inl,
  inv_fun := sum.elim nat.succ (λ _, 0),
  left_inv := λ n, by cases n; refl,
  right_inv := by rintro (_|_|_); refl }

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def nat_sum_punit_equiv_nat : ℕ ⊕ punit.{u+1} ≃ ℕ :=
nat_equiv_nat_sum_punit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def int_equiv_nat_sum_nat : ℤ ≃ ℕ ⊕ ℕ :=
{ to_fun := λ z, int.cases_on z inl inr,
  inv_fun := sum.elim coe int.neg_succ_of_nat,
  left_inv := by rintro (m|n); refl,
  right_inv := by rintro (m|n); refl }

end

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def list_equiv_of_equiv {α β : Type*} (e : α ≃ β) : list α ≃ list β :=
{ to_fun := list.map e,
  inv_fun := list.map e.symm,
  left_inv := λ l, by rw [list.map_map, e.symm_comp_self, list.map_id],
  right_inv := λ l, by rw [list.map_map, e.self_comp_symm, list.map_id] }

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def unique_congr (e : α ≃ β) : unique α ≃ unique β :=
{ to_fun := λ h, @equiv.unique _ _ h e.symm,
  inv_fun := λ h, @equiv.unique _ _ h e,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
lemma is_empty_congr (e : α ≃ β) : is_empty α ↔ is_empty β :=
⟨λ h, @function.is_empty _ _ h e.symm, λ h, @function.is_empty _ _ h e⟩

protected lemma is_empty (e : α ≃ β) [is_empty β] : is_empty α :=
e.is_empty_congr.mpr ‹_›

section
open subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtype_equiv {p : α → Prop} {q : β → Prop}
  (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) : {a : α // p a} ≃ {b : β // q b} :=
{ to_fun    := λ a, ⟨e a, (h _).mp a.prop⟩,
  inv_fun   := λ b, ⟨e.symm b, (h _).mpr ((e.apply_symm_apply b).symm ▸ b.prop)⟩,
  left_inv  := λ a, subtype.ext $ by simp,
  right_inv := λ b, subtype.ext $ by simp }

@[simp] lemma subtype_equiv_refl {p : α → Prop}
  (h : ∀ a, p a ↔ p (equiv.refl _ a) := λ a, iff.rfl) :
  (equiv.refl α).subtype_equiv h = equiv.refl {a : α // p a} :=
by { ext, refl }

@[simp] lemma subtype_equiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β)
  (h : ∀ (a : α), p a ↔ q (e a)) :
  (e.subtype_equiv h).symm = e.symm.subtype_equiv (λ a, by
  { convert (h $ e.symm a).symm,
    exact (e.apply_symm_apply a).symm }) :=
rfl

@[simp] lemma subtype_equiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (e : α ≃ β) (f : β ≃ γ)
  (h : ∀ (a : α), p a ↔ q (e a)) (h' : ∀ (b : β), q b ↔ r (f b)):
  (e.subtype_equiv h).trans (f.subtype_equiv h') =
    (e.trans f).subtype_equiv (λ a, (h a).trans (h' $ e a)) :=
rfl

@[simp] lemma subtype_equiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β)
  (h : ∀ (a : α), p a ↔ q (e a)) (x : {x // p x}) :
  e.subtype_equiv h x = ⟨e x, (h _).1 x.2⟩ :=
rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtype_equiv_right {p q : α → Prop} (e : ∀x, p x ↔ q x) : {x // p x} ≃ {x // q x} :=
subtype_equiv (equiv.refl _) e

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtype_equiv_of_subtype {p : β → Prop} (e : α ≃ β) :
  {a : α // p (e a)} ≃ {b : β // p b} :=
subtype_equiv e $ by simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtype_equiv_of_subtype' {p : α → Prop} (e : α ≃ β) :
  {a : α // p a} ≃ {b : β // p (e.symm b)} :=
e.symm.subtype_equiv_of_subtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtype_equiv_prop {α : Sort*} {p q : α → Prop} (h : p = q) : subtype p ≃ subtype q :=
subtype_equiv (equiv.refl α) (assume a, h ▸ iff.rfl)

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
@[simps]
def subtype_subtype_equiv_subtype_exists {α : Sort u} (p : α → Prop) (q : subtype p → Prop) :
  subtype q ≃ {a : α // ∃h:p a, q ⟨a, h⟩ } :=
⟨λ a, ⟨a, a.1.2, by { rcases a with ⟨⟨a, hap⟩, haq⟩, exact haq }⟩,
  λ a, ⟨⟨a, a.2.fst⟩, a.2.snd⟩,
  assume ⟨⟨a, ha⟩, h⟩, rfl, assume ⟨a, h₁, h₂⟩, rfl⟩

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
@[simps] def subtype_subtype_equiv_subtype_inter {α : Sort u} (p q : α → Prop) :
  {x : subtype p // q x.1} ≃ subtype (λ x, p x ∧ q x) :=
(subtype_subtype_equiv_subtype_exists p _).trans $
subtype_equiv_right $ λ x, exists_prop

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
@[simps] def subtype_subtype_equiv_subtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
  {x : subtype p // q x.1} ≃ subtype q :=
(subtype_subtype_equiv_subtype_inter p _).trans $
subtype_equiv_right $ λ x, and_iff_right_of_imp h

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
def subtype_univ_equiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) :
  subtype p ≃ α :=
⟨λ x, x, λ x, ⟨x, h x⟩, λ x, subtype.eq rfl, λ x, rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtype_sigma_equiv {α : Type u} (p : α → Type v) (q : α → Prop) :
  { y : sigma p // q y.1 } ≃ Σ(x : subtype q), p x.1 :=
⟨λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ ⟨⟨x, h⟩, y⟩, rfl,
 λ ⟨⟨x, y⟩, h⟩, rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigma_subtype_equiv_of_subset {α : Type u} (p : α → Type v) (q : α → Prop)
  (h : ∀ x, p x → q x) :
  (Σ x : subtype q, p x) ≃ Σ x : α, p x :=
(subtype_sigma_equiv p q).symm.trans $ subtype_univ_equiv $ λ x, h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigma_subtype_fiber_equiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (h : ∀ x, p (f x)) :
  (Σ y : subtype p, {x : α // f x = y}) ≃ α :=
calc _ ≃ Σ y : β, {x : α // f x = y} : sigma_subtype_equiv_of_subset _ p (λ y ⟨x, h'⟩, h' ▸ h x)
   ... ≃ α                           : sigma_fiber_equiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigma_subtype_fiber_equiv_subtype {α : Type u} {β : Type v} (f : α → β)
  {p : α → Prop} {q : β → Prop} (h : ∀ x, p x ↔ q (f x)) :
  (Σ y : subtype q, {x : α // f x = y}) ≃ subtype p :=
calc (Σ y : subtype q, {x : α // f x = y}) ≃
  Σ y : subtype q, {x : subtype p // subtype.mk (f x) ((h x).1 x.2) = y} :
  begin
    apply sigma_congr_right,
    assume y,
    symmetry,
    refine (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _),
    assume x,
    exact ⟨λ ⟨hp, h'⟩, congr_arg subtype.val h', λ h', ⟨(h x).2 (h'.symm ▸ y.2), subtype.eq h'⟩⟩
  end
   ... ≃ subtype p : sigma_fiber_equiv (λ x : subtype p, (⟨f x, (h x).1 x.property⟩ : subtype q))

/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigma_option_equiv_of_some {α : Type u} (p : option α → Type v) (h : p none → false) :
  (Σ x : option α, p x) ≃ (Σ x : α, p (some x)) :=
begin
  have h' : ∀ x, p x → x.is_some,
  { intro x,
    cases x,
    { intro n, exfalso, exact h n },
    { intro s, exact rfl } },
  exact (sigma_subtype_equiv_of_subset _ _ h').symm.trans
    (sigma_congr_left' (option_is_some_equiv α)),
end

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def pi_equiv_subtype_sigma (ι : Type*) (π : ι → Type*) :
  (Π i, π i) ≃ {f : ι → Σ i, π i // ∀ i, (f i).1 = i } :=
⟨ λf, ⟨λi, ⟨i, f i⟩, assume i, rfl⟩, λf i, begin rw ← f.2 i, exact (f.1 i).2 end,
  assume f, funext $ assume i, rfl,
  assume ⟨f, hf⟩, subtype.eq $ funext $ assume i, sigma.eq (hf i).symm $
    eq_of_heq $ rec_heq_of_heq _ $ rec_heq_of_heq _ $ heq.refl _⟩

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtype_pi_equiv_pi {α : Sort u} {β : α → Sort v} {p : Πa, β a → Prop} :
  {f : Πa, β a // ∀a, p a (f a) } ≃ Πa, { b : β a // p a b } :=
⟨λf a, ⟨f.1 a, f.2 a⟩, λf, ⟨λa, (f a).1, λa, (f a).2⟩,
  by { rintro ⟨f, h⟩, refl },
  by { rintro f, funext a, exact subtype.ext_val rfl }⟩

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtype_prod_equiv_prod {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
  {c : α × β // p c.1 ∧ q c.2} ≃ ({a // p a} × {b // q b}) :=
⟨λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl⟩

/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtype_prod_equiv_sigma_subtype {α β : Type*} (p : α → β → Prop) :
  {x : α × β // p x.1 x.2} ≃ Σ a, {b : β // p a b} :=
{ to_fun := λ x, ⟨x.1.1, x.1.2, x.prop⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2⟩, x.2.prop⟩,
  left_inv := λ x, by ext; refl,
  right_inv := λ ⟨a, b, pab⟩, rfl }

/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps] def pi_equiv_pi_subtype_prod
  {α : Type*} (p : α → Prop) (β : α → Type*) [decidable_pred p] :
  (Π (i : α), β i) ≃ (Π (i : {x // p x}), β i) × (Π (i : {x // ¬ p x}), β i) :=
{ to_fun := λ f, (λ x, f x, λ x, f x),
  inv_fun := λ f x, if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩,
  right_inv := begin
    rintros ⟨f, g⟩,
    ext1;
    { ext y,
      rcases y,
      simp only [y_property, dif_pos, dif_neg, not_false_iff, subtype.coe_mk],
      refl },
  end,
  left_inv := λ f, begin
    ext x,
    by_cases h : p x;
    { simp only [h, dif_neg, dif_pos, not_false_iff],
      refl },
  end }

/-- A product of types can be split as the binary product of one of the types and the product
  of all the remaining types. -/
@[simps] def pi_split_at {α : Type*} [decidable_eq α] (i : α) (β : α → Type*) :
  (Π j, β j) ≃ β i × Π j : {j // j ≠ i}, β j :=
{ to_fun := λ f, ⟨f i, λ j, f j⟩,
  inv_fun := λ f j, if h : j = i then h.symm.rec f.1 else f.2 ⟨j, h⟩,
  right_inv := λ f, by { ext, exacts [dif_pos rfl, (dif_neg x.2).trans (by cases x; refl)] },
  left_inv := λ f, by { ext, dsimp only, split_ifs, { subst h }, { refl } } }

/-- A product of copies of a type can be split as the binary product of one copy and the product
  of all the remaining copies. -/
@[simps] def fun_split_at {α : Type*} [decidable_eq α] (i : α) (β : Type*) :
  (α → β) ≃ β × ({j // j ≠ i} → β) := pi_split_at i _

end

section subtype_equiv_codomain
variables {X : Type*} {Y : Type*} [decidable_eq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) : {g : X → Y // g ∘ coe = f} ≃ Y :=
(subtype_preimage _ f).trans $
@fun_unique {x' // ¬ x' ≠ x} _ $
show unique {x' // ¬ x' ≠ x}, from @equiv.unique _ _
  (show unique {x' // x' = x}, from
    { default := ⟨x, rfl⟩, uniq := λ ⟨x', h⟩, subtype.val_injective h })
  (subtype_equiv_right $ λ a, not_not)

@[simp] lemma coe_subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) :
  (subtype_equiv_codomain f : {g : X → Y // g ∘ coe = f} → Y) = λ g, (g : X → Y) x := rfl

@[simp] lemma subtype_equiv_codomain_apply (f : {x' // x' ≠ x} → Y)
  (g : {g : X → Y // g ∘ coe = f}) :
  subtype_equiv_codomain f g = (g : X → Y) x := rfl

lemma coe_subtype_equiv_codomain_symm (f : {x' // x' ≠ x} → Y) :
  ((subtype_equiv_codomain f).symm : Y → {g : X → Y // g ∘ coe = f}) =
  λ y, ⟨λ x', if h : x' ≠ x then f ⟨x', h⟩ else y,
    by { funext x', dsimp, erw [dif_pos x'.2, subtype.coe_eta] }⟩ := rfl

@[simp] lemma subtype_equiv_codomain_symm_apply (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
rfl

@[simp] lemma subtype_equiv_codomain_symm_apply_eq (f : {x' // x' ≠ x} → Y) (y : Y) :
  ((subtype_equiv_codomain f).symm y : X → Y) x = y :=
dif_neg (not_not.mpr rfl)

lemma subtype_equiv_codomain_symm_apply_ne (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) (h : x' ≠ x) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
dif_pos h

end subtype_equiv_codomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def of_bijective (f : α → β) (hf : bijective f) : α ≃ β :=
{ to_fun := f,
  inv_fun := function.surj_inv hf.surjective,
  left_inv := function.left_inverse_surj_inv hf,
  right_inv := function.right_inverse_surj_inv _}

lemma of_bijective_apply_symm_apply (f : α → β) (hf : bijective f) (x : β) :
  f ((of_bijective f hf).symm x) = x :=
(of_bijective f hf).apply_symm_apply x

@[simp] lemma of_bijective_symm_apply_apply (f : α → β) (hf : bijective f) (x : α) :
  (of_bijective f hf).symm (f x) = x :=
(of_bijective f hf).symm_apply_apply x

instance : can_lift (α → β) (α ≃ β) coe_fn bijective :=
{ prf := λ f hf, ⟨of_bijective f hf, rfl⟩ }

section

variables {α' β' : Type*} (e : perm α') {p : β' → Prop} [decidable_pred p]
  (f : α' ≃ subtype p)

/--
Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def perm.extend_domain : perm β' :=
(perm_congr f e).subtype_congr (equiv.refl _)

@[simp] lemma perm.extend_domain_apply_image (a : α') :
  e.extend_domain f (f a) = f (e a) :=
by simp [perm.extend_domain]

lemma perm.extend_domain_apply_subtype {b : β'} (h : p b) :
  e.extend_domain f b = f (e (f.symm ⟨b, h⟩)) :=
by simp [perm.extend_domain, h]

lemma perm.extend_domain_apply_not_subtype {b : β'} (h : ¬ p b) :
  e.extend_domain f b = b :=
by simp [perm.extend_domain, h]

@[simp] lemma perm.extend_domain_refl : perm.extend_domain (equiv.refl _) f = equiv.refl _ :=
by simp [perm.extend_domain]

@[simp] lemma perm.extend_domain_symm :
  (e.extend_domain f).symm = perm.extend_domain e.symm f := rfl

lemma perm.extend_domain_trans (e e' : perm α') :
  (e.extend_domain f).trans (e'.extend_domain f) = perm.extend_domain (e.trans e') f :=
by simp [perm.extend_domain, perm_congr_trans]

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtype_quotient_equiv_quotient_subtype (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) :
  {x // p₂ x} ≃ quotient s₂ :=
{ to_fun := λ a, quotient.hrec_on a.1 (λ a h, ⟦⟨a, (hp₂ _).2 h⟩⟧)
    (λ a b hab, hfunext (by rw quotient.sound hab)
    (λ h₁ h₂ _, heq_of_eq (quotient.sound ((h _ _).2 hab)))) a.2,
  inv_fun := λ a, quotient.lift_on a (λ a, (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : {x // p₂ x}))
    (λ a b hab, subtype.ext_val (quotient.sound ((h _ _).1 hab))),
  left_inv := λ ⟨a, ha⟩, quotient.induction_on a (λ a ha, rfl) ha,
  right_inv := λ a, quotient.induction_on a (λ ⟨a, ha⟩, rfl) }

@[simp] lemma subtype_quotient_equiv_quotient_subtype_mk (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x hx) :
  subtype_quotient_equiv_quotient_subtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ := rfl

@[simp] lemma subtype_quotient_equiv_quotient_subtype_symm_mk (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x) :
  (subtype_quotient_equiv_quotient_subtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.prop⟩ := rfl

section swap
variable [decidable_eq α]

/-- A helper function for `equiv.swap`. -/
def swap_core (a b r : α) : α :=
if r = a then b
else if r = b then a
else r

theorem swap_core_self (r a : α) : swap_core a a r = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
by { unfold swap_core, split_ifs; cc }

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : perm α :=
⟨swap_core a b, swap_core a b, λr, swap_core_swap_core r a b, λr, swap_core_swap_core r a b⟩

@[simp] theorem swap_self (a : α) : swap a a = equiv.refl _ :=
ext $ λ r, swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
ext $ λ r, swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
rfl

@[simp] theorem swap_apply_left (a b : α) : swap a b a = b :=
if_pos rfl

@[simp] theorem swap_apply_right (a b : α) : swap a b b = a :=
by { by_cases h : b = a; simp [swap_apply_def, h], }

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x :=
by simp [swap_apply_def] {contextual := tt}

@[simp] theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = equiv.refl _ :=
ext $ λ x, swap_core_swap_core _ _ _

@[simp] lemma symm_swap (a b : α) : (swap a b).symm = swap a b := rfl

@[simp] lemma swap_eq_refl_iff {x y : α} : swap x y = equiv.refl _ ↔ x = y :=
begin
  refine ⟨λ h, (equiv.refl _).injective _, λ h, h ▸ (swap_self _)⟩,
  rw [←h, swap_apply_left, h, refl_apply]
end

theorem swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
by { cases π, refl }

lemma swap_eq_update (i j : α) :
  (equiv.swap i j : α → α) = update (update id j i) i j :=
funext $ λ x, by rw [update_apply _ i j, update_apply _ j i, equiv.swap_apply_def, id.def]

lemma comp_swap_eq_update (i j : α) (f : α → β) :
  f ∘ equiv.swap i j = update (update f j (f i)) i (f j) :=
by rw [swap_eq_update, comp_update, comp_update, comp.right_id]

@[simp] lemma symm_trans_swap_trans [decidable_eq β] (a b : α) (e : α ≃ β) :
  (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
equiv.ext (λ x, begin
  have : ∀ a, e.symm x = a ↔ x = e a :=
    λ a, by { rw @eq_comm _ (e.symm x), split; intros; simp * at * },
  simp [swap_apply_def, this],
  split_ifs; simp
end)

@[simp] lemma trans_swap_trans_symm [decidable_eq β] (a b : β)
  (e : α ≃ β) : (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
symm_trans_swap_trans a b e.symm

@[simp] lemma swap_apply_self (i j a : α) :
  swap i j (swap i j a) = a :=
by rw [← equiv.trans_apply, equiv.swap_swap, equiv.refl_apply]

/-- A function is invariant to a swap if it is equal at both elements -/
lemma apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k :=
begin
  by_cases hi : k = i, { rw [hi, swap_apply_left, hv] },
  by_cases hj : k = j, { rw [hj, swap_apply_right, hv] },
  rw swap_apply_of_ne_of_ne hi hj,
end

lemma swap_apply_eq_iff {x y z w : α} :
  swap x y z = w ↔ z = swap x y w :=
by rw [apply_eq_iff_eq_symm_apply, symm_swap]

lemma swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) :=
begin
  by_cases hab : a = b,
  { simp [hab] },
  by_cases hax : x = a,
  { simp [hax, eq_comm] },
  by_cases hbx : x = b,
  { simp [hbx] },
  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]
end

namespace perm

@[simp] lemma sum_congr_swap_refl {α β : Sort*} [decidable_eq α] [decidable_eq β] (i j : α) :
  equiv.perm.sum_congr (equiv.swap i j) (equiv.refl β) = equiv.swap (sum.inl i) (sum.inl j) :=
begin
  ext x,
  cases x,
  { simp [sum.map, swap_apply_def],
    split_ifs; refl},
  { simp [sum.map, swap_apply_of_ne_of_ne] },
end

@[simp] lemma sum_congr_refl_swap {α β : Sort*} [decidable_eq α] [decidable_eq β] (i j : β) :
  equiv.perm.sum_congr (equiv.refl α) (equiv.swap i j) = equiv.swap (sum.inr i) (sum.inr j) :=
begin
  ext x,
  cases x,
  { simp [sum.map, swap_apply_of_ne_of_ne] },
  { simp [sum.map, swap_apply_def],
    split_ifs; refl},
end

end perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def set_value (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
(swap a (f.symm b)).trans f

@[simp] theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : set_value f a b a = b :=
by { dsimp [set_value], simp [swap_apply_left] }

end swap

end equiv

namespace function.involutive

/-- Convert an involutive function `f` to a permutation with `to_fun = inv_fun = f`. -/
def to_perm (f : α → α) (h : involutive f) : equiv.perm α :=
⟨f, f, h.left_inverse, h.right_inverse⟩

@[simp] lemma coe_to_perm {f : α → α} (h : involutive f) : (h.to_perm f : α → α) = f := rfl

@[simp] lemma to_perm_symm {f : α → α} (h : involutive f) : (h.to_perm f).symm = h.to_perm f := rfl

lemma to_perm_involutive {f : α → α} (h : involutive f) : involutive (h.to_perm f) := h

end function.involutive

lemma plift.eq_up_iff_down_eq {x : plift α} {y : α} : x = plift.up y ↔ x.down = y :=
equiv.plift.eq_symm_apply

lemma function.injective.map_swap {α β : Sort*} [decidable_eq α] [decidable_eq β]
  {f : α → β} (hf : function.injective f) (x y z : α) :
  f (equiv.swap x y z) = equiv.swap (f x) (f y) (f z) :=
begin
  conv_rhs { rw equiv.swap_apply_def },
  split_ifs with h₁ h₂,
  { rw [hf h₁, equiv.swap_apply_left] },
  { rw [hf h₂, equiv.swap_apply_right] },
  { rw [equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)] }
end

namespace equiv

section
variables (P : α → Sort w) (e : α ≃ β)

/--
Transport dependent functions through an equivalence of the base space.
-/
@[simps] def Pi_congr_left' : (Π a, P a) ≃ (Π b, P (e.symm b)) :=
{ to_fun := λ f x, f (e.symm x),
  inv_fun := λ f x, begin rw [← e.symm_apply_apply x], exact f (e x)  end,
  left_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { dsimp, rw e.symm_apply_apply })),
  right_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { rw e.apply_symm_apply })) }

end

section
variables (P : β → Sort w) (e : α ≃ β)

/--
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def Pi_congr_left : (Π a, P (e a)) ≃ (Π b, P b) :=
(Pi_congr_left' P e.symm).symm
end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π a : α, (W a ≃ Z (h₁ a)))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def Pi_congr : (Π a, W a) ≃ (Π b, Z b) :=
(equiv.Pi_congr_right h₂).trans (equiv.Pi_congr_left _ h₁)

@[simp] lemma coe_Pi_congr_symm :
  ((h₁.Pi_congr h₂).symm : (Π b, Z b) → (Π a, W a)) = λ f a, (h₂ a).symm (f (h₁ a)) :=
rfl

lemma Pi_congr_symm_apply (f : Π b, Z b) :
  (h₁.Pi_congr h₂).symm f = λ a, (h₂ a).symm (f (h₁ a)) :=
rfl

@[simp] lemma Pi_congr_apply_apply (f : Π a, W a) (a : α) :
  h₁.Pi_congr h₂ f (h₁ a) = h₂ a (f a) :=
begin
  change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a),
  generalize_proofs hZa,
  revert hZa,
  rw h₁.symm_apply_apply a,
  simp,
end

end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π b : β, (W (h₁.symm b) ≃ Z b))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def Pi_congr' : (Π a, W a) ≃ (Π b, Z b) :=
(Pi_congr h₁.symm (λ b, (h₂ b).symm)).symm

@[simp] lemma coe_Pi_congr' :
  (h₁.Pi_congr' h₂ : (Π a, W a) → (Π b, Z b)) = λ f b, h₂ b $ f $ h₁.symm b :=
rfl

lemma Pi_congr'_apply (f : Π a, W a) :
  h₁.Pi_congr' h₂ f = λ b, h₂ b $ f $ h₁.symm b :=
rfl

@[simp] lemma Pi_congr'_symm_apply_symm_apply (f : Π b, Z b) (b : β) :
  (h₁.Pi_congr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) :=
begin
  change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b),
  generalize_proofs hWb,
  revert hWb,
  generalize hb : h₁ (h₁.symm b) = b',
  rw h₁.apply_symm_apply b at hb,
  subst hb,
  simp,
end

end

section binary_op

variables {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

lemma semiconj_conj (f : α₁ → α₁) : semiconj e f (e.conj f) := λ x, by simp

lemma semiconj₂_conj : semiconj₂ e f (e.arrow_congr e.conj f) := λ x y, by simp

instance [is_associative α₁ f] :
  is_associative β₁ (e.arrow_congr (e.arrow_congr e) f) :=
(e.semiconj₂_conj f).is_associative_right e.surjective

instance [is_idempotent α₁ f] :
  is_idempotent β₁ (e.arrow_congr (e.arrow_congr e) f) :=
(e.semiconj₂_conj f).is_idempotent_right e.surjective

instance [is_left_cancel α₁ f] :
  is_left_cancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
⟨e.surjective.forall₃.2 $ λ x y z, by simpa using @is_left_cancel.left_cancel _ f _ x y z⟩

instance [is_right_cancel α₁ f] :
  is_right_cancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
⟨e.surjective.forall₃.2 $ λ x y z, by simpa using @is_right_cancel.right_cancel _ f _ x y z⟩

end binary_op

end equiv

lemma function.injective.swap_apply [decidable_eq α] [decidable_eq β] {f : α → β}
  (hf : function.injective f) (x y z : α) :
  equiv.swap (f x) (f y) (f z) = f (equiv.swap x y z) :=
begin
  by_cases hx : z = x, by simp [hx],
  by_cases hy : z = y, by simp [hy],
  rw [equiv.swap_apply_of_ne_of_ne hx hy, equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]
end

lemma function.injective.swap_comp [decidable_eq α] [decidable_eq β] {f : α → β}
  (hf : function.injective f) (x y : α) :
  equiv.swap (f x) (f y) ∘ f = f ∘ equiv.swap x y :=
funext $ λ z, hf.swap_apply _ _ _

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingleton_prod_self_equiv {α : Type*} [subsingleton α] : α × α ≃ α :=
{ to_fun := λ p, p.1,
  inv_fun := λ a, (a, a),
  left_inv := λ p, subsingleton.elim _ _,
  right_inv := λ p, subsingleton.elim _ _, }

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equiv_of_subsingleton_of_subsingleton [subsingleton α] [subsingleton β]
  (f : α → β) (g : β → α) : α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable
def equiv.punit_of_nonempty_of_subsingleton {α : Sort*} [h : nonempty α] [subsingleton α] :
  α ≃ punit.{v} :=
equiv_of_subsingleton_of_subsingleton
 (λ _, punit.star) (λ _, h.some)

/-- `unique (unique α)` is equivalent to `unique α`. -/
def unique_unique_equiv : unique (unique α) ≃ unique α :=
equiv_of_subsingleton_of_subsingleton (λ h, h.default)
  (λ h, { default := h, uniq := λ _, subsingleton.elim _ _ })

namespace function

lemma update_comp_equiv {α β α' : Sort*} [decidable_eq α'] [decidable_eq α] (f : α → β) (g : α' ≃ α)
  (a : α) (v : β) :
  update f a v ∘ g = update (f ∘ g) (g.symm a) v :=
by rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

lemma update_apply_equiv_apply {α β α' : Sort*} [decidable_eq α'] [decidable_eq α]
  (f : α → β) (g : α' ≃ α) (a : α) (v : β) (a' : α') :
  update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
congr_fun (update_comp_equiv f g a v) a'

lemma Pi_congr_left'_update [decidable_eq α] [decidable_eq β]
  (P : α → Sort*) (e : α ≃ β) (f : Π a, P a) (b : β) (x : P (e.symm b)) :
  e.Pi_congr_left' P (update f (e.symm b) x) = update (e.Pi_congr_left' P f) b x :=
begin
  ext b',
  rcases eq_or_ne b' b with rfl | h,
  { simp, },
  { simp [h], },
end

lemma Pi_congr_left'_symm_update [decidable_eq α] [decidable_eq β]
  (P : α → Sort*) (e : α ≃ β) (f : Π b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
  (e.Pi_congr_left' P).symm (update f b x) = update ((e.Pi_congr_left' P).symm f) (e.symm b) x :=
by simp [(e.Pi_congr_left' P).symm_apply_eq, Pi_congr_left'_update]

end function
