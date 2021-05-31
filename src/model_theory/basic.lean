/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.nat.basic

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

universes l u

variables {α : Type u} {β : Type u}

namespace first_order

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
structure language : Type (l+1) :=
(functions : ℕ → Type l) (relations : ℕ → Type l)

namespace language

/-- The empty language has no symbols. -/
def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance] def const (L : language.{l}) : Type l := L.functions 0

variable (L : language.{u})

/-- A language is relational when it has no function symbols. -/
def is_relational : Prop := ∀ n, L.functions n → false

/-- A language is algebraic when it has no relation symbols. -/
def is_algebraic : Prop := ∀ n, L.relations n → false

variable {L}

lemma is_relational_of_empty {symb : ℕ → Type u}  : is_relational ⟨λ _, pempty, symb⟩ :=
by { intro n, apply pempty.elim }

lemma is_algebraic_of_empty {symb : ℕ → Type u}  : is_algebraic ⟨symb, λ _, pempty⟩ :=
by { intro n, apply pempty.elim }

variables (L) (M : Type u)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure :=
(fun_map : ∀{n}, L.functions n → (fin n → M) → M)
(rel_map : ∀{n}, L.relations n → (fin n → M) → Prop)

variables (N : Type u) [L.Structure M] [L.Structure N]

open first_order.language.Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
protected structure hom :=
(to_fun : M → N)
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x))
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r x → rel_map r (to_fun ∘ x))

notation A ` →[`:25 L `] ` B := L.hom A B

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
protected structure embedding extends M ↪ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x))
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x)

notation A ` ↪[`:25 L `] ` B := L.embedding A B

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
protected structure equiv extends M ≃ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x))
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x)

notation A ` ≃[`:25 L `] ` B := L.equiv A B

variables {L M N}
namespace hom

@[simps] instance has_coe_to_fun : has_coe_to_fun (M →[L] N) :=
⟨(λ _, M → N), first_order.language.hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_inj ⦃f g : M →[L] N⦄ (h : (f : M → N) = g) : f = g :=
by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r x → rel_map r (φ ∘ x) := φ.map_rel' r x

variables (L) (M)
/-- The identity map from a structure to itself-/
def id : M →[L] M :=
{ to_fun := id,
  map_fun' := λ _ _ _, rfl,
  map_rel' := λ _ _ _, id }

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

variables {P : Type u} [L.Structure P] {Q : Type u} [L.Structure Q]

/-- Composition of first-order homomorphisms -/
def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_fun' := λ n f, by simp,
  map_rel' := λ _ _ _ h, by simp [h] }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f.to_fun,
  map_fun' := f.map_fun',
  map_rel' := λ n r x, (f.map_rel' r x).2 }

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) :=
⟨(λ _, M → N), λ f, f.to_hom⟩

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_inj ⦃f g : M ↪[L] N⦄ (h : (f : M → N) = g) : f = g :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

lemma injective (f : M ↪[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity embedding from a structure to itself-/
def id : M ↪[L] M :=
{ to_embedding := function.embedding.refl M,
  map_fun' := λ _ _ _, rfl,
  map_rel' := λ _ _ _, iff.refl _ }

variables {L} {M}

instance : inhabited (M ↪[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

variables {P : Type u} [L.Structure P] {Q : Type u} [L.Structure Q]

/-- Composition of first-order embeddings -/
def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
{ to_fun := hnp ∘ hmn,
  inj' := hnp.injective.comp hmn.injective,
  map_fun' := λ n f, by simp,
  map_rel' := λ _ _ _, by rw [map_rel, map_rel], }

--infixr  ` ∘ `:80      := comp

@[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order embeddings is associative. -/
lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end embedding

namespace equiv

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
def symm (f : M ≃[L] N) : N ≃[L] M :=
{ map_fun' := λ n f' x, begin
    simp only [equiv.to_fun_as_coe],
    rw [equiv.symm_apply_eq],
    refine eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  map_rel' := λ n r x, begin
    simp only [equiv.to_fun_as_coe],
    refine (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  .. f.to_equiv.symm }

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_embedding := f.to_equiv.to_embedding,
  map_fun' := f.map_fun',
  map_rel' := f.map_rel' }

/-- A first-order equivalence is also a first-order embedding. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f.to_equiv,
  map_fun' := f.map_fun',
  map_rel' := λ n r x, (f.map_rel' r x).2 }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) :=
⟨(λ _, M → N), λ f, f.to_embedding⟩

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

lemma coe_inj ⦃f g : M ≃[L] N⦄ (h : (f : M → N) = g) : f = g :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity equivalence from a structure to itself-/
def id : M ≃[L] M :=
{ to_equiv := equiv.refl M,
  map_fun' := λ _ _ _, rfl,
  map_rel' := λ _ _ _, iff.refl _ }

variables {L} {M}

instance : inhabited (M ≃[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

variables {P : Type u} [L.Structure P] {Q : Type u} [L.Structure Q]

/-- Composition of first-order equivalences -/
def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ to_fun := hnp ∘ hmn,
  map_fun' := λ n f x, by simp,
  map_rel' := λ n r x, by rw [map_rel, map_rel],
  .. (hmn.to_equiv.trans hnp.to_equiv) }

--infixr  ` ∘ `:80      := comp

@[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

end language
end first_order
