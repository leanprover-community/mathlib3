/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.fin.tuple.basic
import category_theory.concrete_category.bundled

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

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
* A `first_order.language.elementary_embedding`, denoted `M ↪ₑ[L] N`, is an embedding from the
  `L`-structure `M` to the `L`-structure `N` that commutes with the realizations of all formulas.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.Lhom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* `first_order.language.with_constants` is defined so that if `M` is an `L.Structure` and
  `A : set M`, `L.with_constants A`, denoted `L[[A]]`, is a language which adds constant symbols for
  elements of `A` to `L`.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/
universes u v u' v' w

namespace first_order

/-! ### Languages and Structures -/

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint check_univs] -- intended to be used with explicit universe parameters
structure language :=
(functions : ℕ → Type u) (relations : ℕ → Type v)

namespace language

/-- The empty language has no symbols. -/
protected def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨language.empty⟩

/-- The sum of two languages consists of the disjoint union of their symbols. -/
protected def sum (L : language.{u v}) (L' : language.{u' v'}) : language :=
⟨λn, L.functions n ⊕ L'.functions n, λ n, L.relations n ⊕ L'.relations n⟩

variable (L : language.{u v})

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance] protected def «constants» := L.functions 0

/-- The type of symbols in a given language. -/
@[nolint has_inhabited_instance] def symbols := (Σl, L.functions l) ⊕ (Σl, L.relations l)

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_functions : ∀ n, is_empty (L.functions n))

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, is_empty (L.relations n))

variables {L} {L' : language.{u' v'}}

instance [L.is_relational] {n : ℕ} : is_empty (L.functions n) := is_relational.empty_functions n

instance [L.is_algebraic] {n : ℕ} : is_empty (L.relations n) := is_algebraic.empty_relations n

instance is_relational_of_empty_functions {symb : ℕ → Type*} : is_relational ⟨λ _, pempty, symb⟩ :=
⟨λ _, pempty.is_empty⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type*}  : is_algebraic ⟨symb, λ _, pempty⟩ :=
⟨λ _, pempty.is_empty⟩

instance is_relational_empty : is_relational language.empty :=
language.is_relational_of_empty_functions

instance is_algebraic_empty : is_algebraic language.empty :=
language.is_algebraic_of_empty_relations

instance is_relational_sum [L.is_relational] [L'.is_relational] : is_relational (L.sum L') :=
⟨λ n, sum.is_empty⟩

instance is_algebraic_sum [L.is_algebraic] [L'.is_algebraic] : is_algebraic (L.sum L') :=
⟨λ n, sum.is_empty⟩

variables (L) (M : Type w)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure :=
(fun_map : ∀{n}, L.functions n → (fin n → M) → M)
(rel_map : ∀{n}, L.relations n → (fin n → M) → Prop)

variables (N : Type*) [L.Structure M] [L.Structure N]

open Structure

/-! ### Maps -/

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure hom :=
(to_fun : M → N)
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r x → rel_map r (to_fun ∘ x) . obviously)

localized "notation A ` →[`:25 L `] ` B := L.hom A B" in first_order

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
@[ancestor function.embedding] structure embedding extends M ↪ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ↪[`:25 L `] ` B := L.embedding A B" in first_order

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure equiv extends M ≃ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in first_order

variables {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

instance : has_coe_t L.constants M :=
⟨λ c, fun_map c default⟩

lemma fun_map_eq_coe_constants {c : L.constants} {x : fin 0 → M} :
  fun_map c x = c := congr rfl (funext fin.elim0)

/-- Given a language with a nonempty type of constants, any structure will be nonempty. This cannot
  be a global instance, because `L` becomes a metavariable. -/
lemma nonempty_of_nonempty_constants [h : nonempty L.constants] : nonempty M :=
h.map coe

/-- `hom_class L F M N` states that `F` is a type of `L`-homomorphisms. You should extend this
  typeclass when you extend `first_order.language.hom`. -/
class hom_class (L : out_param language) (F : Type*)
  (M N : out_param $ Type*) [fun_like F M (λ _, N)] [L.Structure M] [L.Structure N] :=
(map_fun : ∀ (φ : F) {n} (f : L.functions n) x, φ (fun_map f x) = fun_map f (φ ∘ x))
(map_rel : ∀ (φ : F) {n} (r : L.relations n) x, rel_map r x → rel_map r (φ ∘ x))

/-- `strong_hom_class L F M N` states that `F` is a type of `L`-homomorphisms which preserve
  relations in both directions. -/
class strong_hom_class (L : out_param language) (F : Type*) (M N : out_param $ Type*)
  [fun_like F M (λ _, N)] [L.Structure M] [L.Structure N] :=
(map_fun : ∀ (φ : F) {n} (f : L.functions n) x, φ (fun_map f x) = fun_map f (φ ∘ x))
(map_rel : ∀ (φ : F) {n} (r : L.relations n) x, rel_map r (φ ∘ x) ↔ rel_map r x)

@[priority 100] instance strong_hom_class.hom_class
  {F M N} [L.Structure M] [L.Structure N] [fun_like F M (λ _, N)] [strong_hom_class L F M N] :
  hom_class L F M N :=
{ map_fun := strong_hom_class.map_fun,
  map_rel := λ φ n R x, (strong_hom_class.map_rel φ R x).2 }

/-- Not an instance to avoid a loop. -/
def hom_class.strong_hom_class_of_is_algebraic [L.is_algebraic]
  {F M N} [L.Structure M] [L.Structure N] [fun_like F M (λ _, N)] [hom_class L F M N] :
  strong_hom_class L F M N :=
{ map_fun := hom_class.map_fun,
  map_rel := λ φ n R x, (is_algebraic.empty_relations n).elim R }

lemma hom_class.map_constants {F M N} [L.Structure M] [L.Structure N] [fun_like F M (λ _, N)]
  [hom_class L F M N]
  (φ : F) (c : L.constants) : φ (c) = c :=
(hom_class.map_fun φ c default).trans (congr rfl (funext default))

namespace hom

instance fun_like : fun_like (M →[L] N) M (λ _, N) :=
{ coe := hom.to_fun,
  coe_injective' := λ f g h, by {cases f, cases g, cases h, refl} }

instance hom_class : hom_class L (M →[L] N) M N :=
{ map_fun := map_fun',
  map_rel := map_rel' }

instance [L.is_algebraic] : strong_hom_class L (M →[L] N) M N :=
hom_class.strong_hom_class_of_is_algebraic

instance has_coe_to_fun : has_coe_to_fun (M →[L] N) (λ _, M → N) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
hom_class.map_fun φ f x

@[simp] lemma map_constants (φ : M →[L] N) (c : L.constants) : φ c = c :=
hom_class.map_constants φ c

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r x → rel_map r (φ ∘ x) :=
hom_class.map_rel φ r x

variables (L) (M)
/-- The identity map from a structure to itself -/
@[refl] def id : M →[L] M :=
{ to_fun := id }

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

/-- Composition of first-order homomorphisms -/
@[trans] def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_rel' := λ _ _ _ h, by simp [h] }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

instance embedding_like : embedding_like (M ↪[L] N) M N :=
{ coe := λ f, f.to_fun,
  injective' := λ f, f.to_embedding.injective,
  coe_injective' := λ f g h, begin
    cases f,
    cases g,
    simp only,
    ext x,
    exact function.funext_iff.1 h x end }

instance strong_hom_class : strong_hom_class L (M ↪[L] N) M N :=
{ map_fun := map_fun',
  map_rel := map_rel' }

instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) (λ _, M → N) :=
fun_like.has_coe_to_fun

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
hom_class.map_fun φ f x

@[simp] lemma map_constants (φ : M ↪[L] N) (c : L.constants) : φ c = c :=
hom_class.map_constants φ c

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x :=
strong_hom_class.map_rel φ r x

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f }

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_injective : @function.injective (M ↪[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ↪[L] N) : function.injective f := f.to_embedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps] def of_injective [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) : M ↪[L] N :=
{ inj' := hf,
  map_rel' := λ n r x, strong_hom_class.map_rel f r x,
  .. f }

@[simp] lemma coe_fn_of_injective [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) :
  (of_injective hf : M → N) = f := rfl

@[simp] lemma of_injective_to_hom [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) :
  (of_injective hf).to_hom = f :=
by { ext, simp }

variables (L) (M)
/-- The identity embedding from a structure to itself -/
@[refl] def refl : M ↪[L] M :=
{ to_embedding := function.embedding.refl M }

variables {L} {M}

instance : inhabited (M ↪[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order embeddings -/
@[trans] def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
{ to_fun := hnp ∘ hmn,
  inj' := hnp.injective.comp hmn.injective }

@[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order embeddings is associative. -/
lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

@[simp] lemma comp_to_hom (hnp : N ↪[L] P) (hmn : M ↪[L] N) :
  (hnp.comp hmn).to_hom = hnp.to_hom.comp hmn.to_hom :=
by { ext, simp only [coe_to_hom, comp_apply, hom.comp_apply] }

end embedding

namespace equiv

instance : equiv_like (M ≃[L] N) M N :=
{ coe := λ f, f.to_fun,
  inv := λ f, f.inv_fun,
  left_inv := λ f, f.left_inv,
  right_inv := λ f, f.right_inv,
  coe_injective' := λ f g h₁ h₂, begin
    cases f,
    cases g,
    simp only,
    ext x,
    exact function.funext_iff.1 h₁ x,
  end, }

instance : strong_hom_class L (M ≃[L] N) M N :=
{ map_fun := map_fun',
  map_rel := map_rel', }

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm] def symm (f : M ≃[L] N) : N ≃[L] M :=
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

instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) (λ _, M → N) :=
fun_like.has_coe_to_fun

@[simp]
lemma apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a := f.to_equiv.apply_symm_apply a

@[simp]
lemma symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a := f.to_equiv.symm_apply_apply a

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
hom_class.map_fun φ f x

@[simp] lemma map_constants (φ : M ≃[L] N) (c : L.constants) : φ c = c :=
hom_class.map_constants φ c

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x :=
strong_hom_class.map_rel φ r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.to_equiv.injective }

/-- A first-order equivalence is also a first-order homomorphism. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn :=
fun_like.coe_injective

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma bijective (f : M ≃[L] N) : function.bijective f := equiv_like.bijective f

lemma injective (f : M ≃[L] N) : function.injective f := equiv_like.injective f

lemma surjective (f : M ≃[L] N) : function.surjective f := equiv_like.surjective f

variables (L) (M)
/-- The identity equivalence from a structure to itself -/
@[refl] def refl : M ≃[L] M :=
{ to_equiv := equiv.refl M }

variables {L} {M}

instance : inhabited (M ≃[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order equivalences -/
@[trans] def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ to_fun := hnp ∘ hmn,
  .. (hmn.to_equiv.trans hnp.to_equiv) }

@[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

section sum_Structure
variables (L₁ L₂ : language) (S : Type*) [L₁.Structure S] [L₂.Structure S]

instance sum_Structure :
  (L₁.sum L₂).Structure S :=
{ fun_map := λ n, sum.elim fun_map fun_map,
  rel_map := λ n, sum.elim rel_map rel_map, }

variables {L₁ L₂ S}

@[simp] lemma fun_map_sum_inl {n : ℕ} (f : L₁.functions n) :
  @fun_map (L₁.sum L₂) S _ n (sum.inl f) = fun_map f := rfl

@[simp] lemma fun_map_sum_inr {n : ℕ} (f : L₂.functions n) :
  @fun_map (L₁.sum L₂) S _ n (sum.inr f) = fun_map f := rfl

@[simp] lemma rel_map_sum_inl {n : ℕ} (R : L₁.relations n) :
  @rel_map (L₁.sum L₂) S _ n (sum.inl R) = rel_map R := rfl

@[simp] lemma rel_map_sum_inr {n : ℕ} (R : L₂.relations n) :
  @rel_map (L₁.sum L₂) S _ n (sum.inr R) = rel_map R := rfl

end sum_Structure

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure Lhom (L L' : language) :=
(on_function : ∀{n}, L.functions n → L'.functions n)
(on_relation : ∀{n}, L.relations n → L'.relations n)

infix ` →ᴸ `:10 := Lhom -- \^L

namespace Lhom

variables (ϕ : L →ᴸ L')

/-- The identity language homomorphism. -/
@[simps] protected def id (L : language) : L →ᴸ L :=
⟨λn, id, λ n, id⟩

instance : inhabited (L →ᴸ L) := ⟨Lhom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
@[simps] protected def sum_inl : L →ᴸ L.sum L' :=
⟨λn, sum.inl, λ n, sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
@[simps] protected def sum_inr : L' →ᴸ L.sum L' :=
⟨λn, sum.inr, λ n, sum.inr⟩

variables (L L')

/-- The inclusion of an empty language into any other language. -/
@[simps] protected def of_is_empty [L.is_algebraic] [L.is_relational] : L →ᴸ L' :=
⟨λ n, (is_relational.empty_functions n).elim, λ n, (is_algebraic.empty_relations n).elim⟩

variables {L L'} {L'' : language}

@[ext] protected lemma funext {F G : L →ᴸ L'} (h_fun : F.on_function = G.on_function )
  (h_rel : F.on_relation = G.on_relation ) : F = G :=
by {cases F with Ff Fr, cases G with Gf Gr, simp only *, exact and.intro h_fun h_rel}

instance [L.is_algebraic] [L.is_relational] : unique (L →ᴸ L') :=
⟨⟨Lhom.of_is_empty L L'⟩, λ _, Lhom.funext (subsingleton.elim _ _) (subsingleton.elim _ _)⟩

/-- The composition of two language homomorphisms. -/
@[simps] def comp (g : L' →ᴸ L'') (f : L →ᴸ L') : L →ᴸ L'' :=
⟨λ n F, g.1 (f.1 F), λ _ R, g.2 (f.2 R)⟩

local infix ` ∘ `:60 := Lhom.comp

@[simp] lemma id_comp (F : L →ᴸ L') : (Lhom.id L') ∘ F = F :=
by {cases F, refl}

@[simp] lemma comp_id (F : L →ᴸ L') : F ∘ (Lhom.id L) = F :=
by {cases F, refl}

lemma comp_assoc {L3 : language} (F: L'' →ᴸ L3) (G : L' →ᴸ L'') (H : L →ᴸ L') :
  (F ∘ G) ∘ H = F ∘ (G ∘ H) :=
rfl

section sum_elim

variables (ψ : L'' →ᴸ L')

/-- A language map defined on two factors of a sum. -/
@[simps] protected def sum_elim : L.sum L'' →ᴸ L' :=
{ on_function := λ n, sum.elim (λ f, ϕ.on_function f) (λ f, ψ.on_function f),
  on_relation := λ n, sum.elim (λ f, ϕ.on_relation f) (λ f, ψ.on_relation f) }

lemma sum_elim_comp_inl (ψ : L'' →ᴸ L') :
  (ϕ.sum_elim ψ) ∘ Lhom.sum_inl = ϕ :=
Lhom.funext (funext (λ _, rfl)) (funext (λ _, rfl))

lemma sum_elim_comp_inr (ψ : L'' →ᴸ L') :
  (ϕ.sum_elim ψ) ∘ Lhom.sum_inr = ψ :=
Lhom.funext (funext (λ _, rfl)) (funext (λ _, rfl))

theorem sum_elim_inl_inr :
  (Lhom.sum_inl).sum_elim (Lhom.sum_inr) = Lhom.id (L.sum L') :=
Lhom.funext (funext (λ _, sum.elim_inl_inr)) (funext (λ _, sum.elim_inl_inr))

theorem comp_sum_elim {L3 : language} (θ : L' →ᴸ L3) :
  θ ∘ (ϕ.sum_elim ψ) = (θ ∘ ϕ).sum_elim (θ ∘ ψ) :=
Lhom.funext (funext (λ n, sum.comp_elim _ _ _)) (funext (λ n, sum.comp_elim _ _ _))

end sum_elim

section sum_map

variables {L₁ L₂ : language} (ψ : L₁ →ᴸ L₂)

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps] def sum_map : L.sum L₁ →ᴸ L'.sum L₂ :=
{ on_function := λ n, sum.map (λ f, ϕ.on_function f) (λ f, ψ.on_function f),
  on_relation := λ n, sum.map (λ f, ϕ.on_relation f) (λ f, ψ.on_relation f) }

@[simp] lemma sum_map_comp_inl :
  (ϕ.sum_map ψ) ∘ Lhom.sum_inl = Lhom.sum_inl ∘ ϕ :=
Lhom.funext (funext (λ _, rfl)) (funext (λ _, rfl))

@[simp] lemma sum_map_comp_inr :
  (ϕ.sum_map ψ) ∘ Lhom.sum_inr = Lhom.sum_inr ∘ ψ :=
Lhom.funext (funext (λ _, rfl)) (funext (λ _, rfl))

end sum_map

/-- A language homomorphism is injective when all the maps between symbol types are. -/
protected structure injective : Prop :=
(on_function {n} : function.injective (on_function ϕ : L.functions n → L'.functions n))
(on_relation {n} : function.injective (on_relation ϕ : L.relations n → L'.relations n))

/-- A language homomorphism is an expansion on a structure if it commutes with the interpretation of
all symbols on that structure. -/
class is_expansion_on (M : Type*) [L.Structure M] [L'.Structure M] : Prop :=
(map_on_function : ∀ {n} (f : L.functions n) (x : fin n → M),
  fun_map (ϕ.on_function f) x = fun_map f x)
(map_on_relation : ∀ {n} (R : L.relations n) (x : fin n → M),
  rel_map (ϕ.on_relation R) x = rel_map R x)

attribute [simp] is_expansion_on.map_on_function is_expansion_on.map_on_relation

instance id_is_expansion_on (M : Type*) [L.Structure M] : is_expansion_on (Lhom.id L) M :=
⟨λ _ _ _, rfl, λ _ _ _, rfl⟩

instance of_is_empty_is_expansion_on (M : Type*) [L.Structure M] [L'.Structure M]
  [L.is_algebraic] [L.is_relational] :
  is_expansion_on (Lhom.of_is_empty L L') M :=
⟨λ n, (is_relational.empty_functions n).elim, λ n, (is_algebraic.empty_relations n).elim⟩

instance sum_elim_is_expansion_on {L'' : language} (ψ : L'' →ᴸ L') (M : Type*)
  [L.Structure M] [L'.Structure M] [L''.Structure M]
  [ϕ.is_expansion_on M] [ψ.is_expansion_on M] :
  (ϕ.sum_elim ψ).is_expansion_on M :=
⟨λ _ f _, sum.cases_on f (by simp) (by simp), λ _ R _, sum.cases_on R (by simp) (by simp)⟩

instance sum_map_is_expansion_on {L₁ L₂ : language} (ψ : L₁ →ᴸ L₂) (M : Type*)
  [L.Structure M] [L'.Structure M] [L₁.Structure M] [L₂.Structure M]
  [ϕ.is_expansion_on M] [ψ.is_expansion_on M] :
  (ϕ.sum_map ψ).is_expansion_on M :=
⟨λ _ f _, sum.cases_on f (by simp) (by simp), λ _ R _, sum.cases_on R (by simp) (by simp)⟩

end Lhom

/-- A language equivalence maps the symbols of one language to symbols of another bijectively. -/
structure Lequiv (L L' : language) :=
(to_Lhom : L →ᴸ L')
(inv_Lhom : L' →ᴸ L)
(left_inv : inv_Lhom.comp to_Lhom = Lhom.id L)
(right_inv : to_Lhom.comp inv_Lhom = Lhom.id L')

infix ` ≃ᴸ `:10 := Lequiv -- \^L

namespace Lequiv

variable (L)

/-- The identity equivalence from a first-order language to itself. -/
@[simps] protected def refl : L ≃ᴸ L :=
⟨Lhom.id L, Lhom.id L, Lhom.id_comp _, Lhom.id_comp _⟩

variable {L}

instance : inhabited (L ≃ᴸ L) := ⟨Lequiv.refl L⟩

variables {L'' : language} (e' : L' ≃ᴸ L'') (e : L ≃ᴸ L')

/-- The inverse of an equivalence of first-order languages. -/
@[simps] protected def symm : L' ≃ᴸ L :=
⟨e.inv_Lhom, e.to_Lhom, e.right_inv, e.left_inv⟩

/-- The composition of equivalences of first-order languages. -/
@[simps, trans] protected def trans (e : L ≃ᴸ L') (e' : L' ≃ᴸ L'') : L ≃ᴸ L'' :=
⟨e'.to_Lhom.comp e.to_Lhom, e.inv_Lhom.comp e'.inv_Lhom,
  by rw [Lhom.comp_assoc, ← Lhom.comp_assoc e'.inv_Lhom, e'.left_inv, Lhom.id_comp, e.left_inv],
  by rw [Lhom.comp_assoc, ← Lhom.comp_assoc e.to_Lhom, e.right_inv, Lhom.id_comp, e'.right_inv]⟩

end Lequiv

section constants_on
variables (α : Type u')

/-- The function symbols of a language with constants indexed by a type. -/
def constants_on_functions : ℕ → Type u'
| 0 := α
| _ := pempty

instance [h : inhabited α] : inhabited (constants_on_functions α 0) := h

/-- A language with constants indexed by a type. -/
def constants_on : language.{u' 0} := ⟨constants_on_functions α, λ _, pempty⟩

variables {α}

@[simp] lemma constants_on_constants : (constants_on α).constants = α := rfl

instance is_algebraic_constants_on : is_algebraic (constants_on α) :=
language.is_algebraic_of_empty_relations

instance is_relational_constants_on [ie : is_empty α] : is_relational (constants_on α) :=
⟨λ n, nat.cases_on n ie (λ _, pempty.is_empty)⟩

/-- Gives a `constants_on α` structure to a type by assigning each constant a value. -/
def constants_on.Structure (f : α → M) : (constants_on α).Structure M :=
{ fun_map := λ n, nat.cases_on n (λ a _, f a) (λ _, pempty.elim),
  rel_map := λ _, pempty.elim }

variables {β : Type v'}

/-- A map between index types induces a map between constant languages. -/
def Lhom.constants_on_map (f : α → β) : (constants_on α) →ᴸ (constants_on β) :=
⟨λ n, nat.cases_on n f (λ _, pempty.elim), λ n, pempty.elim⟩

lemma constants_on_map_is_expansion_on {f : α → β} {fα : α → M} {fβ : β → M}
  (h : fβ ∘ f = fα) :
  @Lhom.is_expansion_on _ _ (Lhom.constants_on_map f) M
    (constants_on.Structure fα) (constants_on.Structure fβ) :=
begin
  letI := constants_on.Structure fα,
  letI := constants_on.Structure fβ,
  exact ⟨λ n, nat.cases_on n (λ F x, (congr_fun h F : _)) (λ n F, pempty.elim F),
    λ _ R, pempty.elim R⟩,
end

end constants_on

section with_constants

variable (L)

section
variables (α : Type w)

/-- Extends a language with a constant for each element of a parameter set in `M`. -/
def with_constants : language.{(max u w) v} := L.sum (constants_on α)

localized "notation L`[[`:95 α`]]`:90 := L.with_constants α" in first_order

/-- The language map adding constants.  -/
@[simps] def Lhom_with_constants : L →ᴸ L[[α]] := Lhom.sum_inl

variables {α}

/-- The constant symbol indexed by a particular element. -/
protected def con (a : α) : L[[α]].constants := sum.inr a

variables {L} (α)

/-- Adds constants to a language map.  -/
def Lhom.add_constants {L' : language} (φ : L →ᴸ L') :
  L[[α]] →ᴸ L'[[α]] := φ.sum_map (Lhom.id _)

instance params_Structure (A : set α) : (constants_on A).Structure α := constants_on.Structure coe

variables (L) (α)

/-- The language map removing an empty constant set.  -/
@[simps] def Lequiv.add_empty_constants [ie : is_empty α] : L ≃ᴸ L[[α]] :=
{ to_Lhom := Lhom_with_constants L α,
  inv_Lhom := Lhom.sum_elim (Lhom.id L) (Lhom.of_is_empty (constants_on α) L),
  left_inv := by rw [Lhom_with_constants, Lhom.sum_elim_comp_inl],
  right_inv := by { simp only [Lhom.comp_sum_elim, Lhom_with_constants, Lhom.comp_id],
    exact trans (congr rfl (subsingleton.elim _ _)) Lhom.sum_elim_inl_inr } }

variables {α} {β : Type*}

/-- The language map extending the constant set.  -/
def Lhom_with_constants_map (f : α → β) : L[[α]] →ᴸ L[[β]] :=
Lhom.sum_map (Lhom.id L) (Lhom.constants_on_map f)

@[simp] lemma Lhom.map_constants_comp_sum_inl {f : α → β} :
  (L.Lhom_with_constants_map f).comp (Lhom.sum_inl) = L.Lhom_with_constants β :=
by ext n f R; refl

end

open_locale first_order
variables (A : set M)

instance with_constants_Structure : L[[A]].Structure M :=
language.sum_Structure _ _ _

instance with_constants_expansion : (L.Lhom_with_constants A).is_expansion_on M :=
⟨λ _ _ _, rfl, λ _ _ _, rfl⟩

instance add_empty_constants_is_expansion_on' :
  (Lequiv.add_empty_constants L (∅ : set M)).to_Lhom.is_expansion_on M :=
L.with_constants_expansion _

instance add_empty_constants_symm_is_expansion_on :
  (Lequiv.add_empty_constants L (∅ : set M)).symm.to_Lhom.is_expansion_on M :=
Lhom.sum_elim_is_expansion_on _ _ _

instance add_constants_expansion {L' : language} [L'.Structure M] (φ : L →ᴸ L')
  [φ.is_expansion_on M] :
  (φ.add_constants A).is_expansion_on M :=
Lhom.sum_map_is_expansion_on _ _ M

@[simp] lemma coe_con {a : A} : ((L.con a) : M) = a := rfl

variables {A} {B : set M} (h : A ⊆ B)

instance constants_on_map_inclusion_is_expansion_on :
  (Lhom.constants_on_map (set.inclusion h)).is_expansion_on M :=
constants_on_map_is_expansion_on rfl

instance map_constants_inclusion_is_expansion_on :
  (L.Lhom_with_constants_map (set.inclusion h)).is_expansion_on M :=
Lhom.sum_map_is_expansion_on _ _ _

end with_constants
end language
end first_order

variables {L : first_order.language.{u v}}

@[protected] instance category_theory.bundled.Structure
  {L : first_order.language.{u v}} (M : category_theory.bundled.{w} L.Structure) :
  L.Structure M :=
M.str

namespace first_order
namespace language
open_locale first_order

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equiv_setoid : setoid (category_theory.bundled L.Structure) :=
{ r := λ M N, nonempty (M ≃[L] N),
  iseqv := ⟨λ M, ⟨equiv.refl L M⟩, λ M N, nonempty.map equiv.symm,
    λ M N P, nonempty.map2 (λ MN NP, NP.comp MN)⟩ }

end language
end first_order
