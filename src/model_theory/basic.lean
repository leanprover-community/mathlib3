/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import category_theory.concrete_category.bundled
import data.fin.tuple.basic
import logic.encodable.basic
import set_theory.cardinal

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

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/
universes u v u' v' w

open_locale cardinal
open cardinal

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

/-- The cardinality of a language is the cardinality of its type of symbols. -/
def card : cardinal := # L.symbols

/-- A language is countable when it has countably many symbols. -/
class countable : Prop := (card_le_omega' : L.card ≤ ω)

lemma card_le_omega [L.countable] : L.card ≤ ω := countable.card_le_omega'

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_functions : ∀ n, is_empty (L.functions n))

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, is_empty (L.relations n))

/-- A language is countable when it has countably many symbols. -/
class countable_functions : Prop := (card_functions_le_omega' : # (Σl, L.functions l) ≤ ω)

lemma card_functions_le_omega [L.countable_functions] :
  # (Σl, L.functions l) ≤ ω :=
countable_functions.card_functions_le_omega'

variables {L} {L' : language.{u' v'}}

lemma card_eq_card_functions_add_card_relations :
  L.card = cardinal.lift.{v} (# (Σl, L.functions l)) +
    cardinal.lift.{u} (# (Σl, L.relations l)) :=
by rw [card, symbols, mk_sum]

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

lemma encodable.countable [h : encodable L.symbols] :
  L.countable :=
⟨cardinal.encodable_iff.1 ⟨h⟩⟩

instance countable_empty : language.empty.countable :=
⟨begin
  rw [card_eq_card_functions_add_card_relations, add_le_omega, lift_le_omega, lift_le_omega,
    ← cardinal.encodable_iff, ← cardinal.encodable_iff],
  exact ⟨⟨encodable.sigma⟩, ⟨encodable.sigma⟩⟩,
end⟩

@[priority 100] instance countable.countable_functions [L.countable] :
  L.countable_functions :=
⟨begin
  refine lift_le_omega.1 (trans _ L.card_le_omega),
  rw [card, symbols, mk_sum],
  exact le_self_add,
end⟩

lemma encodable.countable_functions [h : encodable (Σl, L.functions l)] :
  L.countable_functions :=
⟨cardinal.encodable_iff.1 ⟨h⟩⟩

@[priority 100] instance is_relational.countable_functions [L.is_relational] :
  L.countable_functions :=
encodable.countable_functions

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

end language
end first_order
