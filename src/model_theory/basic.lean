/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.fin.tuple.basic

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
structure embedding extends M ↪ N :=
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

namespace hom

instance has_coe_to_fun : has_coe_to_fun (M →[L] N) (λ _, M → N) := ⟨to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_injective : @function.injective (M →[L] N) (M → N) coe_fn
| f g h := by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M →[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c default).trans (congr rfl (funext default))

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r x → rel_map r (φ ∘ x) := φ.map_rel' r x

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

instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) (λ _, M → N) := ⟨λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M ↪[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c default).trans (congr rfl (funext default))

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

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
  map_rel' := λ n, (is_algebraic.empty_relations n).elim,
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

instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) (λ _, M → N) := ⟨λ f, f.to_fun⟩

@[simp]
lemma apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a := f.to_equiv.apply_symm_apply a

@[simp]
lemma symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a := f.to_equiv.symm_apply_apply a

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_constants (φ : M ≃[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c default).trans (congr rfl (funext default))

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

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

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

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
protected def id (L : language) : L →ᴸ L :=
⟨λn, id, λ n, id⟩

instance : inhabited (L →ᴸ L) := ⟨Lhom.id L⟩

/-- The inclusion of the left factor into the sum of two languages. -/
protected def sum_inl : L →ᴸ L.sum L' :=
⟨λn, sum.inl, λ n, sum.inl⟩

/-- The inclusion of the right factor into the sum of two languages. -/
protected def sum_inr : L' →ᴸ L.sum L' :=
⟨λn, sum.inr, λ n, sum.inr⟩

variables (L L')

/-- The inclusion of an empty language into any other language. -/
protected def of_is_empty [L.is_algebraic] [L.is_relational] : L →ᴸ L' :=
⟨λ n, (is_relational.empty_functions n).elim, λ n, (is_algebraic.empty_relations n).elim⟩

variables {L L'}

/-- The composition of two language homomorphisms. -/
@[reducible] def comp {L1} {L2} {L3} (g : L2 →ᴸ L3) (f : L1 →ᴸ L2) : L1 →ᴸ L3 :=
⟨λ n F, g.1 (f.1 F), λ _ R, g.2 (f.2 R)⟩

@[ext] protected lemma funext {L1} {L2} {F G : L1 →ᴸ L2} (h_fun : F.on_function = G.on_function )
  (h_rel : F.on_relation = G.on_relation ) : F = G :=
by {cases F with Ff Fr, cases G with Gf Gr, simp only *, exact and.intro h_fun h_rel}

local infix ` ∘ `:60 := Lhom.comp

@[simp] lemma id_comp {L1 L2} {F : L1 →ᴸ L2} : (Lhom.id L2) ∘ F = F :=
by {cases F, refl}

@[simp] lemma comp_id {L1 L2} {F : L1 →ᴸ L2} : F ∘ (Lhom.id L1) = F :=
by {cases F, refl}

/-- A language map defined on two factors of a sum. -/
@[simps] def sum_elim {L'' : language} (ψ : L'' →ᴸ L') : L.sum L'' →ᴸ L' :=
{ on_function := λ n, sum.elim (λ f, ϕ.on_function f) (λ f, ψ.on_function f),
  on_relation := λ n, sum.elim (λ f, ϕ.on_relation f) (λ f, ψ.on_relation f) }

/-- The map between two sum-languages induced by maps on the two factors. -/
@[simps] def sum_map {L₁ L₂ : language} (ψ : L₁ →ᴸ L₂) : L.sum L₁ →ᴸ L'.sum L₂ :=
{ on_function := λ n, sum.map (λ f, ϕ.on_function f) (λ f, ψ.on_function f),
  on_relation := λ n, sum.map (λ f, ϕ.on_relation f) (λ f, ψ.on_relation f) }

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
def Lhom_with_constants : L →ᴸ L[[α]] := Lhom.sum_inl

variable {L}

/-- Adds constants to a language map.  -/
def Lhom.add_constants {L' : language} (φ : L →ᴸ L') :
  L[[α]] →ᴸ L'[[α]] := φ.sum_map (Lhom.id _)

instance params_Structure (A : set α) : (constants_on A).Structure α := constants_on.Structure coe

variables (L) (α)

/-- The language map removing an empty constant set.  -/
def Lhom_trim_empty_constants [is_empty α] : L[[α]] →ᴸ L :=
Lhom.sum_elim (Lhom.id L) (Lhom.of_is_empty (constants_on α) L)

variables {α} {β : Type*}

/-- The language map extending the constant set.  -/
def Lhom_with_constants_map (f : α → β) : L[[α]] →ᴸ L[[β]] :=
Lhom.sum_map (Lhom.id L) (Lhom.constants_on_map f)

@[simp] lemma Lhom.map_constants_comp_with_constants {f : α → β} :
  (L.Lhom_with_constants_map f).comp (L.Lhom_with_constants α) = L.Lhom_with_constants β :=
by ext n f R; refl

end

open_locale first_order
variables (A : set M)

instance with_constants_Structure : L[[A]].Structure M :=
language.sum_Structure _ _ _

instance trim_empty_constants_is_expansion_on :
  (L.Lhom_trim_empty_constants (∅ : set M)).is_expansion_on M :=
Lhom.sum_elim_is_expansion_on _ _ _

instance with_constants_expansion : (L.Lhom_with_constants A).is_expansion_on M :=
⟨λ _ _ _, rfl, λ _ _ _, rfl⟩

instance add_constants_expansion {L' : language} [L'.Structure M] (φ : L →ᴸ L')
  [φ.is_expansion_on M] :
  (φ.add_constants A).is_expansion_on M :=
Lhom.sum_map_is_expansion_on _ _ M

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
