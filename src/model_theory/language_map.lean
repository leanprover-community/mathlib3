/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import model_theory.basic
/-!
# Language Maps
Maps between first-order languages in the style of the
[Flypitch project](https://flypitch.github.io/), as well as several important maps between
structures.

## Main Definitions
* A `first_order.language.Lhom`, denoted `L →ᴸ L'`, is a map between languages, sending the symbols
  of one to symbols of the same kind and arity in the other.
* A `first_order.language.Lequiv`, denoted `L ≃ᴸ L'`, is an invertible language homomorphism.
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
namespace language
open Structure

variables (L : language.{u v}) (L' : language.{u' v'}) {M : Type w} [L.Structure M]

/-- A language homomorphism maps the symbols of one language to symbols of another. -/
structure Lhom :=
(on_function : ∀{n}, L.functions n → L'.functions n)
(on_relation : ∀{n}, L.relations n → L'.relations n)

infix ` →ᴸ `:10 := Lhom -- \^L

variables {L L'}

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
