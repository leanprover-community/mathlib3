/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import order.closure
import model_theory.semantics
import model_theory.encoding

/-!
# First-Order Substructures
This file defines substructures of first-order structures in a similar manner to the various
substructures appearing in the algebra library.

## Main Definitions
* A `first_order.language.substructure` is defined so that `L.substructure M` is the type of all
substructures of the `L`-structure `M`.
* `first_order.language.substructure.closure` is defined so that if `s : set M`, `closure L s` is
the least substructure of `M` containing `s`.
* `first_order.language.substructure.comap` is defined so that `s.comap f` is the preimage of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.substructure.map` is defined so that `s.map f` is the image of the
substructure `s` under the homomorphism `f`, as a substructure.
* `first_order.language.hom.range` is defined so that `f.map` is the range of the
the homomorphism `f`, as a substructure.
* `first_order.language.hom.dom_restrict` and `first_order.language.hom.cod_restrict` restrict
the domain and codomain respectively of first-order homomorphisms to substructures.
* `first_order.language.embedding.dom_restrict` and `first_order.language.embedding.cod_restrict`
restrict the domain and codomain respectively of first-order embeddings to substructures.
* `first_order.language.substructure.inclusion` is the inclusion embedding between substructures.

## Main Results
* `L.substructure M` forms a `complete_lattice`.

-/

universes u v w

namespace first_order
namespace language

variables {L : language.{u v}} {M : Type w} {N P : Type*}
variables [L.Structure M] [L.Structure N] [L.Structure P]
open_locale first_order cardinal
open Structure cardinal

section closed_under

open set

variables {n : ℕ} (f : L.functions n) (s : set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def closed_under : Prop :=
∀ (x : fin n → M), (∀ i : fin n, x i ∈ s) → fun_map f x ∈ s

variable (L)

@[simp] lemma closed_under_univ : closed_under f (univ : set M) :=
λ _ _, mem_univ _

variables {L f s} {t : set M}

namespace closed_under

lemma inter (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ∩ t) :=
λ x h, mem_inter (hs x (λ i, mem_of_mem_inter_left (h i)))
  (ht x (λ i, mem_of_mem_inter_right (h i)))

lemma inf (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ⊓ t) := hs.inter ht

variables {S : set (set M)}

lemma Inf (hS : ∀ s, s ∈ S → closed_under f s) : closed_under f (Inf S) :=
λ x h s hs, hS s hs x (λ i, h i s hs)

end closed_under
end closed_under

variables (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure substructure :=
(carrier : set M)
(fun_mem : ∀{n}, ∀ (f : L.functions n), closed_under f carrier)

variables {L} {M}

namespace substructure

instance : set_like (L.substructure M) M :=
⟨substructure.carrier, λ p q h, by cases p; cases q; congr'⟩

/-- See Note [custom simps projection] -/
def simps.coe (S : L.substructure M) : set M := S
initialize_simps_projections substructure (carrier → coe)

@[simp]
lemma mem_carrier {s : L.substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.substructure M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.substructure M) (s : set M) (hs : s = S) : L.substructure M :=
{ carrier := s,
  fun_mem := λ n f, hs.symm ▸ (S.fun_mem f) }

end substructure

variable {S : L.substructure M}

lemma term.realize_mem {α : Type*} (t : L.term α) (xs : α → M) (h : ∀ a, xs a ∈ S) :
  t.realize xs ∈ S :=
begin
  induction t with a n f ts ih,
  { exact h a },
  { exact substructure.fun_mem _ _ _ ih }
end

namespace substructure

@[simp] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma constants_mem (c : L.constants) : ↑c ∈ S :=
mem_carrier.2 (S.fun_mem c _ fin.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : has_top (L.substructure M) :=
⟨{ carrier := set.univ,
   fun_mem := λ n f x h, set.mem_univ _ }⟩

instance : inhabited (L.substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.substructure M) : set M) = set.univ := rfl

/-- The inf of two substructures is their intersection. -/
instance : has_inf (L.substructure M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    fun_mem := λ n f, (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
lemma coe_inf (p p' : L.substructure M) : ((p ⊓ p' : L.substructure M) : set M) = p ∩ p' := rfl

@[simp]
lemma mem_inf {p p' : L.substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (L.substructure M) :=
⟨λ s, { carrier := ⋂ t ∈ s, ↑t,
        fun_mem := λ n f, closed_under.Inf begin
          rintro _ ⟨t, rfl⟩,
          by_cases h : t ∈ s,
          { simpa [h] using t.fun_mem f },
          { simp [h] }
        end }⟩

@[simp, norm_cast]
lemma coe_Inf (S : set (L.substructure M)) :
  ((Inf S : L.substructure M) : set M) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (L.substructure M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p := set.mem_Inter₂

lemma mem_infi {ι : Sort*} {S : ι → L.substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → L.substructure M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : complete_lattice (L.substructure M) :=
{ le           := (≤),
  lt           := (<),
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (L.substructure M) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set M) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : lower_adjoint (coe : L.substructure M → set M) := ⟨λ s, Inf {S | s ⊆ S},
  λ s S, ⟨set.subset.trans (λ x hx, mem_Inf.2 $ λ S hS, hS hx), λ h, Inf_le h⟩⟩

variables {L} {s : set M}

lemma mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.substructure M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
lemma subset_closure : s ⊆ closure L s := (closure L).le_closure s

lemma not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure L s) : P ∉ s :=
λ h, hP (subset_closure h)

@[simp]
lemma closed (S : L.substructure M) : (closure L).closed (S : set M) :=
congr rfl ((closure L).eq_of_le set.subset.rfl (λ x xS, mem_closure.2 (λ T hT, hT xS)))

open set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
lemma closure_le : closure L s ≤ S ↔ s ⊆ S := (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
(closure L).monotone h

lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
(closure L).eq_of_le h₁ h₂

lemma coe_closure_eq_range_term_realize :
  (closure L s : set M) = range (@term.realize L _ _ _ (coe : s → M)) :=
begin
  let S : L.substructure M := ⟨range (term.realize coe), λ n f x hx, _⟩,
  { change _ = (S : set M),
    rw ← set_like.ext'_iff,
    refine closure_eq_of_le (λ x hx, ⟨var ⟨x, hx⟩, rfl⟩) (le_Inf (λ S' hS', _)),
    { rintro _ ⟨t, rfl⟩,
      exact t.realize_mem _ (λ i, hS' i.2) } },
  { simp only [mem_range] at *,
    refine ⟨func f (λ i, (classical.some (hx i))), _⟩,
    simp only [term.realize, λ i, classical.some_spec (hx i)] }
end

instance small_closure [small.{u} s] :
  small.{u} (closure L s) :=
begin
  rw [← set_like.coe_sort_coe, substructure.coe_closure_eq_range_term_realize],
  exact small_range _,
end

lemma mem_closure_iff_exists_term {x : M} :
  x ∈ closure L s ↔ ∃ (t : L.term s), t.realize (coe : s → M) = x :=
by rw [← set_like.mem_coe, coe_closure_eq_range_term_realize, mem_range]

lemma lift_card_closure_le_card_term : cardinal.lift.{max u w} (# (closure L s)) ≤ # (L.term s) :=
begin
  rw [← set_like.coe_sort_coe, coe_closure_eq_range_term_realize],
  rw [← cardinal.lift_id'.{w (max u w)} (# (L.term s))],
  exact cardinal.mk_range_le_lift,
end

theorem lift_card_closure_le : cardinal.lift.{(max u w) w} (# (closure L s)) ≤
  max ω (cardinal.lift.{(max u w) w} (#s) + cardinal.lift.{(max u w) u} (#(Σ i, L.functions i))) :=
begin
  refine lift_card_closure_le_card_term.trans (term.card_le.trans _),
  rw [mk_sum, lift_umax', lift_umax],
end

variable (L)

lemma _root_.set.countable.substructure_closure
  [L.countable_functions] (h : s.countable) :
  nonempty (encodable (closure L s)) :=
begin
  haveI : nonempty (encodable s) := h,
  rw [encodable_iff, ← lift_le_omega],
  exact lift_card_closure_le_card_term.trans term.card_le_omega,
end

variables {L} (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator] lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure L s)
  (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
(@closure_le L M _ ⟨set_of p, λ n, Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator] lemma dense_induction {p : M → Prop} (x : M) {s : set M}
  (hs : closure L s = ⊤) (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
have ∀ x ∈ closure L s, p x, from λ x hx, closure_induction hx Hs (λ n, Hfun),
by simpa [hs] using this x

variables (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure L M _) coe :=
{ choice := λ s _, closure L s,
  gc := (closure L).gc,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variables {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp] lemma closure_eq : closure L (S : set M) = S := (substructure.gi L M).l_u_eq S

@[simp] lemma closure_empty : closure L (∅ : set M) = ⊥ :=
(substructure.gi L M).gc.l_bot

@[simp] lemma closure_univ : closure L (univ : set M) = ⊤ :=
@coe_top L M _ ▸ closure_eq ⊤

lemma closure_union (s t : set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
(substructure.gi L M).gc.l_sup

lemma closure_Union {ι} (s : ι → set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
(substructure.gi L M).gc.l_supr

instance small_bot :
  small.{u} (⊥ : L.substructure M) :=
begin
  rw ← closure_empty,
  exact substructure.small_closure
end

/-!
### `comap` and `map`
-/

/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps] def comap (φ : M →[L] N) (S : L.substructure N) : L.substructure M :=
{ carrier := (φ ⁻¹' S),
  fun_mem := λ n f x hx, begin
    rw [mem_preimage, φ.map_fun],
    exact S.fun_mem f (φ ∘ x) hx,
  end }

@[simp]
lemma mem_comap {S : L.substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

lemma comap_comap (S : L.substructure P) (g : N →[L] P) (f : M →[L] N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

@[simp]
lemma comap_id (S : L.substructure P) : S.comap (hom.id _ _) = S :=
ext (by simp)

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps] def map (φ : M →[L] N) (S : L.substructure M) : L.substructure N :=
{ carrier := (φ '' S),
  fun_mem := λ n f x hx, (mem_image _ _ _).1
    ⟨fun_map f (λ i, classical.some (hx i)),
     S.fun_mem f _ (λ i, (classical.some_spec (hx i)).1),
     begin
       simp only [hom.map_fun, set_like.mem_coe],
       exact congr rfl (funext (λ i, (classical.some_spec (hx i)).2)),
     end⟩ }

@[simp]
lemma mem_map {f : M →[L] N} {S : L.substructure M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

lemma mem_map_of_mem (f : M →[L] N) {S : L.substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
mem_image_of_mem f hx

lemma apply_coe_mem_map (f : M →[L] N) (S : L.substructure M) (x : S) : f x ∈ S.map f :=
mem_map_of_mem f x.prop

lemma map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image _ _ _

lemma map_le_iff_le_comap {f : M →[L] N} {S : L.substructure M} {T : L.substructure N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

lemma gc_map_comap (f : M →[L] N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

lemma map_le_of_le_comap {T : L.substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
(gc_map_comap f).l_le

lemma le_comap_of_map_le {T : L.substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
(gc_map_comap f).le_u

lemma le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_comap_le {S : L.substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
(gc_map_comap f).l_u_le _

lemma monotone_map {f : M →[L] N} : monotone (map f) :=
(gc_map_comap f).monotone_l

lemma monotone_comap {f : M →[L] N} : monotone (comap f) :=
(gc_map_comap f).monotone_u

@[simp]
lemma map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
(gc_map_comap f).l_u_l_eq_l _

@[simp]
lemma comap_map_comap {S : L.substructure N} {f : M →[L] N} :
  ((S.comap f).map f).comap f = S.comap f :=
(gc_map_comap f).u_l_u_eq_u _

lemma map_sup (S T : L.substructure M) (f : M →[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : M →[L] N) (s : ι → L.substructure M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (S T : L.substructure N) (f : M →[L] N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : M →[L] N) (s : ι → L.substructure N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : M →[L] N) : (⊥ : L.substructure M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : M →[L] N) : (⊤ : L.substructure N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp] lemma map_id (S : L.substructure M) : S.map (hom.id L M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

lemma map_closure (f : M →[L] N) (s : set M) :
  (closure L s).map f = closure L (f '' s) :=
eq.symm $ closure_eq_of_le (set.image_subset f subset_closure) $ map_le_iff_le_comap.2 $
  closure_le.2 $ λ x hx, subset_closure ⟨x, hx, rfl⟩

@[simp] lemma closure_image (f : M →[L] N) :
  closure L (f '' s) = map f (closure L s) :=
(map_closure f s).symm

section galois_coinsertion

variables {ι : Type*} {f : M →[L] N} (hf : function.injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap : galois_coinsertion (map f) (comap f) :=
(gc_map_comap f).to_galois_coinsertion
  (λ S x, by simp [mem_comap, mem_map, hf.eq_iff])

lemma comap_map_eq_of_injective (S : L.substructure M) : (S.map f).comap f = S :=
(gci_map_comap hf).u_l_eq _

lemma comap_surjective_of_injective : function.surjective (comap f) :=
(gci_map_comap hf).u_surjective

lemma map_injective_of_injective : function.injective (map f) :=
(gci_map_comap hf).l_injective

lemma comap_inf_map_of_injective (S T : L.substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
(gci_map_comap hf).u_inf_l _ _

lemma comap_infi_map_of_injective (S : ι → L.substructure M) :
  (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

lemma comap_sup_map_of_injective (S T : L.substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
(gci_map_comap hf).u_sup_l _ _

lemma comap_supr_map_of_injective (S : ι → L.substructure M) :
  (⨆ i, (S i).map f).comap f = supr S :=
(gci_map_comap hf).u_supr_l _

lemma map_le_map_iff_of_injective {S T : L.substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
(gci_map_comap hf).l_le_l_iff

lemma map_strict_mono_of_injective : strict_mono (map f) :=
(gci_map_comap hf).strict_mono_l

end galois_coinsertion

section galois_insertion

variables {ι : Type*} {f : M →[L] N} (hf : function.surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
(gc_map_comap f).to_galois_insertion
  (λ S x h, let ⟨y, hy⟩ := hf x in mem_map.2 ⟨y, by simp [hy, h]⟩)

lemma map_comap_eq_of_surjective (S : L.substructure N) : (S.comap f).map f = S :=
(gi_map_comap hf).l_u_eq _

lemma map_surjective_of_surjective : function.surjective (map f) :=
(gi_map_comap hf).l_surjective

lemma comap_injective_of_surjective : function.injective (comap f) :=
(gi_map_comap hf).u_injective

lemma map_inf_comap_of_surjective (S T : L.substructure N) :
  (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
(gi_map_comap hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (S : ι → L.substructure N) :
  (⨅ i, (S i).comap f).map f = infi S :=
(gi_map_comap hf).l_infi_u _

lemma map_sup_comap_of_surjective (S T : L.substructure N) :
  (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
(gi_map_comap hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (S : ι → L.substructure N) :
  (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

lemma comap_le_comap_iff_of_surjective {S T : L.substructure N} :
  S.comap f ≤ T.comap f ↔ S ≤ T :=
(gi_map_comap hf).u_le_u_iff

lemma comap_strict_mono_of_surjective : strict_mono (comap f) :=
(gi_map_comap hf).strict_mono_u

end galois_insertion

instance induced_Structure {S : L.substructure M} : L.Structure S :=
{ fun_map := λ n f x, ⟨fun_map f (λ i, x i), S.fun_mem f (λ i, x i) (λ i, (x i).2)⟩,
  rel_map := λ n r x, rel_map r (λ i, (x i : M)) }

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.substructure M) : S ↪[L] M :=
{ to_fun := coe,
  inj' := subtype.coe_injective }

@[simp] theorem coe_subtype : ⇑S.subtype = coe := rfl

/-- The equivalence between the maximal substructure of a structure and the structure itself. -/
def top_equiv : (⊤ : L.substructure M) ≃[L] M  :=
{ to_fun := subtype ⊤,
  inv_fun := λ m, ⟨m, mem_top m⟩,
  left_inv := λ m, by simp,
  right_inv := λ m, rfl }

@[simp] lemma coe_top_equiv : ⇑(top_equiv : (⊤ : L.substructure M) ≃[L] M) = coe := rfl

/-- A dependent version of `substructure.closure_induction`. -/
@[elab_as_eliminator] lemma closure_induction' (s : set M) {p : Π x, x ∈ closure L s → Prop}
  (Hs : ∀ x (h : x ∈ s), p x (subset_closure h))
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f {x | ∃ hx, p x hx})
  {x} (hx : x ∈ closure L s) :
  p x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ closure L s) (hc : p x hx), hc),
  exact closure_induction hx (λ x hx, ⟨subset_closure hx, Hs x hx⟩) @Hfun
end

end substructure

namespace Lhom
open substructure

variables {L' : language} [L'.Structure M] (φ : L →ᴸ L') [φ.is_expansion_on M]
include φ

/-- Reduces the language of a substructure along a language hom. -/
def substructure_reduct : L'.substructure M ↪o L.substructure M :=
{ to_fun := λ S, { carrier := S,
    fun_mem := λ n f x hx, begin
      have h := S.fun_mem (φ.on_function f) x hx,
      simp only [is_expansion_on.map_on_function, substructure.mem_carrier] at h,
      exact h,
    end },
  inj' := λ S T h, begin
    simp only [set_like.coe_set_eq] at h,
    exact h,
  end,
  map_rel_iff' := λ S T, iff.rfl }

@[simp] lemma mem_substructure_reduct {x : M} {S : L'.substructure M} :
  x ∈ φ.substructure_reduct S ↔ x ∈ S := iff.rfl

@[simp] lemma coe_substructure_reduct {S : L'.substructure M} :
  (φ.substructure_reduct S : set M) = ↑S := rfl

end Lhom

namespace substructure

/-- Turns any substructure containing a constant set `A` into a `L[[A]]`-substructure. -/
def with_constants (S : L.substructure M) {A : set M} (h : A ⊆ S) : L[[A]].substructure M :=
{ carrier := S,
  fun_mem := λ n f, begin
    cases f,
    { exact S.fun_mem f },
    { cases n,
      { exact λ _ _, h f.2 },
      { exact is_empty_elim f } }
  end }

variables {A : set M} {s : set M} (h : A ⊆ S)

@[simp] lemma mem_with_constants {x : M} : x ∈ S.with_constants h ↔ x ∈ S := iff.rfl

@[simp] lemma coe_with_constants : (S.with_constants h : set M) = ↑S := rfl

@[simp] lemma reduct_with_constants :
  (L.Lhom_with_constants A).substructure_reduct (S.with_constants h) = S :=
by { ext, simp }

lemma subset_closure_with_constants : A ⊆ (closure (L[[A]]) s) :=
begin
  intros a ha,
  simp only [set_like.mem_coe],
  let a' : (L[[A]]).constants := sum.inr ⟨a, ha⟩,
  exact constants_mem a',
end

lemma closure_with_constants_eq : (closure (L[[A]]) s) = (closure L (A ∪ s)).with_constants
  ((A.subset_union_left s).trans subset_closure) :=
begin
  refine closure_eq_of_le ((A.subset_union_right s).trans subset_closure) _,
  rw ← ((L.Lhom_with_constants A).substructure_reduct).le_iff_le,
  simp only [subset_closure, reduct_with_constants, closure_le, Lhom.coe_substructure_reduct,
    set.union_subset_iff, and_true],
  { exact subset_closure_with_constants },
  { apply_instance },
  { apply_instance },
end

end substructure

namespace hom

open substructure

/-- The restriction of a first-order hom to a substructure `s ⊆ M` gives a hom `s → N`. -/
@[simps] def dom_restrict (f : M →[L] N) (p : L.substructure M) : p →[L] N :=
f.comp p.subtype.to_hom

/-- A first-order hom `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted to a
hom `M → p`. -/
@[simps] def cod_restrict (p : L.substructure N) (f : M →[L] N) (h : ∀c, f c ∈ p) : M →[L] p :=
{ to_fun := λc, ⟨f c, h c⟩,
  map_rel' := λ n R x h, f.map_rel R x h }

@[simp] lemma comp_cod_restrict (f : M →[L] N) (g : N →[L] P) (p : L.substructure P)
  (h : ∀b, g b ∈ p) :
  ((cod_restrict p g h).comp f : M →[L] p) = cod_restrict p (g.comp f) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (f : M →[L] N) (p : L.substructure N) (h : ∀b, f b ∈ p) :
  p.subtype.to_hom.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- The range of a first-order hom `f : M → N` is a submodule of `N`.
See Note [range copy pattern]. -/
def range (f : M →[L] N) : L.substructure N :=
(map f ⊤).copy (set.range f) set.image_univ.symm

theorem range_coe (f : M →[L] N) :
  (range f : set N) = set.range f := rfl

@[simp] theorem mem_range
  {f : M →[L] N} {x} : x ∈ range f ↔ ∃ y, f y = x :=
iff.rfl

lemma range_eq_map
  (f : M →[L] N) : f.range = map f ⊤ :=
by { ext, simp }

theorem mem_range_self
  (f : M →[L] N) (x : M) : f x ∈ f.range := ⟨x, rfl⟩

@[simp] theorem range_id : range (id L M) = ⊤ :=
set_like.coe_injective set.range_id

theorem range_comp (f : M →[L] N) (g : N →[L] P) :
  range (g.comp f : M →[L] P) = map g (range f) :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range (f : M →[L] N) (g : N →[L] P) :
  range (g.comp f : M →[L] P) ≤ range g :=
set_like.coe_mono (set.range_comp_subset_range f g)

theorem range_eq_top {f : M →[L] N} :
  range f = ⊤ ↔ function.surjective f :=
by rw [set_like.ext'_iff, range_coe, coe_top, set.range_iff_surjective]

lemma range_le_iff_comap {f : M →[L] N} {p : L.substructure N} :
  range f ≤ p ↔ comap f p = ⊤ :=
by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : M →[L] N} {p : L.substructure M} :
  map f p ≤ range f :=
set_like.coe_mono (set.image_subset_range f p)

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eq_locus (f g : M →[L] N) : substructure L M :=
{ carrier := {x : M | f x = g x},
  fun_mem := λ n fn x hx, by
  { have h : f ∘ x = g ∘ x := by { ext, repeat {rw function.comp_apply}, apply hx, },
    simp [h], } }

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
lemma eq_on_closure {f g : M →[L] N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure L s) :=
show closure L s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_top {f g : M →[L] N} (h : set.eq_on f g (⊤ : substructure L M)) :
  f = g :=
ext $ λ x, h trivial

variable {s : set M}

lemma eq_of_eq_on_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_top $ hs ▸ eq_on_closure h

end hom

namespace embedding
open substructure

/-- The restriction of a first-order embedding to a substructure `s ⊆ M` gives an embedding `s → N`.
-/
def dom_restrict (f : M ↪[L] N) (p : L.substructure M) : p ↪[L] N :=
  f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : M ↪[L] N) (p : L.substructure M) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A first-order embedding `f : M → N` whose values lie in a substructure `p ⊆ N` can be restricted
to an embedding `M → p`. -/
def cod_restrict (p : L.substructure N) (f : M ↪[L] N) (h : ∀c, f c ∈ p) : M ↪[L] p :=
{ to_fun := f.to_hom.cod_restrict p h,
  inj' := λ a b ab, f.injective (subtype.mk_eq_mk.1 ab),
  map_fun' := λ n F x, (f.to_hom.cod_restrict p h).map_fun' F x,
  map_rel' := λ n r x, begin
    simp only,
    rw [← p.subtype.map_rel, function.comp.assoc],
    change rel_map r ((hom.comp p.subtype.to_hom (f.to_hom.cod_restrict p h)) ∘ x) ↔ _,
    rw [hom.subtype_comp_cod_restrict, ← f.map_rel],
    refl,
  end }

@[simp] theorem cod_restrict_apply (p : L.substructure N) (f : M ↪[L] N) {h} (x : M) :
  (cod_restrict p f h x : N) = f x := rfl

@[simp] lemma comp_cod_restrict (f : M ↪[L] N) (g : N ↪[L] P) (p : L.substructure P)
  (h : ∀b, g b ∈ p) :
  ((cod_restrict p g h).comp f : M ↪[L] p) = cod_restrict p (g.comp f) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (f : M ↪[L] N) (p : L.substructure N) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- The equivalence between a substructure `s` and its image `s.map f.to_hom`, where `f` is an
  embedding. -/
noncomputable def substructure_equiv_map (f : M ↪[L] N) (s : L.substructure M) :
  s ≃[L] s.map f.to_hom :=
{ to_fun := cod_restrict (s.map f.to_hom) (f.dom_restrict s) (λ ⟨m, hm⟩, ⟨m, hm, rfl⟩),
  inv_fun := λ n, ⟨classical.some n.2, (classical.some_spec n.2).1⟩,
  left_inv := λ ⟨m, hm⟩, subtype.mk_eq_mk.2 (f.injective ((classical.some_spec (cod_restrict
    (s.map f.to_hom) (f.dom_restrict s) (λ ⟨m, hm⟩, ⟨m, hm, rfl⟩) ⟨m, hm⟩).2).2)),
  right_inv := λ ⟨n, hn⟩, subtype.mk_eq_mk.2 (classical.some_spec hn).2 }

@[simp] lemma substructure_equiv_map_apply (f : M ↪[L] N) (p : L.substructure M) (x : p) :
  (f.substructure_equiv_map p x : N) = f x := rfl

/-- The equivalence between the domain and the range of an embedding `f`. -/
noncomputable def equiv_range (f : M ↪[L] N) :
  M ≃[L] f.to_hom.range :=
{ to_fun := cod_restrict f.to_hom.range f f.to_hom.mem_range_self,
  inv_fun := λ n, classical.some n.2,
  left_inv := λ m, f.injective (classical.some_spec (cod_restrict f.to_hom.range f
    f.to_hom.mem_range_self m).2),
  right_inv := λ ⟨n, hn⟩, subtype.mk_eq_mk.2 (classical.some_spec hn) }

@[simp] lemma equiv_range_apply (f : M ↪[L] N) (x : M) :
  (f.equiv_range x : N) = f x := rfl

end embedding

namespace equiv

lemma to_hom_range (f : M ≃[L] N) :
  f.to_hom.range = ⊤ :=
begin
  ext n,
  simp only [hom.mem_range, coe_to_hom, substructure.mem_top, iff_true],
  exact ⟨f.symm n, apply_symm_apply _ _⟩
end

end equiv

namespace substructure

/-- The embedding associated to an inclusion of substructures. -/
def inclusion {S T : L.substructure M} (h : S ≤ T) : S ↪[L] T :=
S.subtype.cod_restrict _ (λ x, h x.2)

@[simp] lemma coe_inclusion {S T : L.substructure M} (h : S ≤ T) :
  (inclusion h : S → T) = set.inclusion h := rfl

lemma range_subtype (S : L.substructure M) : S.subtype.to_hom.range = S :=
begin
  ext x,
  simp only [hom.mem_range, embedding.coe_to_hom, coe_subtype],
  refine ⟨_, λ h, ⟨⟨x, h⟩, rfl⟩⟩,
  rintros ⟨⟨y, hy⟩, rfl⟩,
  exact hy,
end

end substructure

end language
end first_order
