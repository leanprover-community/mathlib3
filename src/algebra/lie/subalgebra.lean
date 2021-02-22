/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.basic
import ring_theory.noetherian

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `lie_subalgebra`
  * `lie_subalgebra.incl`
  * `lie_subalgebra.map`
  * `lie_hom.range`
  * `lie_equiv.of_injective`
  * `lie_equiv.of_eq`
  * `lie_equiv.of_subalgebra`
  * `lie_equiv.of_subalgebras`

## Tags

lie algebra, lie subalgebra
-/

universes u v w w₁ w₂

section lie_subalgebra

variables (R : Type u) (L : Type v) [comm_ring R] [lie_ring L] [lie_algebra R L]

set_option old_structure_cmd true
/-- A Lie subalgebra of a Lie algebra is submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie algebra. -/
structure lie_subalgebra extends submodule R L :=
(lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier)

attribute [nolint doc_blame] lie_subalgebra.to_submodule

/-- The zero algebra is a subalgebra of any Lie algebra. -/
instance : has_zero (lie_subalgebra R L) :=
⟨{ lie_mem' := λ x y hx hy, by { rw [((submodule.mem_bot R).1 hx), zero_lie],
                                exact submodule.zero_mem (0 : submodule R L), },
   ..(0 : submodule R L) }⟩

instance : inhabited (lie_subalgebra R L) := ⟨0⟩
instance : has_coe (lie_subalgebra R L) (submodule R L) := ⟨lie_subalgebra.to_submodule⟩
instance : has_mem L (lie_subalgebra R L) := ⟨λ x L', x ∈ (L' : set L)⟩

/-- A Lie subalgebra forms a new Lie ring. -/
instance lie_subalgebra_lie_ring (L' : lie_subalgebra R L) : lie_ring L' :=
{ bracket      := λ x y, ⟨⁅x.val, y.val⁆, L'.lie_mem' x.property y.property⟩,
  lie_add      := by { intros, apply set_coe.ext, apply lie_add, },
  add_lie      := by { intros, apply set_coe.ext, apply add_lie, },
  lie_self     := by { intros, apply set_coe.ext, apply lie_self, },
  leibniz_lie  := by { intros, apply set_coe.ext, apply leibniz_lie, } }

/-- A Lie subalgebra forms a new Lie algebra. -/
instance lie_subalgebra_lie_algebra (L' : lie_subalgebra R L) : lie_algebra R L' :=
{ lie_smul := by { intros, apply set_coe.ext, apply lie_smul } }

namespace lie_subalgebra

variables {R L} (L' : lie_subalgebra R L)

@[simp] lemma zero_mem : (0 : L) ∈ L' := (L' : submodule R L).zero_mem

lemma smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' := (L' : submodule R L).smul_mem t h

lemma add_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (x + y : L) ∈ L' :=
(L' : submodule R L).add_mem hx hy

lemma lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' := L'.lie_mem' hx hy

@[simp] lemma mem_carrier {x : L} : x ∈ L'.carrier ↔ x ∈ (L' : set L) := iff.rfl

@[simp] lemma mem_coe_submodule {x : L} : x ∈ (L' : submodule R L) ↔ x ∈ L' := iff.rfl

lemma mem_coe {x : L} : x ∈ (L' : set L) ↔ x ∈ L' := iff.rfl

@[simp, norm_cast] lemma coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x : L), ↑y⁆ := rfl

lemma ext_iff (x y : L') : x = y ↔ (x : L) = y := subtype.ext_iff

lemma coe_zero_iff_zero (x : L') : (x : L) = 0 ↔ x = 0 := (ext_iff L' x 0).symm

@[ext] lemma ext (L₁' L₂' : lie_subalgebra R L) (h : ∀ x, x ∈ L₁' ↔ x ∈ L₂') :
  L₁' = L₂' :=
by { cases L₁', cases L₂', simp only [], ext x, exact h x, }

lemma ext_iff' (L₁' L₂' : lie_subalgebra R L) : L₁' = L₂' ↔ ∀ x, x ∈ L₁' ↔ x ∈ L₂' :=
⟨λ h x, by rw h, ext L₁' L₂'⟩

@[simp] lemma mk_coe (S : set L) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : lie_subalgebra R L) : set L) = S := rfl

@[simp] lemma coe_to_submodule_mk (p : submodule R L) (h) :
  (({lie_mem' := h, ..p} : lie_subalgebra R L) : submodule R L) = p :=
by { cases p, refl, }

lemma coe_injective : function.injective (coe : lie_subalgebra R L → set L) :=
λ L₁' L₂' h, by cases L₁'; cases L₂'; congr'

@[norm_cast] theorem coe_set_eq (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : set L) = L₂' ↔ L₁' = L₂' := coe_injective.eq_iff

lemma to_submodule_injective :
  function.injective (coe : lie_subalgebra R L → submodule R L) :=
λ L₁' L₂' h, by { rw submodule.ext'_iff at h, rw ← coe_set_eq, exact h, }

@[simp] lemma coe_to_submodule_eq_iff (L₁' L₂' : lie_subalgebra R L) :
  (L₁' : submodule R L) = (L₂' : submodule R L) ↔ L₁' = L₂' :=
to_submodule_injective.eq_iff

@[norm_cast]
lemma coe_to_submodule : ((L' : submodule R L) : set L) = L' := rfl

end lie_subalgebra

variables {R L} {L₂ : Type w} [lie_ring L₂] [lie_algebra R L₂]
variables (f : L →ₗ⁅R⁆ L₂)

/-- The embedding of a Lie subalgebra into the ambient space as a Lie morphism. -/
def lie_subalgebra.incl (L' : lie_subalgebra R L) : L' →ₗ⁅R⁆ L :=
{ map_lie' := λ x y, by { rw [linear_map.to_fun_eq_coe, submodule.subtype_apply], refl, },
  ..L'.to_submodule.subtype }

namespace lie_hom

/-- The range of a morphism of Lie algebras is a Lie subalgebra. -/
def range : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y,
    show x ∈ f.to_linear_map.range → y ∈ f.to_linear_map.range → ⁅x, y⁆ ∈ f.to_linear_map.range,
    by { repeat { rw linear_map.mem_range }, rintros ⟨x', hx⟩ ⟨y', hy⟩, refine ⟨⁅x', y'⁆, _⟩,
         rw [←hx, ←hy], change f ⁅x', y'⁆ = ⁅f x', f y'⁆, rw map_lie, },
  ..(f : L →ₗ[R] L₂).range }

@[simp] lemma range_coe : (f.range : set L₂) = set.range f :=
linear_map.range_coe ↑f

@[simp] lemma mem_range (x : L₂) : x ∈ f.range ↔ ∃ (y : L), f y = x := linear_map.mem_range

end lie_hom

namespace lie_subalgebra

variables (K K' : lie_subalgebra R L) (K₂ : lie_subalgebra R L₂)

@[simp] lemma incl_range : K.incl.range = K :=
by { rw ← coe_to_submodule_eq_iff, exact (K : submodule R L).range_subtype, }

/-- The image of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
codomain. -/
def map : lie_subalgebra R L₂ :=
{ lie_mem' := λ x y hx hy, by {
    erw submodule.mem_map at hx, rcases hx with ⟨x', hx', hx⟩, rw ←hx,
    erw submodule.mem_map at hy, rcases hy with ⟨y', hy', hy⟩, rw ←hy,
    erw submodule.mem_map,
    exact ⟨⁅x', y'⁆, K.lie_mem hx' hy', f.map_lie x' y'⟩, },
..((K : submodule R L).map (f : L →ₗ[R] L₂)) }

@[simp] lemma mem_map (x : L₂) : x ∈ K.map f ↔ ∃ (y : L), y ∈ K ∧ f y = x := submodule.mem_map

-- TODO Rename and state for homs instead of equivs.
@[simp] lemma mem_map_submodule (e : L ≃ₗ⁅R⁆ L₂) (x : L₂) :
  x ∈ K.map (e : L →ₗ⁅R⁆ L₂) ↔ x ∈ (K : submodule R L).map (e : L →ₗ[R] L₂) :=
iff.rfl

/-- The preimage of a Lie subalgebra under a Lie algebra morphism is a Lie subalgebra of the
domain. -/
def comap : lie_subalgebra R L :=
{ lie_mem' := λ x y hx hy, by
    { suffices : ⁅f x, f y⁆ ∈ K₂, by { simp [this], }, exact K₂.lie_mem hx hy, },
  ..((K₂ : submodule R L₂).comap (f : L →ₗ[R] L₂)), }

section lattice_structure

open set

instance : partial_order (lie_subalgebra R L) :=
{ le := λ N N', ∀ ⦃x⦄, x ∈ N → x ∈ N', -- Overriding `le` like this gives a better defeq.
  ..partial_order.lift (coe : lie_subalgebra R L → set L) coe_injective }

lemma le_def : K ≤ K' ↔ (K : set L) ⊆ K' := iff.rfl

@[simp, norm_cast] lemma coe_submodule_le_coe_submodule : (K : submodule R L) ≤ K' ↔ K ≤ K' :=
iff.rfl

instance : has_bot (lie_subalgebra R L) := ⟨0⟩

@[simp] lemma bot_coe : ((⊥ : lie_subalgebra R L) : set L) = {0} := rfl

@[simp] lemma bot_coe_submodule : ((⊥ : lie_subalgebra R L) : submodule R L) = ⊥ := rfl

@[simp] lemma mem_bot (x : L) : x ∈ (⊥ : lie_subalgebra R L) ↔ x = 0 := mem_singleton_iff

instance : has_top (lie_subalgebra R L) :=
⟨{ lie_mem' := λ x y hx hy, mem_univ ⁅x, y⁆,
   ..(⊤ : submodule R L) }⟩

@[simp] lemma top_coe : ((⊤ : lie_subalgebra R L) : set L) = univ := rfl

@[simp] lemma top_coe_submodule : ((⊤ : lie_subalgebra R L) : submodule R L) = ⊤ := rfl

@[simp] lemma mem_top (x : L) : x ∈ (⊤ : lie_subalgebra R L) := mem_univ x

instance : has_inf (lie_subalgebra R L) :=
⟨λ K K', { lie_mem' := λ x y hx hy, mem_inter (K.lie_mem hx.1 hy.1) (K'.lie_mem hx.2 hy.2),
            ..(K ⊓ K' : submodule R L) }⟩

instance : has_Inf (lie_subalgebra R L) :=
⟨λ S, { lie_mem' := λ x y hx hy, by
        { simp only [submodule.mem_carrier, mem_Inter, submodule.Inf_coe, mem_set_of_eq,
            forall_apply_eq_imp_iff₂, exists_imp_distrib] at *,
          intros K hK, exact K.lie_mem (hx K hK) (hy K hK), },
        ..Inf {(s : submodule R L) | s ∈ S} }⟩

@[simp] theorem inf_coe : (↑(K ⊓ K') : set L) = K ∩ K' := rfl

@[simp] lemma Inf_coe_to_submodule (S : set (lie_subalgebra R L)) :
  (↑(Inf S) : submodule R L) = Inf {(s : submodule R L) | s ∈ S} := rfl

@[simp] lemma Inf_coe (S : set (lie_subalgebra R L)) : (↑(Inf S) : set L) = ⋂ s ∈ S, (s : set L) :=
begin
  rw [← coe_to_submodule, Inf_coe_to_submodule, submodule.Inf_coe],
  ext x,
  simpa only [mem_Inter, mem_set_of_eq, forall_apply_eq_imp_iff₂, exists_imp_distrib],
end

lemma Inf_glb (S : set (lie_subalgebra R L)) : is_glb S (Inf S) :=
begin
  have h : ∀ (K K' : lie_subalgebra R L), (K : set L) ≤ K' ↔ K ≤ K', { intros, exact iff.rfl, },
  simp only [is_glb.of_image h, Inf_coe, is_glb_binfi],
end

/-- The set of Lie subalgebras of a Lie algebra form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`. -/
instance : complete_lattice (lie_subalgebra R L) :=
{ bot          := ⊥,
  bot_le       := λ N _ h, by { rw mem_bot at h, rw h, exact N.zero_mem', },
  top          := ⊤,
  le_top       := λ _ _ _, trivial,
  inf          := (⊓),
  le_inf       := λ N₁ N₂ N₃ h₁₂ h₁₃ m hm, ⟨h₁₂ hm, h₁₃ hm⟩,
  inf_le_left  := λ _ _ _, and.left,
  inf_le_right := λ _ _ _, and.right,
  ..complete_lattice_of_Inf _ Inf_glb }

instance : add_comm_monoid (lie_subalgebra R L) :=
{ add       := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero      := ⊥,
  zero_add  := λ _, bot_sup_eq,
  add_zero  := λ _, sup_bot_eq,
  add_comm  := λ _ _, sup_comm, }

@[simp] lemma add_eq_sup : K + K' = K ⊔ K' := rfl

@[norm_cast, simp] lemma inf_coe_to_submodule :
  (↑(K ⊓ K') : submodule R L) = (K : submodule R L) ⊓ (K' : submodule R L) := rfl

@[simp] lemma mem_inf (x : L) : x ∈ K ⊓ K' ↔ x ∈ K ∧ x ∈ K' :=
by rw [← mem_coe_submodule, ← mem_coe_submodule, ← mem_coe_submodule, inf_coe_to_submodule,
  submodule.mem_inf]

lemma eq_bot_iff : K = ⊥ ↔ ∀ (x : L), x ∈ K → x = 0 :=
by { rw eq_bot_iff, exact iff.rfl, }

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_bot : subsingleton (lie_subalgebra R ↥(⊥ : lie_subalgebra R L)) :=
begin
  apply subsingleton_of_bot_eq_top,
  ext ⟨x, hx⟩, change x ∈ ⊥ at hx, rw submodule.mem_bot at hx, subst hx,
  simp only [true_iff, eq_self_iff_true, submodule.mk_eq_zero, mem_bot],
end

variables (R L)

lemma well_founded_of_noetherian [is_noetherian R L] :
  well_founded ((>) : lie_subalgebra R L → lie_subalgebra R L → Prop) :=
begin
  let f : ((>) : lie_subalgebra R L → lie_subalgebra R L → Prop) →r
          ((>) : submodule R L → submodule R L → Prop) :=
  { to_fun       := coe,
    map_rel' := λ N N' h, h, },
  apply f.well_founded, rw ← is_noetherian_iff_well_founded, apply_instance,
end

variables {R L K K' f}

section nested_subalgebras

variables (h : K ≤ K')

/-- Given two nested Lie subalgebras `K ⊆ K'`, the inclusion `K ↪ K'` is a morphism of Lie
algebras. -/
def hom_of_le : K →ₗ⁅R⁆ K' :=
{ map_lie' := λ x y, rfl,
  ..submodule.of_le h }

@[simp] lemma coe_hom_of_le (x : K) : (hom_of_le h x : L) = x := rfl

lemma hom_of_le_apply (x : K) : hom_of_le h x = ⟨x.1, h x.2⟩ := rfl

lemma hom_of_le_injective : function.injective (hom_of_le h) :=
λ x y, by simp only [hom_of_le_apply, imp_self, subtype.mk_eq_mk, submodule.coe_eq_coe,
  subtype.val_eq_coe]

/-- Given two nested Lie subalgebras `K ⊆ K'`, we can view `K` as a Lie subalgebra of `K'`,
regarded as Lie algebra in its own right. -/
def of_le : lie_subalgebra R K' := (hom_of_le h).range

@[simp] lemma mem_of_le (x : K') : x ∈ of_le h ↔ (x : L) ∈ K :=
begin
  simp only [of_le, hom_of_le_apply, lie_hom.mem_range],
  split,
  { rintros ⟨y, rfl⟩, exact y.property, },
  { intros h, use ⟨(x : L), h⟩, simp, },
end

lemma of_le_eq_comap_incl : of_le h = K.comap K'.incl :=
by { ext, rw mem_of_le, refl, }

end nested_subalgebras

lemma map_le_iff_le_comap {K : lie_subalgebra R L} {K' : lie_subalgebra R L₂} :
  map f K ≤ K' ↔ K ≤ comap f K' := set.image_subset_iff

lemma gc_map_comap : galois_connection (map f) (comap f) := λ K K', map_le_iff_le_comap

end lattice_structure

end lie_subalgebra

end lie_subalgebra

namespace lie_equiv

variables {R : Type u} {L₁ : Type v} {L₂ : Type w}
variables [comm_ring R] [lie_ring L₁] [lie_ring L₂] [lie_algebra R L₁] [lie_algebra R L₂]

/-- An injective Lie algebra morphism is an equivalence onto its range. -/
noncomputable def of_injective (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) :
  L₁ ≃ₗ⁅R⁆ f.range :=
have h' : (f : L₁ →ₗ[R] L₂).ker = ⊥ := linear_map.ker_eq_bot_of_injective h,
{ map_lie' := λ x y, by { apply set_coe.ext, simpa, },
..(linear_equiv.of_injective ↑f h')}

@[simp] lemma of_injective_apply (f : L₁ →ₗ⁅R⁆ L₂) (h : function.injective f) (x : L₁) :
  ↑(of_injective f h x) = f x := rfl

variables (L₁' L₁'' : lie_subalgebra R L₁) (L₂' : lie_subalgebra R L₂)

/-- Lie subalgebras that are equal as sets are equivalent as Lie algebras. -/
def of_eq (h : (L₁' : set L₁) = L₁'') : L₁' ≃ₗ⁅R⁆ L₁'' :=
{ map_lie' := λ x y, by { apply set_coe.ext, simp, },
  ..(linear_equiv.of_eq ↑L₁' ↑L₁''
      (by {ext x, change x ∈ (L₁' : set L₁) ↔ x ∈ (L₁'' : set L₁), rw h, } )) }

@[simp] lemma of_eq_apply (L L' : lie_subalgebra R L₁) (h : (L : set L₁) = L') (x : L) :
  (↑(of_eq L L' h x) : L₁) = x := rfl

variables (e : L₁ ≃ₗ⁅R⁆ L₂)

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebra : L₁'' ≃ₗ⁅R⁆ (L₁''.map e : lie_subalgebra R L₂) :=
{ map_lie' := λ x y, by { apply set_coe.ext, exact lie_hom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, }
  ..(linear_equiv.of_submodule (e : L₁ ≃ₗ[R] L₂) ↑L₁'') }

@[simp] lemma of_subalgebra_apply (x : L₁'') : ↑(e.of_subalgebra _  x) = e x := rfl

/-- An equivalence of Lie algebras restricts to an equivalence from any Lie subalgebra onto its
image. -/
def of_subalgebras (h : L₁'.map ↑e = L₂') : L₁' ≃ₗ⁅R⁆ L₂' :=
{ map_lie' := λ x y, by { apply set_coe.ext, exact lie_hom.map_lie (↑e : L₁ →ₗ⁅R⁆ L₂) ↑x ↑y, },
  ..(linear_equiv.of_submodules (e : L₁ ≃ₗ[R] L₂) ↑L₁' ↑L₂' (by { rw ←h, refl, })) }

@[simp] lemma of_subalgebras_apply (h : L₁'.map ↑e = L₂') (x : L₁') :
  ↑(e.of_subalgebras _ _ h x) = e x := rfl

@[simp] lemma of_subalgebras_symm_apply (h : L₁'.map ↑e = L₂') (x : L₂') :
  ↑((e.of_subalgebras _ _ h).symm x) = e.symm x := rfl

end lie_equiv
