/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.direct_limit
import model_theory.finitely_generated


/-!
# Fraïssé Limits of First-Order Structures
This file defines Fraïssé classes and Fraïssé limits and proves that each Fraïssé class has a unique
Fraïssé limit.

## Main Definitions
*

-/

open_locale first_order
open set

namespace first_order
namespace language
open Structure

variables {L : language} {M : Type*} [L.Structure M]

def weakly_homogeneous : Prop := ∀ (s t : L.substructure M) (f : s ↪[L] M) (h : s ≤ t),
  t.fg → ∃ (g : t ↪[L] M), g.comp (substructure.inclusion h) = f

variables (L) (M)

def age : {S : L.substructure M // S.fg} → Type* := λ (S : {S : L.substructure M // S.fg}), ↥S

instance age_structure (S) : L.Structure (L.age M S) :=
(infer_instance : L.Structure S)

def equiv_age (s : L.substructure M) (hs : s.fg) : s ≃[L] L.age M ⟨s, hs⟩ :=
equiv.refl L s

variables {M} {ι : Type*} (K : ι → Type*) [Π i, L.Structure (K i)]

def hereditary_property : Prop :=
∀ (i : ι) (S : L.substructure (K i)), S.fg → ∃ (j : ι), nonempty (K j ≃[L] S)

def joint_embedding_property : Prop :=
∀ (i j : ι), ∃ (k : ι), nonempty (K i ↪[L] K k) ∧ nonempty (K j ↪[L] K k)

def amalgamation_property : Prop :=
∀ (i j k : ι) (f : K i ↪[L] K j) (g : K i ↪[L] K k),
  ∃ (l : ι) (f' : K j ↪[L] K l) (g' : K k ↪[L] K l), f'.comp f = g'.comp g

def essential_countability : Prop :=
∃ (S : set ι), countable S ∧ ∀ (i : ι), ∃ j ∈ S, nonempty (K i ≃[L] K j)

class fraisse_class :=
(hp : L.hereditary_property K)
(jep : L.joint_embedding_property K)
(ap : L.amalgamation_property K)
(ec : L.essential_countability K)
(fg : ∀ i, Structure.fg L (K i))

variable (M)

def extension_property : Prop := ∀ i j (f₀ : K i ↪[L] M) (f₁ : K i ↪[L] K j),
  ∃ (g : K j ↪[L] M), g.comp f₁ = f₀

class is_age : Prop :=
(fg' : ∀ i, Structure.fg L (K i))
( exists_equiv_of_fg' : ∀ (s : L.substructure M) (hs : s.fg), ∃ i, nonempty (K i ≃[L] s))
(exists_equiv_substructure' : ∀ i, ∃ (s : L.substructure M), nonempty (K i ≃[L] s))

variables {L} {K}

lemma fg_age (i) : Structure.fg L (L.age M i) := (substructure.fg_iff_Structure_fg _).1 i.2

lemma hp_age : L.hereditary_property (L.age M) :=
λ ⟨i, hi⟩ s hs, ⟨⟨s.map i.subtype.to_hom, hs.map _⟩, ⟨(i.subtype.substructure_equiv_map s).symm⟩⟩

lemma jep_age : L.joint_embedding_property (L.age M) :=
λ ⟨i, hi⟩ ⟨j, hj⟩, ⟨⟨i ⊔ j, fg_sup hi hj⟩, ⟨substructure.inclusion le_sup_left⟩,
  ⟨substructure.inclusion le_sup_right⟩⟩

instance : is_age L M (L.age M) :=
{ fg' := fg_age M,
  exists_equiv_of_fg' := λ s hs, ⟨⟨s, hs⟩, ⟨equiv.refl L s⟩⟩,
  exists_equiv_substructure' := λ i, ⟨i, ⟨equiv.refl L i⟩⟩  }

namespace is_age

variables (L K M) [L.is_age M K]

lemma fg : ∀ i, Structure.fg L (K i) := fg' M

lemma exists_equiv_of_fg (s : L.substructure M) (hs : s.fg) : ∃ i, nonempty (K i ≃[L] s) :=
   exists_equiv_of_fg' s hs

lemma exists_equiv_substructure (i) : ∃ (s : L.substructure M), nonempty (K i ≃[L] s) :=
  exists_equiv_substructure' i

lemma exists_equiv_fg_substructure (i) : ∃ (s : L.substructure M), s.fg ∧ nonempty (K i ≃[L] s) :=
begin
  obtain ⟨s, ⟨fs⟩⟩ := exists_equiv_substructure L M K i,
  exact ⟨s, s.fg_iff_Structure_fg.2 (fs.fg_iff.1 (fg L M K i)), ⟨fs⟩⟩
end

include M

lemma hp : L.hereditary_property K :=
λ i s hs, begin
  obtain ⟨S, ⟨fS⟩⟩ := exists_equiv_substructure L M K i,
  obtain ⟨j, ⟨fj⟩⟩ := exists_equiv_of_fg L M K ((s.map fS.to_hom).map S.subtype.to_hom)
    ((hs.map _).map _),
  have f := (S.subtype.comp fS.to_embedding).substructure_equiv_map s,
  rw [embedding.comp_to_hom, ← map_map, equiv.to_embedding_to_hom] at f,
  exact ⟨j, ⟨f.symm.comp fj⟩⟩,
end

lemma jep : L.joint_embedding_property K :=
λ i j, begin
  obtain ⟨Si, Sifg, ⟨fSi⟩⟩ := exists_equiv_fg_substructure L M K i,
  obtain ⟨Sj, Sjfg, ⟨fSj⟩⟩ := exists_equiv_fg_substructure L M K j,
  obtain ⟨k, ⟨fk⟩⟩ :=  exists_equiv_of_fg L M K (Si ⊔ Sj) (fg_sup Sifg Sjfg),
  exact ⟨k, ⟨fk.symm.to_embedding.comp (embedding.comp (substructure.inclusion le_sup_left)
    fSi.to_embedding)⟩, ⟨fk.symm.to_embedding.comp
    (embedding.comp (substructure.inclusion le_sup_right) fSj.to_embedding)⟩⟩,
end

end is_age

variables (L M K)

class is_saturating_age [is_age L M K] : Prop :=
(ep : extension_property L M K)

namespace is_saturating_age

open is_age

variables [is_age L M K] [is_saturating_age L M K]

include M

lemma ap : amalgamation_property L K :=
λ i j k fij fik, begin
  obtain ⟨si, sifg, ⟨fsi⟩⟩ := exists_equiv_fg_substructure L M K i,
  obtain ⟨sj, sjfg, ⟨fsj⟩⟩ := exists_equiv_fg_substructure L M K j,
  obtain ⟨sk, skfg, ⟨fsk⟩⟩ := exists_equiv_fg_substructure L M K k,
  obtain ⟨gk, hgk⟩ := ep i k ((sj.subtype.comp fsj.to_embedding).comp fij) fik,
  have Sfg : (sj ⊔ gk.to_hom.range).fg,
  { refine fg_sup sjfg _,
    rw [hom.range_eq_map],
    exact (Structure.fg_def.1 (is_age.fg L M K k)).map _ },
  obtain ⟨l, ⟨fl⟩⟩ := exists_equiv_of_fg L M K _ Sfg,
  refine ⟨l, fl.symm.to_embedding.comp ((substructure.inclusion _).comp fsj.to_embedding),
    fl.symm.to_embedding.comp (gk.cod_restrict (sj ⊔ gk.to_hom.range)
      (λ c, (set_like.coe_subset_coe.2 le_sup_right) (gk.to_hom.mem_range_self c))), _⟩,
  { exact le_sup_left },
  { ext x,
    have hgkx := (embedding.ext_iff.1 hgk) x,
    simp only [embedding.comp_apply, equiv.coe_to_embedding, substructure.coe_subtype] at hgkx,
    simp only [embedding.comp_apply, equiv.coe_to_embedding, substructure.coe_inclusion],
    refine congr rfl (subtype.coe_injective _),
    simp only [hgkx, set.coe_inclusion, embedding.cod_restrict_apply] }
end

end is_saturating_age




end language
end first_order
