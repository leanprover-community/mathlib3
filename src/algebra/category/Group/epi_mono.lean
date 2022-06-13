/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import category_theory.epi_mono
import group_theory.quotient_group
import algebra.category.Group.basic

/-!
# Monomorphisms and epimorphism in `Group` and `CommGroup`
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/


universes u

namespace monoid_hom

open quotient_group

variables {A B : Type u}

section

variables [group A] [group B]

@[to_additive add_monoid_hom.ker_eq_bot]
lemma ker_eq_bot (f : A →* B) :
  f.ker = ⊥ ↔ function.injective f :=
{ mp := λ h1 x y h2, begin
    rw [←div_eq_one, ←map_div, ←mem_ker] at h2,
    rwa [h1, subgroup.mem_bot, div_eq_one] at h2,
  end,
  mpr := λ h, set_like.ext $ λ x, iff.trans (mem_ker _) $
    iff.trans begin
      rw ←(by rw map_one : f x = f 1 ↔ f x = 1),
      exact ⟨λ h', h h', λ h, h ▸ rfl⟩,
    end subgroup.mem_bot.symm }

@[to_additive add_monoid_hom.range_eq_top]
lemma range_eq_top (f : A →* B) :
  f.range = ⊤ ↔ function.surjective f :=
{ mp := λ h x, begin
    rcases show x ∈ f.range, from h.symm ▸ subgroup.mem_top _ with ⟨a, h⟩,
    exact ⟨a, h⟩,
  end,
  mpr := λ h, set_like.ext $ λ x, iff.trans mem_range
    ⟨λ _, trivial, λ _, h x⟩ }

@[to_additive add_monoid_hom.range_zero_eq_bot]
lemma range_one_eq_bot :
  (1 : A →* B).range = ⊥ :=
set_like.ext $ λ a, iff.trans monoid_hom.mem_range $
  iff.trans (by simp only [one_apply, exists_const]; split; intros h; subst h)
    subgroup.mem_bot.symm
@[to_additive add_monoid_hom.ker_zero_eq_top]
lemma ker_one_eq_top :
  (1 : A →* B).ker = ⊤ :=
set_like.ext $ λ a, iff.trans (monoid_hom.mem_ker _) $ by simp

@[to_additive add_monoid_hom.ker_eq_bot_of_cancel]
lemma ker_eq_bot_of_cancel {f : A →* B}
  (h : ∀ (u v : f.ker →* A), f.comp u = f.comp v → u = v) :
  f.ker = (⊥ : subgroup A) :=
begin
  specialize h 1 f.ker.subtype begin
    ext1,
    simp only [comp_one, one_apply, coe_comp, subgroup.coe_subtype, function.comp_app],
    rw [←subtype.val_eq_coe, f.mem_ker.mp x.2],
  end,
  rw [←subgroup.subtype_range f.ker, ←h, range_one_eq_bot],
end

end

section

variables [comm_group A] [comm_group B]

@[to_additive add_monoid_hom.range_eq_top_of_cancel]
lemma range_eq_top_of_cancel {f : A →* B}
  (h : ∀ (u v : B →* B ⧸ f.range), u.comp f = v.comp f → u = v) :
  f.range = ⊤ :=
begin
  specialize h 1 (quotient_group.mk' _) begin
    ext1,
    simp only [one_apply, coe_comp, coe_mk', function.comp_app],
    rw [show (1 : B ⧸ f.range) = (1 : B), from quotient_group.coe_one _, quotient_group.eq, inv_one,
      one_mul],
    exact ⟨x, rfl⟩,
  end,
  replace h : (quotient_group.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by rw h,
  rwa [ker_one_eq_top, quotient_group.ker_mk] at h,
end

end

end monoid_hom

section

open category_theory

namespace Group

variables {A B : Group.{u}} (f : A ⟶ B)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
monoid_hom.ker_eq_bot_of_cancel $ λ u v,
  (@cancel_mono _ _ _ _ _ f _
    (show Group.of f.ker ⟶ A, from u) _).1

lemma mono_iff_ker_eq_bot :
  mono f ↔ f.ker = ⊥ :=
⟨λ h, @@ker_eq_bot_of_mono f h,
λ h, concrete_category.mono_of_injective _ $ (monoid_hom.ker_eq_bot f).1 h⟩

lemma mono_iff_injective :
  mono f ↔ function.injective f :=
iff.trans (mono_iff_ker_eq_bot f) $ monoid_hom.ker_eq_bot f

end Group

namespace CommGroup

variables {A B : CommGroup.{u}} (f : A ⟶ B)

@[to_additive AddCommGroup.range_eq_top_of_epi]
lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
monoid_hom.range_eq_top_of_cancel $ λ u v,
  (@cancel_epi _ _ _ _ _ f _
    (show CommGroup.of B ⟶ CommGroup.of (B ⧸ f.range), from u) _).1

@[to_additive AddCommGroup.epi_iff_range_eq_top]
lemma epi_iff_range_eq_top :
  epi f ↔ f.range = ⊤ :=
⟨λ h, @@range_eq_top_of_epi f h,
λ h, concrete_category.epi_of_surjective _ $ (monoid_hom.range_eq_top f).1 h⟩

@[to_additive AddCommGroup.epi_iff_surjective]
lemma epi_iff_surjective :
  epi f ↔ function.surjective f :=
iff.trans (epi_iff_range_eq_top f) $ monoid_hom.range_eq_top f

end CommGroup

end
