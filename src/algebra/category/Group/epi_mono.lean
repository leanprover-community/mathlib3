/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Group.equivalence_Group_AddGroup
import group_theory.quotient_group

/-!
# Monomorphisms and epimorphisms in `Group`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
In this file, we prove monomorphisms in category of group are injective homomorphisms and
epimorphisms are surjective homomorphisms.
-/

noncomputable theory

universes u v

namespace monoid_hom

open quotient_group

variables {A : Type u} {B : Type v}

section
variables [group A] [group B]

@[to_additive add_monoid_hom.ker_eq_bot_of_cancel]
lemma ker_eq_bot_of_cancel {f : A →* B} (h : ∀ (u v : f.ker →* A), f.comp u = f.comp v → u = v) :
  f.ker = ⊥ :=
by simpa using _root_.congr_arg range (h f.ker.subtype 1 (by tidy))

end

section
variables [comm_group A] [comm_group B]

@[to_additive add_monoid_hom.range_eq_top_of_cancel]
lemma range_eq_top_of_cancel {f : A →* B}
  (h : ∀ (u v : B →* B ⧸ f.range), u.comp f = v.comp f → u = v) :
  f.range = ⊤ :=
begin
  specialize h 1 (quotient_group.mk' _) _,
  { ext1,
    simp only [one_apply, coe_comp, coe_mk', function.comp_app],
    rw [show (1 : B ⧸ f.range) = (1 : B), from quotient_group.coe_one _, quotient_group.eq,
     inv_one, one_mul],
    exact ⟨x, rfl⟩, },
  replace h : (quotient_group.mk' _).ker = (1 : B →* B ⧸ f.range).ker := by rw h,
  rwa [ker_one, quotient_group.ker_mk] at h,
end

end

end monoid_hom

section

open category_theory

namespace Group

variables {A B : Group.{u}} (f : A ⟶ B)

@[to_additive AddGroup.ker_eq_bot_of_mono]
lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
monoid_hom.ker_eq_bot_of_cancel $ λ u v,
  (@cancel_mono _ _ _ _ _ f _ (show Group.of f.ker ⟶ A, from u) _).1

@[to_additive AddGroup.mono_iff_ker_eq_bot]
lemma mono_iff_ker_eq_bot : mono f ↔ f.ker = ⊥ :=
⟨λ h, @@ker_eq_bot_of_mono f h,
 λ h, concrete_category.mono_of_injective _ $ (monoid_hom.ker_eq_bot_iff f).1 h⟩

@[to_additive AddGroup.mono_iff_injective]
lemma mono_iff_injective : mono f ↔ function.injective f :=
iff.trans (mono_iff_ker_eq_bot f) $ monoid_hom.ker_eq_bot_iff f

namespace surjective_of_epi_auxs

local notation `X` := set.range (function.swap left_coset f.range.carrier)

/--
Define `X'` to be the set of all left cosets with an extra point at "infinity".
-/
@[nolint has_nonempty_instance]
inductive X_with_infinity
| from_coset : set.range (function.swap left_coset f.range.carrier) → X_with_infinity
| infinity : X_with_infinity

open X_with_infinity equiv.perm
open_locale coset

local notation `X'` := X_with_infinity f
local notation `∞` := X_with_infinity.infinity
local notation `SX'` := equiv.perm X'

instance : has_smul B X' :=
{ smul := λ b x, match x with
  | from_coset y := from_coset ⟨b *l y,
    begin
      rw [←subtype.val_eq_coe, ←y.2.some_spec, left_coset_assoc],
      use b * y.2.some,
    end⟩
  | ∞ := ∞
  end }

lemma mul_smul (b b' : B) (x : X') : (b * b') • x = b • b' • x :=
match x with
| from_coset y :=
  begin
    change from_coset _ = from_coset _,
    simp only [←subtype.val_eq_coe, left_coset_assoc],
  end
| ∞ := rfl
end

lemma one_smul (x : X') : (1 : B) • x = x :=
match x with
| from_coset y :=
  begin
    change from_coset _ = from_coset _,
    simp only [←subtype.val_eq_coe, one_left_coset, subtype.ext_iff_val],
  end
| ∞ := rfl
end

lemma from_coset_eq_of_mem_range {b : B} (hb : b ∈ f.range) :
  from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ =
  from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
begin
  congr,
  change b *l f.range = f.range,
  nth_rewrite 1 [show (f.range : set B) = 1 *l f.range, from (one_left_coset _).symm],
  rw [left_coset_eq_iff, mul_one],
  exact subgroup.inv_mem _ hb,
end

lemma from_coset_ne_of_nin_range {b : B} (hb : b ∉ f.range) :
  from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ ≠
  from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
begin
  intros r,
  simp only [subtype.mk_eq_mk] at r,
  change b *l f.range = f.range at r,
  nth_rewrite 1 [show (f.range : set B) = 1 *l f.range, from (one_left_coset _).symm] at r,
  rw [left_coset_eq_iff, mul_one] at r,
  exact hb (inv_inv b ▸ (subgroup.inv_mem _ r)),
end

instance : decidable_eq X' := classical.dec_eq _

/--
Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' :=
equiv.swap (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) ∞

local notation `τ` := tau f

lemma τ_apply_infinity :
  τ ∞ = from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
equiv.swap_apply_right _ _

lemma τ_apply_from_coset :
  τ (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) = ∞ :=
equiv.swap_apply_left _ _

lemma τ_apply_from_coset' (x : B) (hx : x ∈ f.range) :
  τ (from_coset ⟨x *l f.range.carrier, ⟨x, rfl⟩⟩) = ∞ :=
(from_coset_eq_of_mem_range _ hx).symm ▸ τ_apply_from_coset _

lemma τ_symm_apply_from_coset :
  (equiv.symm τ) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) = ∞ :=
by rw [tau, equiv.symm_swap, equiv.swap_apply_left]

lemma τ_symm_apply_infinity :
  (equiv.symm τ) ∞ = from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
by rw [tau, equiv.symm_swap, equiv.swap_apply_right]

/--
Let `g : B ⟶ S(X')` be defined as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β *l y`.
-/
def G : B →* SX' :=
{ to_fun := λ β,
  { to_fun := λ x, β • x,
    inv_fun := λ x, β⁻¹ • x,
    left_inv := λ x, by { dsimp only, rw [←mul_smul, mul_left_inv, one_smul] },
    right_inv := λ x, by { dsimp only, rw [←mul_smul, mul_right_inv, one_smul] } },
  map_one' := by { ext, simp [one_smul] },
  map_mul' := λ b1 b2, by { ext, simp [mul_smul] } }

local notation `g` := G f

/--
Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
def H : B →* SX':=
{ to_fun := λ β, ((τ).symm.trans (g β)).trans τ,
  map_one' := by { ext, simp },
  map_mul' := λ b1 b2, by { ext, simp } }

local notation `h` := H f

/-!
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ∉ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/

lemma g_apply_from_coset (x : B) (y : X) : (g x) (from_coset y) = from_coset ⟨x *l y, by tidy⟩ :=
rfl

lemma g_apply_infinity (x : B) : (g x) ∞ = ∞ := rfl

lemma h_apply_infinity (x : B) (hx : x ∈ f.range) : (h x) ∞ = ∞ :=
begin
  simp only [H, monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app],
  rw [τ_symm_apply_infinity, g_apply_from_coset],
  simpa only [←subtype.val_eq_coe] using τ_apply_from_coset' f x hx,
end

lemma h_apply_from_coset (x : B) :
  (h x) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
  from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
by simp [H, τ_symm_apply_from_coset, g_apply_infinity, τ_apply_infinity]

lemma h_apply_from_coset' (x : B) (b : B) (hb : b ∈ f.range):
  (h x) (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
  from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
(from_coset_eq_of_mem_range _ hb).symm ▸ h_apply_from_coset f x

lemma h_apply_from_coset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
  (h x) (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
  from_coset ⟨(x * b) *l f.range.carrier, ⟨x * b, rfl⟩⟩ :=
begin
  simp only [H, tau, monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app],
  rw [equiv.symm_swap, @equiv.swap_apply_of_ne_of_ne X' _
    (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) ∞
    (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) (from_coset_ne_of_nin_range _ hb) (by simp)],
  simp only [g_apply_from_coset, ←subtype.val_eq_coe, left_coset_assoc],
  refine equiv.swap_apply_of_ne_of_ne (from_coset_ne_of_nin_range _ (λ r, hb _)) (by simp),
  convert subgroup.mul_mem _ (subgroup.inv_mem _ hx) r,
  rw [←mul_assoc, mul_left_inv, one_mul],
end

lemma agree : f.range.carrier = {x | h x = g x} :=
begin
  refine set.ext (λ b, ⟨_, λ (hb : h b = g b), classical.by_contradiction (λ r, _)⟩),
  { rintros ⟨a, rfl⟩,
    change h (f a) = g (f a),
    ext ⟨⟨_, ⟨y, rfl⟩⟩⟩,
    { rw [g_apply_from_coset],
      by_cases m : y ∈ f.range,
      { rw [h_apply_from_coset' _ _ _ m, from_coset_eq_of_mem_range _ m],
        change from_coset _ = from_coset ⟨f a *l (y *l _), _⟩,
        simpa only [←from_coset_eq_of_mem_range _ (subgroup.mul_mem _ ⟨a, rfl⟩ m),
          left_coset_assoc] },
      { rw [h_apply_from_coset_nin_range _ _ ⟨_, rfl⟩ _ m],
        simpa only [←subtype.val_eq_coe, left_coset_assoc], }, },
    { rw [g_apply_infinity, h_apply_infinity _ _ ⟨_, rfl⟩], } },
  { have eq1 : (h b) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
      (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) := by simp [H, tau, g_apply_infinity],
    have eq2 : (g b) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
      (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) := rfl,
    exact (from_coset_ne_of_nin_range _ r).symm (by rw [←eq1, ←eq2, fun_like.congr_fun hb]) }
end

lemma comp_eq : f ≫ (show B ⟶ Group.of SX', from g) = f ≫ h :=
fun_like.ext _ _ $ λ a,
  by simp only [comp_apply, show h (f a) = _, from (by simp [←agree] : f a ∈ {b | h b = g b})]

lemma g_ne_h (x : B) (hx : x ∉ f.range) : g ≠ h :=
begin
  intros r,
  replace r := fun_like.congr_fun (fun_like.congr_fun r x)
    ((from_coset ⟨f.range, ⟨1, one_left_coset _⟩⟩)),
  rw [H, g_apply_from_coset, monoid_hom.coe_mk, tau] at r,
  simp only [monoid_hom.coe_range, subtype.coe_mk, equiv.symm_swap,
    equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app] at r,
  erw [equiv.swap_apply_left, g_apply_infinity, equiv.swap_apply_right] at r,
  exact from_coset_ne_of_nin_range _ hx r,
end

end surjective_of_epi_auxs

lemma surjective_of_epi [epi f] : function.surjective f :=
begin
  by_contra r,
  push_neg at r,
  rcases r with ⟨b, hb⟩,
  exact surjective_of_epi_auxs.g_ne_h f b (λ ⟨c, hc⟩, hb _ hc)
    ((cancel_epi f).1 (surjective_of_epi_auxs.comp_eq f)),
end

lemma epi_iff_surjective : epi f ↔ function.surjective f :=
⟨λ h, @@surjective_of_epi f h, concrete_category.epi_of_surjective _⟩

lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
iff.trans (epi_iff_surjective _) (subgroup.eq_top_iff' f.range).symm

end Group

namespace AddGroup
variables {A B : AddGroup.{u}} (f : A ⟶ B)

lemma epi_iff_surjective : epi f ↔ function.surjective f :=
begin
  have i1 : epi f ↔ epi (Group_AddGroup_equivalence.inverse.map f),
  { refine ⟨_, Group_AddGroup_equivalence.inverse.epi_of_epi_map⟩,
    introsI e',
    apply Group_AddGroup_equivalence.inverse.map_epi },
  rwa Group.epi_iff_surjective at i1,
end

lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
iff.trans (epi_iff_surjective _) (add_subgroup.eq_top_iff' f.range).symm

end AddGroup

namespace Group
variables {A B : Group.{u}} (f : A ⟶ B)

@[to_additive]
instance forget_Group_preserves_mono : (forget Group).preserves_monomorphisms :=
{ preserves := λ X Y f e, by rwa [mono_iff_injective, ←category_theory.mono_iff_injective] at e }

@[to_additive]
instance forget_Group_preserves_epi : (forget Group).preserves_epimorphisms :=
{ preserves := λ X Y f e, by rwa [epi_iff_surjective, ←category_theory.epi_iff_surjective] at e }

end Group

namespace CommGroup
variables {A B : CommGroup.{u}} (f : A ⟶ B)

@[to_additive AddCommGroup.ker_eq_bot_of_mono]
lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
monoid_hom.ker_eq_bot_of_cancel $ λ u v,
  (@cancel_mono _ _ _ _ _ f _ (show CommGroup.of f.ker ⟶ A, from u) _).1

@[to_additive AddCommGroup.mono_iff_ker_eq_bot]
lemma mono_iff_ker_eq_bot : mono f ↔ f.ker = ⊥ :=
⟨λ h, @@ker_eq_bot_of_mono f h,
 λ h, concrete_category.mono_of_injective _ $ (monoid_hom.ker_eq_bot_iff f).1 h⟩

@[to_additive AddCommGroup.mono_iff_injective]
lemma mono_iff_injective : mono f ↔ function.injective f :=
iff.trans (mono_iff_ker_eq_bot f) $ monoid_hom.ker_eq_bot_iff f

@[to_additive]
lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
monoid_hom.range_eq_top_of_cancel $ λ u v h,
  (@cancel_epi _ _ _ _ _ f _ (show B ⟶ ⟨B ⧸ monoid_hom.range f⟩, from u) v).1 h

@[to_additive]
lemma epi_iff_range_eq_top : epi f ↔ f.range = ⊤ :=
⟨λ hf, by exactI range_eq_top_of_epi _,
 λ hf, concrete_category.epi_of_surjective _ $ monoid_hom.range_top_iff_surjective.mp hf⟩

@[to_additive]
lemma epi_iff_surjective : epi f ↔ function.surjective f :=
by rw [epi_iff_range_eq_top, monoid_hom.range_top_iff_surjective]

@[to_additive]
instance forget_CommGroup_preserves_mono : (forget CommGroup).preserves_monomorphisms :=
{ preserves := λ X Y f e, by rwa [mono_iff_injective, ←category_theory.mono_iff_injective] at e }

@[to_additive]
instance forget_CommGroup_preserves_epi : (forget CommGroup).preserves_epimorphisms :=
{ preserves := λ X Y f e, by rwa [epi_iff_surjective, ←category_theory.epi_iff_surjective] at e }

end CommGroup

end
