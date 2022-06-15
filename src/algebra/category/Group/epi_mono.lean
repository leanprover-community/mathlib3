/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import category_theory.epi_mono
import group_theory.quotient_group
import algebra.category.Group.basic

/-!
# Monomorphisms and epimorphism in `Group`
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

@[to_additive AddGroup.ker_eq_bot_of_mono]
lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
monoid_hom.ker_eq_bot_of_cancel $ λ u v,
  (@cancel_mono _ _ _ _ _ f _
    (show Group.of f.ker ⟶ A, from u) _).1

@[to_additive AddGroup.mono_iff_ker_eq_bot]
lemma mono_iff_ker_eq_bot :
  mono f ↔ f.ker = ⊥ :=
⟨λ h, @@ker_eq_bot_of_mono f h,
λ h, concrete_category.mono_of_injective _ $ (monoid_hom.ker_eq_bot f).1 h⟩

@[to_additive AddGroup.mono_iff_injective]
lemma mono_iff_injective :
  mono f ↔ function.injective f :=
iff.trans (mono_iff_ker_eq_bot f) $ monoid_hom.ker_eq_bot f

namespace surjective_of_epi_auxs

local notation `X` := set.range (function.swap left_coset f.range.carrier)

/--
Define `X'` to be the set of all right cosets with an extra point at "infinity".
-/
inductive X_with_infinity
| from_coset : set.range (function.swap left_coset f.range.carrier) → X_with_infinity
| infinity : X_with_infinity

open X_with_infinity equiv.perm
open_locale coset

local notation `X'` := X_with_infinity f
local notation `⊙` := X_with_infinity.infinity
local notation `SX'` := equiv.perm X'

noncomputable instance : decidable_eq X' := classical.dec_eq _

/--
Let `τ` be the permutation on `X'` exchanging `f.range` and the point at infinity.
-/
noncomputable def tau : SX' := equiv.swap
(from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) ⊙

local notation `τ` := tau f

lemma τ_apply_infinity :
  τ ⊙ = from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
begin
  dunfold tau,
  rw [equiv.swap_apply_right],
end

lemma τ_apply_from_coset :
  τ (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) = ⊙ :=
begin
  dunfold tau,
  rw [equiv.swap_apply_left],
end

lemma τ_apply_from_coset' (x : B) (hx : x ∈ f.range) :
  τ (from_coset ⟨x *l f.range.carrier, ⟨x, rfl⟩⟩) = ⊙ :=
begin
  convert τ_apply_from_coset _,
  ext b,
  simp only [mem_left_coset_iff, subgroup.mem_carrier, monoid_hom.mem_range],
  rcases hx with ⟨c, rfl⟩,
  split,
  { rintros ⟨a, ha⟩,
    use c * a,
    rw [map_mul, ha, ←mul_assoc, mul_right_inv (f c), one_mul], },
  { rintros ⟨a, rfl⟩,
    use c⁻¹ * a,
    rw [map_mul, map_inv], },
end

lemma τ_symm_apply_from_coset :
  (equiv.symm τ) (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) = ⊙ :=
begin
  dunfold tau,
  rw [equiv.symm_swap, equiv.swap_apply_left],
end

lemma τ_symm_apply_infinity :
  (equiv.symm τ) ⊙ = from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
begin
  dunfold tau,
  rw [equiv.symm_swap, equiv.swap_apply_right],
end

/--
Let `g : B ⟶ S(X')` be defined as as such that, for any `β : B`, `g(β)` is the function sending
point at infinity to point at infinity and sending coset `y` to `β *l y`.
-/
def G : B ⟶ Group.of SX' :=
{ to_fun := λ β,
  { to_fun := λ x,
      match x with
      | from_coset y := from_coset ⟨β *l y, begin
        rcases y.2 with ⟨b, hb⟩,
        rw [subtype.val_eq_coe] at hb,
        rw [←hb, set.mem_range, left_coset_assoc],
        use β * b,
      end⟩
      | ⊙ := ⊙
      end,
    inv_fun := λ x,
      match x with
      | from_coset y := from_coset ⟨β⁻¹ *l y, begin
        rcases y.2 with ⟨b, hb⟩,
        rw [subtype.val_eq_coe] at hb,
        rw [←hb, set.mem_range, left_coset_assoc],
        use β⁻¹ * b,
      end⟩
      | ⊙ := ⊙
      end,
    left_inv := λ x,
      match x with
      | from_coset y := begin
        change from_coset ⟨_, _⟩ = _,
        simp
      end
      | ⊙ := rfl
      end,
    right_inv := λ x,
      match x with
      | from_coset y := begin
        change from_coset _ = _,
        simp
      end
      | ⊙ := rfl
      end },
  map_one' := begin
    ext x,
    rcases x with ⟨⟨_, ⟨y, rfl⟩⟩⟩,
    { simp only [equiv.coe_fn_mk, equiv.perm.coe_one, id.def],
      change from_coset _ = _,
      simp },
    { refl },
  end,
  map_mul' := λ b1 b2, begin
    ext x,
    rcases x with ⟨⟨_, ⟨y, rfl⟩⟩⟩,
    { simp only [equiv.coe_fn_mk, equiv.perm.coe_mul, function.comp_app],
      change from_coset _ = from_coset _,
      simp only [left_coset_assoc, subtype.coe_mk, subtype.mk_eq_mk, mul_assoc], },
    { refl },
  end }

local notation `g` := G f

/--
Define `h : B ⟶ S(X')` to be `τ g τ⁻¹`
-/
noncomputable def H : B ⟶ Group.of SX':=
{ to_fun := λ β, (equiv.trans (equiv.symm τ) (g β)).trans τ,
  map_one' := begin
    ext x,
    simp
  end,
  map_mul' := λ b1 b2, begin
    ext x,
    simp
  end }

local notation `h` := H f

/--
The strategy is the following: assuming `epi f`
* prove that `f.range = {x | h x = g x}`;
* thus `f ≫ h = f ≫ g` so that `h = g`;
* but if `f` is not surjective, then some `x ≠ f.range`, then `h x ≠ g x` at the coset `f.range`.
-/

lemma g_apply_from_coset (x : B) (y : X) :
  (g x).to_fun (from_coset y) =
  from_coset ⟨x *l y, begin
    rcases y.2 with ⟨b, hb⟩,
    rw [subtype.val_eq_coe] at hb,
    rw [←hb, set.mem_range, left_coset_assoc],
    use x * b,
  end⟩ := rfl

lemma g_apply_infinity (x : B) :
  (g x).to_fun ⊙ = ⊙ := rfl

lemma h_apply_infinity (x : B) (hx : x ∈ f.range) :
  (h x).to_fun ⊙ = ⊙ :=
begin
  dunfold H,
  simp only [monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app],
  rw [τ_symm_apply_infinity],
  have := g_apply_from_coset f x ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩,
  rw [equiv.to_fun_as_coe] at this,
  rw this,
  simpa only [←subtype.val_eq_coe] using τ_apply_from_coset' f x hx,
end

lemma h_apply_from_coset (x : B) :
  (h x).to_fun (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
  from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩ :=
begin
  dunfold H,
  simp only [monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app],
  rw [τ_symm_apply_from_coset],
  have := g_apply_infinity f x,
  rw [equiv.to_fun_as_coe] at this,
  rw [this, τ_apply_infinity],
end

lemma h_apply_from_coset' (x : B) (b : B) (hb : b ∈ f.range):
  (h x).to_fun (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
  from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩ :=
begin
  have eq1 : b *l (monoid_hom.range f).carrier = (monoid_hom.range f).carrier,
  { rcases hb with ⟨a, rfl⟩,
    ext y,
    simp only [mem_left_coset_iff, subgroup.mem_carrier, monoid_hom.mem_range],
    split,
    { rintros ⟨a', ha'⟩,
      use a * a',
      rw [map_mul, ha', ←mul_assoc, mul_right_inv, one_mul], },
    { rintros ⟨a', rfl⟩,
      use a⁻¹ * a',
      rw [map_mul, map_inv], }, },
  convert h_apply_from_coset f x,
end

lemma h_apply_from_coset_nin_range (x : B) (hx : x ∈ f.range) (b : B) (hb : b ∉ f.range) :
  (h x).to_fun (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) =
  from_coset ⟨(x * b) *l f.range.carrier, ⟨x * b, rfl⟩⟩ :=
begin
  dunfold H tau,
  simp only [monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app],
  rw [equiv.symm_swap],
  rw @equiv.swap_apply_of_ne_of_ne X' _
    (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) ⊙
    (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩) begin
      intro r,
      simp only [subtype.mk_eq_mk] at r,
      change b *l f.range = f.range at r,
      have eq1 : (f.range : set B) = 1 *l f.range,
      { rw one_left_coset, },
      conv_rhs at r { rw eq1 },
      rw [left_coset_eq_iff, mul_one] at r,
      apply hb,
      replace r : b⁻¹⁻¹ ∈ f.range := subgroup.inv_mem _ r,
      rwa [inv_inv] at r,
    end begin
      simp only [ne.def, not_false_iff],
    end,
  have := g_apply_from_coset f x,
  rw [equiv.to_fun_as_coe] at this,
  rw this,
  clear this,
  simp only [←subtype.val_eq_coe, left_coset_assoc],
  refine equiv.swap_apply_of_ne_of_ne begin
    intro r,
    simp only [subtype.mk_eq_mk] at r,
    change x * b *l f.range = f.range at r,
    have eq1 : (f.range : set B) = 1 *l f.range,
    { rw one_left_coset, },
    conv_rhs at r { rw eq1 },
    rw [left_coset_eq_iff, mul_one] at r,
    replace r : (x * b)⁻¹⁻¹ ∈ f.range := subgroup.inv_mem _ r,
    rw inv_inv at r,
    apply hb,
    replace hx : x⁻¹ ∈ f.range := subgroup.inv_mem _ hx,
    have := subgroup.mul_mem _ hx r,
    rwa [←mul_assoc, mul_left_inv, one_mul] at this,
  end begin
    simp only [ne.def, not_false_iff],
  end,
end

lemma agree :
  f.range.carrier = {x | h x = g x} :=
begin
  ext b,
  split,
  { rintros ⟨a, rfl⟩,
    change h (f a) = g (f a),
    ext,
    rcases x with ⟨⟨_, ⟨y, rfl⟩⟩⟩,
    { have := g_apply_from_coset f (f a),
      rw [equiv.to_fun_as_coe] at this,
      rw this,
      clear this,
      by_cases m : y ∈ f.range,
      { have := h_apply_from_coset' f (f a) y m,
        rw [equiv.to_fun_as_coe] at this,
        simp only [this, ←subtype.val_eq_coe],
        congr' 1,
        change y *l f.range = f a *l (y *l f.range),
        rw [left_coset_assoc, left_coset_eq_iff],
        refine subgroup.mul_mem _ (subgroup.inv_mem _ m)
          (subgroup.mul_mem _ ⟨a, rfl⟩ m), },
      { have := h_apply_from_coset_nin_range f (f a) ⟨a, rfl⟩ y m,
        rw [equiv.to_fun_as_coe] at this,
        rw this,
        clear this,
        simp only [←subtype.val_eq_coe, left_coset_assoc],
        refl, }, },
    { have := g_apply_infinity f (f a),
      rw [equiv.to_fun_as_coe] at this,
      rw this,
      clear this,
      have := h_apply_infinity f (f a) ⟨a, rfl⟩,
      simpa only [equiv.to_fun_as_coe] using this, }, },
  { rintros (hb : h b = g b),
    have eq1 : (h b).to_fun (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
      (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩),
    { dunfold H tau,
      simp only [equiv.symm_swap, monoid_hom.coe_mk, equiv.to_fun_as_coe, equiv.coe_trans,
        function.comp_app, equiv.swap_apply_left],
      have := g_apply_infinity f b,
      rw [equiv.to_fun_as_coe] at this,
      rw [this, equiv.swap_apply_right], },
    have eq2 : (g b).to_fun (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
      (from_coset ⟨b *l f.range.carrier, ⟨b, rfl⟩⟩),
    { unfold G,
      simp only [monoid_hom.coe_mk],
      change from_coset _ = _,
      refl, },
    have eq3 : (h b).to_fun (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩) =
      (g b).to_fun (from_coset ⟨f.range.carrier, ⟨1, one_left_coset _⟩⟩),
    { simp only [equiv.to_fun_as_coe, hb], },
    rw [eq1, eq2] at eq3,
    simp only [subtype.mk_eq_mk] at eq3,
    change (f.range : set B) = b *l f.range at eq3,
    rwa [show (f.range : set B) = 1 *l f.range, by rw one_left_coset _,
      left_coset_assoc, left_coset_eq_iff, inv_one, one_mul, mul_one] at eq3 }
end

lemma comp_eq : f ≫ g = f ≫ h :=
begin
  ext1 a,
  rw [comp_apply, comp_apply],
  have : f a ∈ f.range.carrier := ⟨a, rfl⟩,
  rw agree at this,
  simp only [set.mem_set_of_eq] at this,
  rw this,
end

lemma g_eq_h [epi f] : g = h :=
(cancel_epi f).1 $ comp_eq f

lemma g_ne_h (x : B) (hx : x ∉ f.range) :
  g ≠ h :=
begin
  intros r,
  replace r : ∀ a, (g x).to_fun a = (h x).to_fun a,
  { intros a,
    simp only [equiv.to_fun_as_coe, r], },
  specialize r (from_coset ⟨f.range, ⟨1, one_left_coset _⟩⟩),
  rw [H, g_apply_from_coset, monoid_hom.coe_mk, tau] at r,
  simp only [monoid_hom.coe_range, subtype.coe_mk, equiv.symm_swap,
    equiv.to_fun_as_coe, equiv.coe_trans, function.comp_app] at r,
  generalize_proofs h1 h2 at r,
  rw [show from_coset ⟨set.range f, h2⟩ = from_coset ⟨f.range.carrier, h2⟩,
    by simpa only [subtype.mk_eq_mk], equiv.swap_apply_left] at r,
  have := g_apply_infinity f x,
  rw [equiv.to_fun_as_coe] at this,
  rw [this, equiv.swap_apply_right] at r,
  clear this,
  simp only [subtype.mk_eq_mk] at r,
  change x *l f.range = f.range at r,
  rw [show (f.range : set B) = 1 *l f.range, from (one_left_coset _).symm,
    left_coset_assoc, mul_one, left_coset_eq_iff, mul_one] at r,
  replace r := subgroup.inv_mem _ r,
  rw inv_inv at r,
  exact hx r,
end

end surjective_of_epi_auxs

lemma surjective_of_epi [epi f] : function.surjective f :=
begin
  by_contra r,
  simp_rw [not_forall, not_exists] at r,
  rcases r with ⟨b, hb⟩,
  refine surjective_of_epi_auxs.g_ne_h f b (λ r, _) _,
  { rcases r with ⟨c, hc⟩,
    exact hb _ hc, },
  apply surjective_of_epi_auxs.g_eq_h,
end

lemma epi_iff_surjective :
  epi f ↔ function.surjective f :=
⟨λ h, @@surjective_of_epi f h, concrete_category.epi_of_surjective _⟩

lemma epi_iff_range_eq_top :
  epi f ↔ f.range = ⊤ :=
iff.trans (epi_iff_surjective _) (subgroup.eq_top_iff' f.range).symm

end Group


end
