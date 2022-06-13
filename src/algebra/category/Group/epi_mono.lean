import category_theory.epi_mono
import algebra.category.Group.basic

namespace monoid_hom

universes u

variables {A B : Type u} [group A] [group B]

@[to_additive add_monoid_hom.range_zero_eq_bot]
lemma range_one_eq_bot :
  (1 : A →* B).range = ⊥ :=
set_like.ext $ λ a, iff.trans monoid_hom.mem_range $
  iff.trans (by simp only [one_apply, exists_const]; split; intros h; subst h)
    subgroup.mem_bot.symm

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


end monoid_hom

namespace Group

open category_theory

universe u

variables {A B : Group.{u}} (f : A ⟶ B)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
monoid_hom.ker_eq_bot_of_cancel $ λ u v h,
monoid_hom.ext $ λ x, begin

end

end Group
