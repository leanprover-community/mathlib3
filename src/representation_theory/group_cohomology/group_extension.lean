import group_theory.semidirect_product

universes v u

@[to_additive] lemma monoid_hom.comp_eq_one_of_range_eq_ker
  {G H J : Type*} [group G] [group H] [group J]
  (f : G →* H) (g : H →* J) (h : f.range = g.ker) :
  g.comp f = 1 :=
monoid_hom.ext $ λ x, g.mem_ker.1 (by rw ←h; exact ⟨x, rfl⟩)

structure extension (H G : Type*) [group H] [group G] :=
(E : Type*)
[is_group : group E]
(i : H →* E)
(π : E →* G)
(i_ker : i.ker = ⊥)
(π_range : π.range = ⊤)
(exact : i.range = π.ker)

attribute [instance] extension.is_group

namespace extension
variables {H G : Type*} [group H] [group G]

@[simp] lemma π_i_apply (E : extension H G) (g : H) :
  E.π (E.i g) = 1 :=
monoid_hom.ext_iff.1 (monoid_hom.comp_eq_one_of_range_eq_ker _ _ E.exact) _

noncomputable def π_sec (E : extension H G) (g : G) : E.E :=
classical.some (monoid_hom.range_top_iff_surjective.1 E.π_range g)

@[simp] lemma π_sec_spec (E : extension H G) (g : G) :
  E.π (π_sec E g) = g :=
classical.some_spec (monoid_hom.range_top_iff_surjective.1 E.π_range g)

noncomputable def i_sec (E : extension H G) : E.i.range ≃* H :=
(monoid_hom.of_injective (E.i.ker_eq_bot_iff.1 E.i_ker)).symm

@[simp] lemma i_sec_spec (E : extension H G) (g : H) :
  E.i_sec (⟨E.i g, ⟨g, rfl⟩⟩) = g :=
(monoid_hom.of_injective (E.i.ker_eq_bot_iff.1 E.i_ker)).3 g

lemma i_sec_spec' (E : extension H G) (g : E.i.range) :
  E.i (E.i_sec g) = g :=
subtype.ext_iff.1 ((monoid_hom.of_injective (E.i.ker_eq_bot_iff.1 E.i_ker)).4 g)

set_option profiler true

structure equiv (E1 E2 : extension H G) :=
(f : E1.E ≃* E2.E)
(left : f.to_monoid_hom.comp E1.i = E2.i)
(right : E2.π.comp f.to_monoid_hom = E1.π)

@[simp] lemma equiv.left_apply {E1 E2 : extension H G} (f : equiv E1 E2) (x : H) :
  f.f (E1.i x) = E2.i x := monoid_hom.ext_iff.1 f.left x

@[simp] lemma equiv.right_apply {E1 E2 : extension H G} (f : equiv E1 E2) (x : E1.E) :
  E2.π (f.f x) = E1.π x := monoid_hom.ext_iff.1 f.right x

@[simps] def refl (E : extension H G) : equiv E E :=
{ f := mul_equiv.refl E.E,
  left := monoid_hom.id_comp _,
  right := monoid_hom.comp_id _ }

@[simps] def symm {E1 E2 : extension H G} (f : equiv E1 E2) : equiv E2 E1 :=
{ f := f.f.symm,
  left :=
  begin
    rw ←f.left,
    ext,
    simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app,
      mul_equiv.symm_apply_apply],
  end,
  right :=
  begin
    rw ←f.right,
    ext,
    simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, function.comp_app,
      mul_equiv.apply_symm_apply],
  end }

@[simps] def trans {E1 E2 E3 : extension H G} (f : equiv E1 E2) (g : equiv E2 E3) : equiv E1 E3 :=
{ f := f.f.trans g.f,
  left :=
  begin
    ext,
    simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, mul_equiv.coe_trans,
      function.comp_app, f.left_apply, g.left_apply],
  end,
  right :=
  begin
    have hf := monoid_hom.ext_iff.1 f.right,
    have hg := monoid_hom.ext_iff.1 g.right,
    ext,
    simp only [monoid_hom.coe_comp, mul_equiv.coe_to_monoid_hom, mul_equiv.coe_trans,
      function.comp_app] at hf hg ⊢,
    rw [hg, hf]
  end, }

variables (H G)

instance rel : setoid (extension H G) :=
{ r := λ E1 E2, nonempty (equiv E1 E2),
  iseqv := ⟨λ E, ⟨refl E⟩, λ E1 E2 ⟨f⟩, ⟨symm f⟩, λ E1 E2 E3 ⟨f⟩ ⟨g⟩, ⟨trans f g⟩⟩ }

def extension_classes := quotient (extension.rel H G)

def trivial : extension H G :=
{ E := H × G,
  is_group := prod.group,
  i := monoid_hom.inl H G,
  π := monoid_hom.snd H G,
  i_ker := eq_bot_iff.2 $ λ x hx, (prod.ext_iff.1 hx).1,
  π_range := eq_top_iff.2 $ λ x hx, ⟨(1, x), rfl⟩,
  exact := subgroup.ext $ λ x, ⟨λ ⟨y, h⟩, h ▸ (monoid_hom.mem_ker _).2 rfl,
   λ hx, ⟨x.1, prod.ext rfl hx.symm⟩⟩ }

section semidirect_product
open semidirect_product

def semidirect_product (φ : G →* mul_aut H) : extension H G :=
{ E := H ⋊[φ] G,
  is_group := by apply_instance,
  i := inl,
  π := right_hom,
  i_ker := (monoid_hom.ker_eq_bot_iff _).2 inl_injective,
  π_range := monoid_hom.range_top_of_surjective _ right_hom_surjective,
  exact := range_inl_eq_ker_right_hom }

@[simps] def one_equiv_trivial_aux : H ⋊[1] G ≃* H × G :=
{ to_fun := λ x, (x.1, x.2),
  inv_fun := λ x, semidirect_product.mk x.1 x.2,
  left_inv := λ x, ext _ _ rfl rfl,
  right_inv := λ x, prod.ext rfl rfl,
  map_mul' := λ x y, prod.ext rfl rfl }

def one_equiv_trivial : equiv (semidirect_product H G 1) (trivial H G) :=
{ f := one_equiv_trivial_aux H G,
  left := by ext; refl; refl,
  right := by ext; refl; refl }

end semidirect_product
end extension
