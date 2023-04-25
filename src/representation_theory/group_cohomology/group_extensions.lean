import representation_theory.group_cohomology.low_degree algebra.category.Group.images algebra.homology.short_exact.preadditive
import group_theory.semidirect_product

universes v u
open category_theory category_theory.limits

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
section
variables {H G : Type*} [group H] [group G]

@[ext] structure hom (E1 E2 : extension H G) :=
(f : E1.E →* E2.E)
(left : f.comp E1.i = E2.i)
(right : E2.π.comp f = E1.π)

def comp {E1 E2 E3 : extension H G} (f : hom E1 E2) (g : hom E2 E3) : hom E1 E3 :=
{ f := g.f.comp f.f,
  left := by rw [monoid_hom.comp_assoc, f.left, g.left],
  right := by rw [←monoid_hom.comp_assoc, g.right, f.right] }

def id (E : extension H G) : hom E E :=
{ f := monoid_hom.id _,
  left := monoid_hom.comp_id _,
  right := monoid_hom.id_comp _ }

lemma comp_id {E1 E2 : extension H G} (f : hom E1 E2) :
  comp f (id E2) = f :=
by ext; refl

lemma id_comp {E1 E2 : extension H G} (f : hom E1 E2) :
  comp (id E1) f = f :=
by ext; refl

/-instance : category (extension H G) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g }-/

structure equiv (E1 E2 : extension H G) :=
(f : E1.E ≃* E2.E)
(left : f.to_monoid_hom.comp E1.i = E2.i)
(right : E2.π.comp f.to_monoid_hom = E1.π)

def refl (E : extension H G) : equiv E E :=
{ f := mul_equiv.refl E.E,
  left := monoid_hom.id_comp _,
  right := monoid_hom.comp_id _ }

def symm {E1 E2 : extension H G} (f : equiv E1 E2) : equiv E2 E1 :=
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

def trans {E1 E2 E3 : extension H G} (f : equiv E1 E2) (g : equiv E2 E3) : equiv E1 E3 :=
{ f := f.f.trans g.f,
  left :=
  begin
    have hf := monoid_hom.ext_iff.1 f.left,
    have hg := monoid_hom.ext_iff.1 g.left,
    ext,
    dsimp at *,
    rw [hf, hg]
  end,
  right :=
  begin
    have hf := monoid_hom.ext_iff.1 f.right,
    have hg := monoid_hom.ext_iff.1 g.right,
    ext,
    dsimp at *,
    rw [hg, hf]
  end, }
/-def mk_iso {E1 E2 : extension H G} (f : E1.E ≅ E2.E) (left : E1.i ≫ f.hom = E2.i)
  (right : f.hom ≫ E2.π = E1.π) :
  E1 ≅ E2 :=
{ hom := ⟨f.hom, left, right⟩,
  inv :=
  { f := f.inv,
    left := f.comp_inv_eq.2 left.symm,
    right := f.inv_comp_eq.2 right.symm },
  hom_inv_id' := extension.hom.ext _ _ f.hom_inv_id,
  inv_hom_id' := extension.hom.ext _ _ f.inv_hom_id }-/
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

def one_equiv_trivial_aux : H ⋊[1] G ≃* H × G :=
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
end

open group_cohomology
variables {G : Type} [group G] {A : Rep ℤ G} (F : two_cocycles A)
-- WHY IS THIS ALL SO FUCKING SLOW
def extend (F : two_cocycles A) := A × G
def mul (x y : extend F) : extend F :=
(x.1 + A.ρ x.2 y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2)

lemma mul_assoc (x y z : extend F) :
  mul F (mul F x y) z = mul F x (mul F y z) :=
begin
  ext,
  { have := (mem_two_cocycles_iff' A F).1 F.2 (x.2, (y.2, z.2)),
    dsimp [mul] at this ⊢,
    simp only [add_right_inj, map_add, add_assoc, ←linear_map.mul_apply, ←map_mul],
    rw [←this, add_rotate'] },
  { exact mul_assoc _ _ _ }
end

lemma two_cocycles_snd {k G : Type u} [comm_ring k] [group G]
  {A : Rep k G} (g : G) (f : two_cocycles A) :
  (f : G × G → A) (1, g) = (f : G × G → A) (1, 1) :=
begin
  have := ((mem_two_cocycles_iff' A f).1 f.2 (1, (1, g))).symm,
  simpa only [map_one, linear_map.one_apply, one_mul, add_right_inj, this],
end

lemma two_cocycles_fst {k G : Type u} [comm_ring k] [group G]
  {A : Rep k G} (g : G) (f : two_cocycles A) :
  (f : G × G → A) (g, 1) = A.ρ g ((f : G × G → A) (1, 1)) :=
begin
  have := (mem_two_cocycles_iff' A f).1 f.2 (g, (1, 1)),
  simpa only [mul_one, add_left_inj, this],
end

lemma one_mul (g : A × G) :
  mul F (-(F : G × G → A) (1, 1), 1) g = g :=
begin
  ext,
  { simp only [mul, map_one, two_cocycles_snd, linear_map.one_apply, neg_add_cancel_comm] },
  { exact one_mul _}
end

lemma mul_one (g : A × G) :
  mul F g (-(F : G × G → A) (1, 1), 1) = g :=
begin
  ext,
  { simp only [mul, two_cocycles_fst g.2, map_neg, neg_add_cancel_right], },
  { exact mul_one _ }
end

lemma mul_left_inv (g : A × G) :
  mul F (- A.ρ g.2⁻¹ g.1 - (F : G × G → A) (g.2⁻¹, g.2) - (F : G × G → A) (1, 1), g.2⁻¹) g
    = (-(F : G × G → A) (1, 1), 1) :=
begin
  ext,
  { simp only [mul, eq_neg_iff_add_eq_zero, ←neg_add',
     add_assoc, neg_add_self] },
  { exact mul_left_inv _ }
end

instance : group (extend F) :=
{ mul := mul F,
  mul_assoc := mul_assoc F,
  one := (-(F : G × G → A) (1, 1), 1),
  one_mul := one_mul F,
  mul_one := mul_one F,
  inv := λ g, (- A.ρ g.2⁻¹ g.1 - (F : G × G → A) (g.2⁻¹, g.2) - (F : G × G → A) (1, 1), g.2⁻¹),
  mul_left_inv := mul_left_inv F }

lemma extend_mul_def (x y : extend F) :
  x * y = (x.1 + A.ρ x.2 y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2) := rfl

lemma extend_one_def :
  (1 : extend F) = (-(F : G × G → A) (1, 1), 1) := rfl

lemma extend_inv_def (g : extend F) :
  g⁻¹ = (- A.ρ g.2⁻¹ g.1 - (F : G × G → A) (g.2⁻¹, g.2) - (F : G × G → A) (1, 1), g.2⁻¹) := rfl

@[simps] def extend_i : multiplicative A →* extend F :=
{ to_fun := λ x, (x - (F : G × G → A) (1, 1), 1),
  map_one' := prod.ext (zero_sub _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    { show (x + y : A) - _ = _ + _,
      simp only [map_one, linear_map.one_apply, add_assoc, sub_add_cancel, add_sub_right_comm] },
    { exact (_root_.mul_one _).symm }
  end }

lemma extend_i_ker_eq_bot : (extend_i F).ker = ⊥ :=
eq_bot_iff.2 $ λ x hx, by rwa [monoid_hom.mem_ker, extend_i_apply, extend_one_def,
  prod.mk_inj_right, sub_eq_neg_self] at hx

@[simps] def extend_π : extend F →* G :=
{ to_fun := prod.snd,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

lemma extend_π_range_eq_top : (extend_π F).range = ⊤ :=
eq_top_iff.2 $ λ x hx, ⟨(0, x), rfl⟩

lemma extend_exact : (extend_i F).range = (extend_π F).ker :=
subgroup.ext $ λ x, ⟨λ ⟨y, h⟩, h ▸ (monoid_hom.mem_ker _).2 rfl,
  λ (h : _ = _), ⟨(x.1 + (F : G × G → A) (1, 1) : A),
  prod.ext (add_sub_cancel _ _) h.symm⟩⟩

def extension : extension (multiplicative A) G :=
{ E := extend F,
  is_group := by apply_instance,
  i := extend_i F,
  π := extend_π F,
  i_ker := extend_i_ker_eq_bot F,
  π_range := extend_π_range_eq_top F,
  exact := extend_exact F }

variables (G A)
def Fucksake : G →* (mul_aut (multiplicative A)) :=
{ to_fun := λ g,
  { to_fun := A.ρ g,
    inv_fun := A.ρ g⁻¹,
    left_inv := sorry,
    right_inv := sorry,
    map_mul' := map_add _ },
  map_one' := sorry,
  map_mul' := sorry }

variables {G A}

def equiv_of_coboundary_aux (f : G → A) :
  extend ⟨d_one A f, sorry⟩ ≃* multiplicative A ⋊[Fucksake G A] G :=
{ to_fun := λ x, semidirect_product.mk (x.1 + f x.2 : A) x.2,
  inv_fun := λ x, (x.1 - f x.2, x.2),
  left_inv := λ x, prod.ext (add_sub_cancel _ _) rfl,
  right_inv := λ x, semidirect_product.ext _ _ (sub_add_cancel _ _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    { dsimp [extend_mul_def, Fucksake],
      show _ = ((x.1 + f x.2) +  A.ρ x.2 (y.1 + f y.2) : A),
      simp only [map_add, add_assoc, add_right_inj, sub_add_add_cancel, add_rotate' (f x.2)]},
    { refl }
  end }

def equiv_of_coboundary (f : G → A) :
  equiv (extension ⟨d_one A f, sorry⟩) (semidirect_product (multiplicative A) G (Fucksake G A)) :=
{ f := equiv_of_coboundary_aux f,
  left :=
  begin
    ext,
    { show (x - (A.ρ 1 (f 1) - f (1 * 1) + f 1) + f 1 : A) = x,
      rw [map_one, linear_map.one_apply, _root_.mul_one, sub_self, zero_add, sub_add_cancel], },
    { refl }
  end,
  right := by ext; refl }

#exit

def equiv_of_eq (F1 F2 : two_cocycles A)
  (H : (two_coboundaries A).mkq F1 = (two_coboundaries A).mkq F2) :
  equiv (extension F1) (extension F2) :=
{ f := _,
  left := _,
  right := _ }

def two_cocycle (E : extension A G) : two_cocycles A :=
{! !}
end
