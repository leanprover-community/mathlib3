import representation_theory.group_cohomology.low_degree algebra.category.Group.images algebra.homology.short_exact.preadditive

universes v u
open category_theory category_theory.limits

structure extension (H G : Type*) [group H] [group G] :=
(E : Type*)
[is_group : group E]
(i : H →* E)
(π : E →* G)
(inj : function.injective i)
(surj : function.surjective π)
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

instance : category (extension H G) :=
{ hom := hom,
  id := id,
  comp := λ X Y Z f g, comp f g }

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
end

open group_cohomology
variables {G : Type} [group G] {A : Rep ℤ G} (F : two_cocycles A)
-- WHY IS THIS ALL SO FUCKING SLOW
def extend (F : two_cocycles A) := A × G
def mul (x y : A × G) : A × G :=
(x.1 + A.ρ x.2 y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2)

lemma mul_assoc (x y z : A × G) :
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
  {-- dsimp [mul],
    simp only [mul, map_one, two_cocycles_snd, linear_map.one_apply, neg_add_cancel_comm] },
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

def extend_i : multiplicative A →* extend F :=
{ to_fun := λ x, (x - (F : G × G → A) (1, 1), 1),
  map_one' := prod.ext (zero_sub _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    dsimp,
    simp only [extend_mul_def],
    show _ + _ - _ = ((_ - _) + _) + _,
    simp only [map_one, linear_map.one_apply, add_assoc],
    rw sub_add_cancel,
    sorry,
  end }

def extend_π : extend F →* G :=
{ to_fun := prod.snd,
  map_one' := rfl,
  map_mul' := λ x y, rfl }
#exit
def extension : extension (multiplicative A) G :=
{ E := extend F,
  is_group := by apply_instance,
  i := extend_i F,
  π := _,
  inj := _,
  surj := _,
  exact := _ }

def equiv_of_eq (F1 F2 : two_cocycles A)
  (H : (two_coboundaries A).quotient.mk F1 = (two_coboundaries A).quotient.mk F2) :
  equiv (extend F1)
end
