import group_theory.group_action.basic
import representation_theory.group_cohomology.group_extensions

variables (G : Type*) [group G] (A : Type*) [add_comm_group A] [distrib_mul_action G A]
namespace whoops

@[simps] def d_two : (G × G → A) →+ (G × G × G → A) :=
{ to_fun := λ f g, g.1 • (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1),
  map_add' := λ x y, funext $ λ g, by sorry,
  map_zero' := sorry }

def two_cocycles := (d_two G A).ker

variables {G A}

lemma mem_two_cocycles_iff (f : G × G → A) :
  f ∈ two_cocycles G A ↔ ∀ g : G × G × G, g.1 • (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2)
    + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1) = 0 :=
sorry

lemma mem_two_cocycles_iff' (f : G × G → A) :
  f ∈ two_cocycles G A ↔ ∀ g : G × G × G, f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1)
    = g.1 • (f (g.2.1, g.2.2)) + f (g.1, g.2.1 * g.2.2) :=
by simp_rw [mem_two_cocycles_iff, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add,
  eq_comm, add_comm (f (prod.fst _, _))]

variables (F : two_cocycles G A)

def extend (F : two_cocycles G A) := A × G

def mul (x y : extend F) : extend F :=
(x.1 + x.2 • y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2)

set_option profiler true
-- > 4.1s
lemma mul_assoc (x y z : extend F) :
  mul F (mul F x y) z = mul F x (mul F y z) :=
begin
  ext,
  { have := (mem_two_cocycles_iff' (F : G × G → A)).1 F.2 (x.2, (y.2, z.2)),
    dsimp [mul] at this ⊢,
    simp only [add_right_inj, smul_add, add_assoc],
    rw [←this, add_rotate', mul_smul] },
  { exact mul_assoc _ _ _ }
end
#exit
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

def add_aut_mul_equiv_mul_aut_multiplicative (A : Type u) [add_comm_monoid A] :
  add_aut A ≃* mul_aut (multiplicative A) :=
{ map_mul' := λ x y, rfl, ..add_equiv.to_multiplicative }

-- not in the mood work out the quickest way to get this using the library
def Fucksake : G →* (mul_aut (multiplicative A)) :=
{ to_fun := λ g,
  { to_fun := A.ρ g,
    inv_fun := A.ρ g⁻¹,
    left_inv := λ x, show (A.ρ g⁻¹ * A.ρ g) x = x,
    by simpa only [←map_mul, inv_mul_self, map_one],
    right_inv := λ x, show (A.ρ g * A.ρ g⁻¹) x = x,
    by simpa only [←map_mul, mul_inv_self, map_one],
    map_mul' := map_add _ },
  map_one' := by ext; simpa only [map_one],
  map_mul' := λ x y, by ext; simpa only [map_mul] }

variables {G A}

def equiv_of_coboundary_aux (f : G → A) :
  extend ⟨d_one A f, linear_map.ext_iff.1 (d_one_comp_d_zero A) f⟩
    ≃* multiplicative A ⋊[Fucksake G A] G :=
{ to_fun := λ x, semidirect_product.mk (x.1 + f x.2 : A) x.2,
  inv_fun := λ x, (x.1 - f x.2, x.2),
  left_inv := λ x, prod.ext (add_sub_cancel _ _) rfl,
  right_inv := λ x, semidirect_product.ext _ _ (sub_add_cancel _ _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    { dsimp [extend_mul_def, Fucksake],
      show _ = ((x.1 + f x.2) + A.ρ x.2 (y.1 + f y.2) : A),
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


end whoops
