import representation_theory.group_cohomology.group_extension
import representation_theory.group_cohomology.low_degree
noncomputable theory
namespace group_cohomology
variables {G : Type} [group G] {A : Rep ℤ G} (F : two_cocycles A)

def extend (F : two_cocycles A) := A × G
open category_theory

namespace extend

def mul (x y : extend F) : extend F :=
(x.1 + A.ρ x.2 y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2)

lemma mul_assoc (x y z : extend F) :
  mul F (mul F x y) z = mul F x (mul F y z) :=
prod.ext
begin
  have := (mem_two_cocycles_iff' A F).1 F.2 (x.2, (y.2, z.2)),
  dsimp only [prod.fst, mul] at this ⊢,
  simp only [add_right_inj, map_add, add_assoc, ←linear_map.mul_apply, ←map_mul],
  rw [←this, add_rotate'],
end (mul_assoc _ _ _)

lemma one_mul (g : A × G) :
  mul F (-(F : G × G → A) (1, 1), 1) g = g :=
begin
  ext,
  { simp only [mul, map_one, two_cocycles_snd, linear_map.one_apply, neg_add_cancel_comm] },
  { exact one_mul _ }
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

lemma mul_def (x y : extend F) :
  x * y = (x.1 + A.ρ x.2 y.1 + (F : G × G → A) (x.2, y.2), x.2 * y.2) := rfl

lemma one_def :
  (1 : extend F) = (-(F : G × G → A) (1, 1), 1) := rfl

lemma inv_def (g : extend F) :
  g⁻¹ = (- A.ρ g.2⁻¹ g.1 - (F : G × G → A) (g.2⁻¹, g.2) - (F : G × G → A) (1, 1), g.2⁻¹) := rfl

@[simps] def i : multiplicative A →* extend F :=
{ to_fun := λ x, (x - (F : G × G → A) (1, 1), 1),
  map_one' := prod.ext (zero_sub _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    { show (x + y : A) - _ = _ + _,
      simp only [map_one, linear_map.one_apply, add_assoc, sub_add_cancel, add_sub_right_comm] },
    { exact (_root_.mul_one _).symm }
  end }

lemma i_ker_eq_bot : (i F).ker = ⊥ :=
eq_bot_iff.2 $ λ x hx, by rwa [monoid_hom.mem_ker, i_apply, one_def,
  prod.mk_inj_right, sub_eq_neg_self] at hx

@[simps] def π : extend F →* G :=
{ to_fun := prod.snd,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

lemma π_range_eq_top : (π F).range = ⊤ :=
eq_top_iff.2 $ λ x hx, ⟨(0, x), rfl⟩

lemma exact : (i F).range = (π F).ker :=
subgroup.ext $ λ x, ⟨λ ⟨y, h⟩, h ▸ (monoid_hom.mem_ker _).2 rfl,
  λ (h : _ = _), ⟨(x.1 + (F : G × G → A) (1, 1) : A),
  prod.ext (add_sub_cancel _ _) h.symm⟩⟩

@[simp] def extension : extension (multiplicative A) G :=
{ E := extend F,
  is_group := by apply_instance,
  i := i F,
  π := π F,
  i_ker := i_ker_eq_bot F,
  π_range := π_range_eq_top F,
  exact := exact F }

end extend
variables (G A)

def add_aut_mul_equiv_mul_aut_multiplicative (A : Type*) [add_comm_monoid A] :
  add_aut A ≃* mul_aut (multiplicative A) :=
{ map_mul' := λ x y, rfl, ..add_equiv.to_multiplicative }

-- not in the mood work out the quickest way to get this using the library
def Fucksake : G →* mul_aut (multiplicative A) :=
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

section

def equiv_of_coboundary_aux (f : G → A) :
  extend ⟨d_one A f, linear_map.ext_iff.1 (d_two_comp_d_one.{0} A) f⟩
    ≃* multiplicative A ⋊[Fucksake G A] G :=
{ to_fun := λ x, semidirect_product.mk (x.1 + f x.2 : A) x.2,
  inv_fun := λ x, (x.1 - f x.2, x.2),
  left_inv := λ x, prod.ext (add_sub_cancel _ _) rfl,
  right_inv := λ x, semidirect_product.ext _ _ (sub_add_cancel _ _) rfl,
  map_mul' := λ x y,
  begin
    ext,
    { dsimp [extend.mul_def, Fucksake],
      show _ = ((x.1 + f x.2) + A.ρ x.2 (y.1 + f y.2) : A),
      simp only [map_add, add_assoc, add_right_inj, sub_add_add_cancel, add_rotate' (f x.2)]},
    { refl }
  end }

def equiv_of_coboundary (f : G → A) :
  (extend.extension ⟨d_one A f, linear_map.ext_iff.1 (d_two_comp_d_one.{0} A) f⟩).equiv
    (extension.semidirect_product (multiplicative A) G (Fucksake G A)) :=
{ f := equiv_of_coboundary_aux f,
  left :=
  begin
    ext,
    { show (x - (A.ρ 1 (f 1) - f (1 * 1) + f 1) + f 1 : A) = x,
      rw [map_one, linear_map.one_apply, _root_.mul_one, sub_self, zero_add, sub_add_cancel], },
    { refl }
  end,
  right := by ext; refl }

@[simps] def equiv_of_eq_aux (F1 F2 : two_cocycles A) (f : G → A) (hf : (F1 - F2 : G × G → A) = d_one A f) :
  extend F1 ≃* extend F2 :=
{ to_fun := λ x, (x.1 + f x.2, x.2),
  inv_fun := λ x, (x.1 - f x.2, x.2),
  left_inv := λ x,
  begin
    ext,
    { dsimp only [prod.fst],
      rw add_sub_cancel },
    { refl },
  end,
  right_inv := λ x,
  begin
    ext,
    { dsimp only [prod.fst],
      rw sub_add_cancel },
    { refl }
  end,
  map_mul' := λ x y,
  begin
    ext,
    { dsimp only [prod.fst, extend.mul_def],
      have := function.funext_iff.1 hf (x.2, y.2),
      simp only [pi.sub_apply, d_one_apply, sub_add_eq_add_sub,
        sub_eq_sub_iff_add_eq_add] at this,
      simp only [map_add, add_assoc, this, add_right_inj],
      simp only [←add_assoc, add_left_inj, ←add_rotate (f x.2)] },
    { refl }
  end }

def equiv_of_eq (F1 F2 : two_cocycles A) (f : G → A) (hf : (F1 - F2 : G × G → A) = d_one A f) :
  (extend.extension F1).equiv (extend.extension F2) :=
{ f := equiv_of_eq_aux F1 F2 f hf,
  left :=
  begin
    ext,
    dsimp [extend.extension],
    { have := function.funext_iff.1 hf (1, 1),
      simp only [pi.sub_apply, d_one_apply, map_one, linear_map.one_apply,
        _root_.mul_one, sub_self, zero_add] at this,
      simp only [←this, sub_add_sub_cancel] },
    { refl }
  end,
  right := rfl }

end
variables {H : Type} [comm_group H]

@[simps] def Fucksake2 (f : G →* mul_aut H) : G →* (additive H →ₗ[ℤ] additive H) :=
{ to_fun := λ g, add_monoid_hom.to_int_linear_map (f g).to_monoid_hom.to_additive,
  map_one' :=
  begin
    ext,
    simp only [map_one, add_monoid_hom.coe_to_int_linear_map, monoid_hom.to_additive_apply_apply,
      mul_equiv.coe_to_monoid_hom, mul_aut.one_apply, of_mul_to_mul, linear_map.one_apply],
  end,
  map_mul' := λ x y,
  begin
    ext,
    simp only [map_mul, add_monoid_hom.coe_to_int_linear_map, monoid_hom.to_additive_apply_apply,
      mul_equiv.coe_to_monoid_hom, mul_aut.mul_apply, to_mul_of_mul, linear_map.mul_apply],
  end }

lemma Fucksake2_apply_apply (f : G →* mul_aut H) (g : G) (h : H) :
  Fucksake2 f g h = f g h := rfl

@[simps] def ffs (f : G →* (monoid.End H)) : G →* mul_aut H :=
{ to_fun := λ g,
  { to_fun := f g,
    inv_fun := f g⁻¹,
    left_inv := λ x, by
    { show (f g⁻¹ * f g) x = x,
      rw [←map_mul, mul_left_inv, map_one],
      refl },
    right_inv := λx, by
    { show (f g * f g⁻¹) x = x,
      rw [←map_mul, mul_right_inv, map_one],
      refl },
  map_mul' := λ x y, map_mul _ _ _ },
  map_one' := begin
    ext,
    show f 1 x = x,
    rw [map_one],
    refl,
  end,
  map_mul' := λ g h,
  begin
    ext,
    show f (g * h) x = f g (f h x),
    rw [map_mul],
    refl,
  end }

@[simps] def G_action (E : extension H G) (g : G) : H →* E.E :=
{ to_fun := λ h, E.π_sec g * E.i h * (E.π_sec g)⁻¹,
  map_one' := by simp only [map_one, mul_one, mul_right_inv],
  map_mul' := λ x y, by simp only [map_mul, conj_mul], }

instance i_range_normal (E : extension H G) : E.i.range.normal :=
{ conj_mem := by simp_rw [E.exact]; exact subgroup.normal.conj_mem infer_instance }

lemma conj_mem' (H : subgroup G) [hn : H.normal] (h : G) (hmem : h ∈ H) (g : G) :
  g⁻¹ * h * g ∈ H := by convert hn.conj_mem h hmem g⁻¹; rw inv_inv

@[simp] def G_action_to_range (E : extension H G) (g : G) : H →* E.i.range :=
monoid_hom.cod_restrict (G_action E g) _ $
λ x, subgroup.normal.conj_mem (group_cohomology.i_range_normal E) _ ⟨x, rfl⟩ _

lemma i_sec_one (E : extension H G) :
  E.i_sec ⟨1, E.i.range.one_mem⟩ = 1 :=
show E.i_sec 1 = 1, from map_one _

lemma i_sec_mul (E : extension H G) (g h : E.E) (hg : g ∈ E.i.range) (hh : h ∈ E.i.range) :
  E.i_sec (⟨g * h, E.i.range.mul_mem hg hh⟩) = E.i_sec ⟨g, hg⟩ * E.i_sec ⟨h, hh⟩ :=
by rw [←map_mul]; refl

lemma i_sec_inv (E : extension H G) (g : E.E) (hg : g ∈ E.i.range) :
  E.i_sec (⟨g⁻¹, E.i.range.inv_mem hg⟩) = (E.i_sec ⟨g, hg⟩)⁻¹ :=
by rw ←map_inv; refl

lemma mul_comm_of_mem_i_range {E : extension H G} (g h : E.E)
  (hg : g ∈ E.i.range) (hh : h ∈ E.i.range) :
  g * h = h * g :=
begin
  rcases hg with ⟨x, rfl⟩,
  rcases hh with ⟨y, rfl⟩,
  rw [←map_mul, mul_comm, map_mul]
end

lemma π_sec_one_mem_i_range (E : extension H G) :
  E.π_sec 1 ∈ E.i.range :=
by rw [E.exact, monoid_hom.mem_ker, E.π_sec_spec]

-- terrible names
lemma π_sec_mul_inv_mem_i_range (E : extension H G) (g h : G) :
  E.π_sec (g * h) * (E.π_sec h)⁻¹ * (E.π_sec g)⁻¹ ∈ E.i.range :=
begin
  simp only [E.exact, monoid_hom.mem_ker, map_mul, map_inv,
    E.π_sec_spec, mul_inv_cancel_right, mul_inv_self],
end

lemma π_sec_mul_inv_mem_i_range' (E : extension H G) (g h : G) :
  E.π_sec g * E.π_sec h * (E.π_sec (g * h))⁻¹ ∈ E.i.range :=
begin
  simp only [E.exact, monoid_hom.mem_ker, map_mul, map_inv,
    E.π_sec_spec, mul_inv_self],
end

-- ugh
lemma π_sec_inv_mul_mem_i_range (E : extension H G) (g h : G) :
  (E.π_sec h)⁻¹ * ((E.π_sec g)⁻¹ * E.π_sec (g * h)) ∈ E.i.range :=
begin
  simp only [E.exact, monoid_hom.mem_ker, map_mul, map_inv,
    E.π_sec_spec, inv_mul_cancel_left, inv_mul_self],
end

@[simps] noncomputable def to_mul_aut_aux (E : extension H G) : G →* (monoid.End H) :=
{ to_fun := λ g, E.i_sec.to_monoid_hom.comp (G_action_to_range E g),
  map_one' :=
  begin
    ext,
    simp only [G_action_to_range, G_action_apply, monoid_hom.coe_comp,
      function.comp_app, monoid_hom.cod_restrict_apply, monoid.coe_one, id.def,
      mul_equiv.coe_to_monoid_hom, extension.i_sec, mul_equiv.symm_apply_eq, subtype.ext_iff,
      subtype.coe_mk, monoid_hom.of_injective_apply,
      mul_inv_eq_iff_eq_mul, mul_comm_of_mem_i_range _ _ (π_sec_one_mem_i_range E) ⟨x, rfl⟩],
  end,
  map_mul' := λ g h,
  begin
    ext,
    simp only [G_action_to_range, G_action_apply, monoid_hom.coe_comp,
      function.comp_app, monoid_hom.cod_restrict_apply, monoid.coe_mul,
      mul_equiv.coe_to_monoid_hom],
    congr' 2,
    simp only [E.i_sec_spec', subtype.coe_mk, mul_inv_eq_iff_eq_mul],
    simp only [mul_assoc, mul_comm_of_mem_i_range (E.i x) _ ⟨x, rfl⟩
      (π_sec_inv_mul_mem_i_range E g h)],
    simp only [mul_assoc, mul_inv_cancel_left],
  end }

lemma to_mul_aut_aux_apply_apply {E : extension H G} (g : G) (x : H) :
  to_mul_aut_aux E g x = E.i_sec ⟨E.π_sec g * E.i x * (E.π_sec g)⁻¹,
    (group_cohomology.i_range_normal E).conj_mem _ ⟨x, rfl⟩ _⟩ :=
by congr' 1; ext; refl

noncomputable def to_mul_aut (E : extension H G) : G →* (mul_aut H)  :=
ffs (to_mul_aut_aux E)

noncomputable def Rep.of_extension (E : extension H G) : Rep ℤ G :=
{ V := Module.of ℤ (additive H),
  ρ := Fucksake2 (to_mul_aut E) }

lemma Rep.of_extension_ρ (E : extension H G) :
  (Rep.of_extension E).ρ = Fucksake2 (to_mul_aut E) := rfl

noncomputable def extension.two_cocycle_aux (E : extension H G) : G × G → H :=
λ ⟨g, h⟩, E.i_sec (⟨E.π_sec g * E.π_sec h * (E.π_sec (g * h))⁻¹,
begin
  rw [E.exact, monoid_hom.mem_ker],
  simp only [map_mul, map_inv, E.π_sec_spec, mul_inv_self],
end⟩)

@[simps] noncomputable def extension.two_cocycle (E : extension H G) :
  two_cocycles (Rep.of_extension E) :=
{ val := @extension.two_cocycle_aux G _ H _ E,
  property :=
  begin
    ext,
    simp only [d_two_apply, extension.two_cocycle_aux,
      Rep.of_extension_ρ, Fucksake2_apply_apply, to_mul_aut,
      ffs_apply_apply, to_mul_aut_aux_apply_apply],
    show (E.i_sec _ / E.i_sec _) * E.i_sec _ / E.i_sec _ = (1 : H),
    simp only [div_eq_mul_inv, E.i_sec_spec'],
    rw [←map_one E.i_sec],
    simp only [←map_mul, ←map_inv],
    congr,
    ext,
    simp only [subgroup.coe_mul, subgroup.coe_mk, subgroup.coe_inv,
      subgroup.coe_one, ←mul_assoc],
    rw [mul_inv_eq_iff_eq_mul, one_mul],
    simp only [mul_assoc],
    rw mul_comm_of_mem_i_range (_ * (_ * _))⁻¹,
    simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev, mul_inv_cancel_left],
    { simp only [←mul_assoc],
      exact E.i.range.inv_mem (π_sec_mul_inv_mem_i_range' E _ _) },
    { rw [←mul_assoc],
      exact (π_sec_mul_inv_mem_i_range' E _ _) }
  end }

def extension.equiv.range_restrict {E1 E2 : extension H G} (f : E1.equiv E2) :
  E1.i.range →* E2.i.range :=
(f.f.to_monoid_hom.comp E1.i.range.subtype).cod_restrict _ $
λ ⟨x, y, rfl⟩, ⟨y, (f.left_apply _).symm⟩

lemma range_restrict_apply {E1 E2 : extension H G} (f : E1.equiv E2) (x : E1.i.range) :
  (f.range_restrict x : E2.E) = f.f x := rfl

@[simp] lemma i_sec_symm_apply {E : extension H G} (x : H) :
  (E.i_sec.symm x : E.E) = E.i x := rfl

lemma range_restrict_comp_i_sec_apply {E1 E2 : extension H G} (f : E1.equiv E2) (x : E1.i.range) :
  E2.i_sec (f.range_restrict x) = E1.i_sec x :=
begin
  rw ←mul_equiv.eq_symm_apply,
  ext,
  rw [i_sec_symm_apply, range_restrict_apply, ←f.left_apply, E1.i_sec_spec'],
end

lemma i_sec_i_apply {E1 E2 : extension H G} (f : E1.equiv E2) (x : E1.i.range) :
  E2.i (E1.i_sec x) = f.f x :=
begin
  rw [←f.left_apply, E1.i_sec_spec'],
end

lemma i_sec_i_symm_apply {E1 E2 : extension H G} (f : E1.equiv E2) (x : E2.i.range) :
  E1.i (E2.i_sec x) = (extension.symm f).f (x : E2.E) :=
i_sec_i_apply (extension.symm f) x

lemma to_mul_aut_aux_eq_of_extension_equiv {E1 E2 : extension H G} (f : E1.equiv E2) :
  to_mul_aut_aux E1 = to_mul_aut_aux E2 :=
begin
  ext g h,
  simp only [G_action_apply, G_action_to_range, to_mul_aut_aux_apply, monoid_hom.coe_comp,
    mul_equiv.coe_to_monoid_hom, function.comp_app, monoid_hom.cod_restrict_apply],
  rw ←range_restrict_comp_i_sec_apply f,
  congr,
  ext,
  rw range_restrict_apply,
  simp only [subtype.coe_mk, map_mul, map_inv, mul_inv_eq_iff_eq_mul],
  simp only [monoid_hom.coe_coe, extension.equiv.left_apply, mul_assoc],
  rw [mul_comm_of_mem_i_range (E2.i h) _ ⟨h, rfl⟩, mul_assoc, mul_inv_cancel_left],
  { simp only [E2.exact, monoid_hom.mem_ker, map_mul, map_inv, extension.π_sec_spec],
    rw [f.right_apply, E1.π_sec_spec, inv_mul_self] }
end

lemma ρ_eq_of_extension_equiv (E1 E2 : extension H G) (f : extension.equiv E1 E2) :
  (Rep.of_extension E1).ρ = (Rep.of_extension E2).ρ :=
begin
  ext g h,
  simp only [Rep.of_extension_ρ, Fucksake2_apply_apply, to_mul_aut, ffs_apply_apply,
    to_mul_aut_aux_eq_of_extension_equiv f],
end

def one_coboundary_of_equiv_aux {E1 E2 : extension H G} (f : E1.equiv E2) (g : G) :
  H := E2.i_sec ⟨(f.f (E1.π_sec g)) * (E2.π_sec g)⁻¹,
begin
  rw [E2.exact, monoid_hom.mem_ker, map_mul, map_inv, E2.π_sec_spec, f.right_apply,
    E1.π_sec_spec, mul_inv_self],
end⟩

lemma lol {E1 E2 : extension H G} (f : E1.equiv E2) (g h : G) :
  E2.π_sec g * E2.π_sec h * (E2.π_sec (g * h))⁻¹ =
    f.f (E1.π_sec g * E1.π_sec h * (E1.π_sec (g * h))⁻¹) *
    E2.π_sec g * E2.π_sec h * (f.f (E1.π_sec h))⁻¹ * (E2.π_sec g)⁻¹
    * (E2.π_sec (g * h) * (f.f (E1.π_sec (g * h)))⁻¹)⁻¹
    * E2.π_sec g * (f.f (E1.π_sec g))⁻¹ :=
begin
  simp only [map_mul_inv, map_mul, mul_assoc],
  rw mul_comm_of_mem_i_range (_ * _)⁻¹,
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_rev, inv_inv],
  simp only [←mul_assoc, mul_left_inj],
  rw ←mul_inv_eq_iff_eq_mul,
  simp only [mul_assoc (f.f _ * f.f _ * _)],
  rw mul_comm_of_mem_i_range (_ * _ * _),
  simp only [mul_assoc, map_inv, inv_mul_cancel_left],
  all_goals {simp only [E2.exact, monoid_hom.mem_ker, map_mul, map_inv,
      f.right_apply, extension.π_sec_spec, mul_inv_cancel_right, mul_inv_self, inv_one] },
end

open extension

lemma heqlemma {V : Type*} [add_comm_group V] (ρ τ : representation ℤ G V) (h : ρ = τ)
  (f g : G × G → V) (hf : f ∈ two_cocycles (Rep.of ρ)) (hg : g ∈ two_cocycles (Rep.of τ))
  (p : G → V) (H : f = g + d_one (Rep.of ρ) p) :
  (submodule.quotient.mk (⟨f, hf⟩ : two_cocycles (Rep.of ρ)) : H2 (Rep.of ρ))
    == (submodule.quotient.mk (⟨g, hg⟩ : two_cocycles (Rep.of τ)) : H2 (Rep.of τ)) :=
begin
  cases h,
  refine heq_of_eq _,
  rw submodule.quotient.eq,
  use p,
  ext,
  simp only [H, linear_map.cod_restrict_apply, add_subgroup_class.coe_sub,
    submodule.coe_mk, add_sub_cancel'],
end

lemma lol3 {G H : Type} [group G] [comm_group H] {E1 E2 : extension H G} (f : E1.equiv E2)
  (g h : G) :
two_cocycle_aux E2 (g, h) = two_cocycle_aux E1 (g, h) * (to_mul_aut E1 g
  (one_coboundary_of_equiv_aux f h) / (one_coboundary_of_equiv_aux f (g * h)) *
  one_coboundary_of_equiv_aux f g)⁻¹ :=
begin
  dsimp only [two_cocycle_aux, one_coboundary_of_equiv_aux, to_mul_aut,
    ffs_apply_apply],
  simp only [div_eq_mul_inv, to_mul_aut_aux_apply_apply],
  repeat {rw ←range_restrict_comp_i_sec_apply f},
  simp only [←map_mul, ←map_inv],
  congr' 1,
  ext,
  simp only [subtype.coe_mk, subgroup.coe_mul, subgroup.coe_inv, range_restrict_apply],
  rw [mul_inv_rev, i_sec_i_symm_apply f],
  simp only [subtype.coe_mk, map_mul, extension.symm_f, mul_equiv.apply_symm_apply],
  simp only [←map_mul, mul_assoc],
  rw mul_comm_of_mem_i_range (f.f _),
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left],
  rw [←mul_assoc (f.f (E1.π_sec (g * h))), mul_comm_of_mem_i_range (f.f _ * _)],
  simp only [mul_assoc, inv_mul_cancel_left],
  all_goals {simp only [E2.exact, monoid_hom.mem_ker, map_mul, map_inv, mul_inv_rev,
    f.right_apply, extension.π_sec_spec, mul_inv_cancel_left, mul_inv_self, inv_one, mul_assoc,
    inv_inv] },
end

lemma lol2 {E1 E2 : extension H G} (f : E1.equiv E2) :
  (submodule.quotient.mk E1.two_cocycle : H2 (Rep.of_extension E1))
  == (submodule.quotient.mk E2.two_cocycle : H2 (Rep.of_extension E2)) :=
begin
  refine heqlemma _ _ _ _ _ _ _ _ _,
  exact ρ_eq_of_extension_equiv _ _ f,
  exact one_coboundary_of_equiv_aux f,
  symmetry,
  refine eq_mul_inv_iff_mul_eq.1 _,
  ext,
  rcases x with ⟨g, h⟩,
  exact lol3 f g h,
end

@[simps] def E_equiv_prod (E : extension H G) :
  E.E ≃ H × G :=
{ to_fun := λ x, (E.i_sec ⟨x * (E.π_sec (E.π x))⁻¹,
    by rw [E.exact, monoid_hom.mem_ker, map_mul, map_inv, E.π_sec_spec, mul_inv_self]⟩, E.π x),
  inv_fun := λ g, E.i g.1 * E.π_sec g.2,
  left_inv := λ x,
  begin
    dsimp only,
    rw [E.i_sec_spec', subtype.coe_mk, inv_mul_cancel_right],
  end,
  right_inv := λ g,
  begin
    dsimp,
    ext,
    { simp only [map_mul, extension.π_sec_spec, extension.π_i_apply,
        one_mul, mul_inv_cancel_right, E.i_sec_spec] },
    { simp only [map_mul, extension.π_sec_spec, extension.π_i_apply, one_mul], }
  end }

lemma monoid_hom.apply_eq_one_of_range_eq_ker {G H J : Type*} [group G] [group H]
  [group J] (f : G →* H) (g : H →* J) (h : f.range = g.ker) (x : G) :
  g (f x) = 1 :=
monoid_hom.ext_iff.1 (f.comp_eq_one_of_range_eq_ker g h) x

def left_inv (E : extension H G) :
  E.equiv (extend.extension (extension.two_cocycle E)) :=
{ f :=
  { map_mul' := λ x y,
    begin
      rw extend.mul_def (extension.two_cocycle E),
      ext,
      { dsimp,
        simp only [Rep.of_extension_ρ, extension.two_cocycle_coe,
          extension.two_cocycle_aux, Fucksake2_apply_apply, ffs_apply_apply,
          to_mul_aut_aux_apply_apply, to_mul_aut,
          E.i_sec_spec'],
        show _ = E.i_sec _ * E.i_sec _ * E.i_sec _,
        simp only [←map_mul E.i_sec],
        congr' 1,
        ext,
        simp only [subtype.coe_mk, E.i.range.coe_mul, mul_assoc, inv_mul_cancel_left, map_mul] },
      { simp only [E_equiv_prod_apply, equiv.to_fun_as_coe, Rep.of_extension_ρ,
          extension.two_cocycle_coe, extension.two_cocycle_aux, Fucksake2_apply_apply,
          ffs_apply_apply, to_mul_aut_aux_apply_apply, to_mul_aut, E.i_sec_spec', map_mul], },
    end, ..E_equiv_prod E },
  left :=
  begin
    refine monoid_hom.ext (λ x, _),
    dsimp only,
    show E_equiv_prod E (E.i x) = extend.i (two_cocycle E) x,
    rw E_equiv_prod_apply,
    rw extend.i_apply,
    ext,
    { simp only [extension.two_cocycle_coe, extension.two_cocycle_aux, one_mul,
        mul_inv_cancel_right, E.i.apply_eq_one_of_range_eq_ker E.π E.exact],
      show _ = x / E.i_sec _,
      rw eq_div_iff_mul_eq',
      rw ←map_mul,
      show E.i_sec (⟨E.i x * _ * E.π_sec 1, _⟩) = _,
      simp_rw inv_mul_cancel_right,
      exact E.i_sec_spec _ },
    exact monoid_hom.ext_iff.1 (E.i.comp_eq_one_of_range_eq_ker E.π E.exact) x,
  end,
  right := sorry }

def correspondence :
  extension.extension_classes H G ≃ Σ (ρ : representation ℤ G (additive H)), H2 (Rep.of ρ) :=
{ to_fun := λ x, quotient.lift_on' x (λ E, @sigma.mk (representation ℤ G (additive H))
      (λ ρ, H2 (Rep.of ρ)) (Fucksake2 (to_mul_aut E))
    (submodule.quotient.mk (extension.two_cocycle E) : H2 (Rep.of_extension E))) $
    begin
      rintros a b ⟨f⟩,
      exact sigma.ext (ρ_eq_of_extension_equiv _ _ f) (lol2 f),
    end,
  inv_fun := λ ⟨ρ, x⟩, quotient.lift_on'
    x (λ y, @quotient.mk' _ (extension.rel H G)
    (extend.extension y)) $ λ a b h,
    begin
      rw submodule.quotient_rel_r_def at h,
      rcases h with ⟨f, hf⟩,
      exact quotient.eq'.2 ⟨equiv_of_eq a b f (subtype.ext_iff.1 hf).symm⟩,
    end,
  left_inv := λ x,
  begin
    refine quotient.induction_on' x (λ y, _),
    sorry
  end,
  right_inv := sorry, }

end group_cohomology
