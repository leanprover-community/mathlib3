import group_theory.quotient_monoid

variables {α : Type*} [monoid α] {X : Type*} [comm_monoid X]
          {Z : Type*} [comm_monoid Z]

local notation `top` := (⊤ : submonoid X)

variables (X)

@[reducible] def completion := (submonoid.r (⊤ : submonoid X)).quotient

namespace completion

instance : has_coe (X × top) (completion X) := infer_instance

instance : has_inv (completion X) :=
⟨localization.lift top (λ x, (((x.2 : X), (⟨x.1, set.mem_univ x.1⟩ : top)) : completion X)) $
λ a b ⟨w, hw⟩, con.eq.2 $ ⟨w, by dsimp; rw [mul_comm _ b.1, mul_comm _ a.1, hw]⟩⟩

def inv : completion X →* completion X :=
⟨λ x, x⁻¹, rfl, λ x y, by induction x; induction y; refl⟩

variables {X}

@[simp] lemma inv_apply (x :  X × top) :
(((x.2 : X), (⟨x.1, set.mem_univ x.1⟩ : top)) : completion X) = x⁻¹ := rfl

@[simp] lemma coe_apply {x y : top} : (⟨x, set.mem_univ x⟩ : top) * y = ⟨x*y, set.mem_univ (x*y)⟩ :=
by tidy

@[simp] lemma one_eq {x : X} :
  ((x, (⟨x, set.mem_univ x⟩ : top)) : completion X) = 1 :=
by {rw (show x = ((⟨x, set.mem_univ x⟩ : top) : X), by tidy), apply localization.mk_self}

lemma mul_left_inv (x : completion X) : x⁻¹ * x = 1 :=
begin
  apply con.induction_on' x,
  rintro ⟨y1, y2⟩,
  rw [←inv_apply, ←localization.mk_apply, ←localization.mk_apply,
      localization.mk_mul_mk, mul_comm],
  apply one_eq,
end

instance : comm_group (completion X) :=
{  mul := (*),
   one := 1,
   one_mul := one_mul,
   mul_one := mul_one,
   mul_assoc := mul_assoc,
   inv := has_inv.inv,
   mul_left_inv := mul_left_inv,
   mul_comm := mul_comm}

lemma inj_of_group_of {G : Type*} [comm_group G] {x y : G}
(H : (x : completion G) = (y : completion G)) : x = y :=
by {cases con.eq.1 H with w hw, simp * at *}

lemma surj_of_group_of {G : Type*} [comm_group G] {y : completion G} :
  ∃ x : G, (x : completion G) = y :=
begin
  apply con.induction_on' y,
  intro z,
  use z.1*(↑z.2)⁻¹,
  simp,
  use 1,
end

end completion



/-open category_theory

namespace CommGroup

@[reducible] def CommGroup : Type (u+1) := bundled comm_group

@[reducible] def is_comm_group_hom {α : Type u} {β : Type v} [comm_group α] [comm_group β]
  (f : α → β) := is_group_hom f

instance to_comm_group (A : CommGroup) : comm_group A := A.str

instance concrete_is_comm_group_hom :
  concrete_category @is_comm_group_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance hom_is_group_hom {G₁ G₂ : CommGroup} (f : G₁ ⟶ G₂) :
  is_comm_group_hom (f : G₁ → G₂) := f.2

instance of_comm_group_hom {α : Type u} {β : Type u} [comm_group α]
  [comm_group β] (f : α →* β) : is_comm_group_hom f :=
{  to_is_mul_hom := ⟨f.3⟩}

instance to_CommGroup_hom {G₁ G₂ : CommGroup} :
  has_coe (G₁ →* G₂) (G₁ ⟶ G₂) := ⟨λ f, subtype.mk f.1 (by apply_instance)⟩

def of (X : Type u) [comm_group X] : CommGroup := ⟨X⟩

lemma id_eq {G : CommGroup} : 𝟙 G = @monoid_hom.id G _ :=
by tidy

lemma comp_eq {G H J : CommGroup} (f : G →* H) (g : H →* J) :
  (comp g f : G ⟶ J) = (f : G ⟶ H) ≫ (g : H ⟶ J) :=
by tidy

end CommGroup

namespace CommMonoid

@[reducible] def CommMonoid : Type (u+1) := bundled comm_monoid

@[reducible] def is_comm_monoid_hom {α : Type u} {β : Type v} [comm_monoid α]
[comm_monoid β] (f : α → β) := is_monoid_hom f

instance to_comm_monoid (A : CommMonoid) : comm_monoid A := A.str

instance concrete_is_monoid_hom :
  concrete_category @is_monoid_hom :=
⟨by introsI α ia; apply_instance,
  by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

instance hom_is_monoid_hom {M₁ M₂ : CommMonoid} (f : M₁ ⟶ M₂) :
  is_comm_monoid_hom (f : M₁ → M₂) := f.2


instance of_comm_monoid_hom {α : Type u} {β : Type u} [comm_monoid α]
[comm_monoid β] (f : α →* β) : is_comm_monoid_hom f :=
{ to_is_mul_hom := ⟨f.3⟩, map_one := f.2}

instance to_CommMonoid_hom {M₁ M₂ : CommMonoid} :
 has_coe (M₁ →* M₂) (M₁ ⟶ M₂) := ⟨λ f, subtype.mk f.1 (by apply_instance)⟩

def of (X : Type u) [comm_monoid X] : CommMonoid := ⟨X⟩

end CommMonoid

section
open CommMonoid CommGroup fractions

variables {D E F : CommMonoid.{w}} (X : CommMonoid.{w}) (f : D ⟶ E)
          {G H J : CommGroup.{x}} (g : G ⟶ H)

@[reducible] def to_monoid_hom : D →* E := ⟨f.1, f.2.2, f.2.1.1⟩

lemma to_monoid_hom_comp (g : E ⟶ F) :
to_monoid_hom (f ≫ g) = comp (to_monoid_hom g) (to_monoid_hom f) :=
by tidy

lemma to_monoid_hom_inj (f g : D ⟶ E) (H : to_monoid_hom f = to_monoid_hom g) : f = g :=
by tidy

lemma to_monoid_hom_eq (f : D →* E) : to_monoid_hom (subtype.mk f (by apply_instance)) = f :=
by tidy

@[reducible] noncomputable def fractions_group_hom :
  fractions (⊤ : submonoid D) →* fractions (⊤ : submonoid E) :=
mk' (group_of_fractions_hom $ comp (monoid_hom.of (⊤ : submonoid E)) $ to_monoid_hom f) $ map_mul _

@[reducible] noncomputable def to_CommGroup :
  CommGroup.of (fractions (⊤ : submonoid D)) →* CommGroup.of (fractions (⊤ : submonoid E)) :=
fractions_group_hom f

@[reducible] noncomputable def fractions_hom_map :
  CommGroup.of (fractions (⊤ : submonoid D)) ⟶ CommGroup.of (fractions (⊤ : submonoid E)) :=
to_CommGroup f

lemma comp_id_of {X : CommMonoid} :
  comp (monoid_hom.id _) (of (⊤ : submonoid X)) = of (⊤ : submonoid X) :=
by tidy

lemma group_hom_id {X : CommMonoid} :
  monoid_hom.id (CommGroup.of (fractions (⊤ : submonoid X))) = group_of_fractions_hom (of (⊤ : submonoid X)) :=
by change monoid_hom.id _ = group_of_fractions_hom (of _);
   apply group_hom_unique; exact comp_id_of

lemma group_of_fractions_hom_comp {X Y Z : CommMonoid} (f : X →* Y) (g : Y →* Z) :
  comp (comp (group_of_fractions_hom (comp (of (⊤ : submonoid Z)) g))
  (group_of_fractions_hom $ comp (of (⊤ : submonoid Y)) f)) (of (⊤ : submonoid X)) =
  comp (of (⊤ : submonoid Z)) (comp g f) :=
begin
  rw [group_hom_comp, comp_assoc],
  exact eq_of_of_comp_group_hom (comp (comp (of _) g) f),
end

lemma fractions_hom_id {X : CommMonoid} :
  (fractions_hom_map (𝟙 X)) = 𝟙 (CommGroup.of (fractions ⊤)) :=
begin
  rw id_eq,
  ext,
  change group_of_fractions_hom (monoid_hom.comp (monoid_hom.of (⊤ : submonoid X))
         (to_monoid_hom (𝟙 X))) x = monoid_hom.id (CommGroup.of (fractions (⊤ : submonoid X))) x,
  rw [group_hom_id, coe_apply, coe_apply],
  congr,
end

lemma fractions_hom_comp {X Y Z : CommMonoid} (f : X ⟶ Y) (g : Y ⟶ Z) :
  fractions_hom_map f ≫ fractions_hom_map g  = fractions_hom_map (f ≫ g) :=
begin
  rw ←comp_eq,
  congr,
  change comp (group_of_fractions_hom _) (group_of_fractions_hom _) =
         group_of_fractions_hom _,
  apply group_hom_unique,
  rw [to_monoid_hom_comp, group_of_fractions_hom_comp],
end

@[reducible] noncomputable def fractions_functor  : CommMonoid.{u} ⥤ CommGroup.{u} :=
{  obj := λ M, of (fractions (⊤ : submonoid M)),
   map := λ _ _ f, fractions_hom_map f,
   map_id' := λ _, fractions_hom_id,
   map_comp' := λ _ _ _ f g, (fractions_hom_comp f g).symm}



/-
@[reducible] def forget_to_CommMonoid : CommGroup.{u} ⥤ CommMonoid.{u} :=
{  obj := λ G : CommGroup, @CommMonoid.of
                (G : Type u) (comm_group.to_comm_monoid G),
   map := λ X Y f, (subtype.mk (to_monoid_hom f : (CommMonoid.of X →* CommMonoid.of Y)) (by apply_instance))}


@[reducible] noncomputable def hom_equiv_to_fun {X : CommMonoid} {Y : CommGroup} (f : fractions_functor.obj X ⟶ Y) :
  X ⟶ forget_to_CommMonoid.obj Y :=
subtype.mk (monoid_hom.comp (monoid_hom.of (⊤ : submonoid X))
  (to_monoid_hom f : (monoid_hom (fractions_functor.obj X : Type u) Y))) (by apply_instance)


instance forget_CommGroup (G : CommGroup) : comm_group (forget_to_CommMonoid.obj G) := G.str
instance forget_is_group_hom {G H : CommGroup} (f : G ⟶ H) : is_group_hom (forget_to_CommMonoid.map f) := f.property
instance monoid_of_forget (G : CommGroup) : comm_monoid (forget_to_CommMonoid.obj G) := infer_instance
instance forget_monoid_hom {M : CommMonoid} {G : CommGroup} (f : M ⟶ forget_to_CommMonoid.obj G) :
  is_monoid_hom f := f.property

def id_of_forget {Y : CommGroup} : forget_to_CommMonoid.obj Y →m Y :=
{  to_fun := λ y, (y : Y),
   mul := by tidy,
   one := by tidy}

@[reducible] noncomputable def hom_equiv_inv_fun {X : CommMonoid} {Y : CommGroup} (f : X ⟶ forget_to_CommMonoid.obj Y) :
  fractions_functor.obj X ⟶ Y :=
subtype.mk (group_of_fractions_hom (monoid_hom.comp (to_monoid_hom f) id_of_forget)) (by apply_instance)

lemma hom_equiv_left_inv {X : CommMonoid} {Y : CommGroup} (f : fractions_functor.obj X ⟶ Y) :
f = hom_equiv_inv_fun (hom_equiv_to_fun f) :=
by apply to_group_hom_inj; rw to_group_hom_eq; apply group_hom_unique; tidy

lemma hom_equiv_right_inv {X : CommMonoid} {Y : CommGroup} (f : X ⟶ forget_to_CommMonoid.obj Y) :
f = hom_equiv_to_fun (hom_equiv_inv_fun f) :=
by apply to_monoid_hom_inj;
   rw [to_monoid_hom_eq, hom_equiv_inv_fun, to_group_hom_eq, eq_of_of_comp_group_hom]; tidy

@[reducible] noncomputable def hom_equiv (X : CommMonoid) (Y : CommGroup) :
  (fractions_functor.obj X ⟶ Y) ≃ (X ⟶ forget_to_CommMonoid.obj Y) :=
⟨ hom_equiv_to_fun, hom_equiv_inv_fun, λ f,
  by rw ←(hom_equiv_left_inv f), λ f, by rw ←(hom_equiv_right_inv f)⟩

lemma hom_equiv_naturality_left_symm' {X' X : CommMonoid} {Y : CommGroup}
  (f : X' ⟶ X) (g : X ⟶ forget_to_CommMonoid.obj Y) :
  (hom_equiv X' Y).symm (f ≫ g) = fractions_functor.map f ≫ (hom_equiv X Y).symm g :=
begin
   rw [subtype.ext, equiv.coe_fn_symm_mk, equiv.coe_fn_symm_mk, bundled.concrete_category_comp],
   simp only [],
   rw (show monoid_hom.comp (to_monoid_hom (f ≫ g)) id_of_forget =
            monoid_hom.comp (to_monoid_hom f)
            (monoid_hom.comp (to_monoid_hom g) id_of_forget), by tidy),
   change _ = _ ∘ (group_of_fractions_hom (monoid_hom.comp (to_monoid_hom f) (monoid_hom.of ⊤))),
   rw ←group_hom.comp_eq,
   exact group_hom.eq_of_fun _ _
     ((group_hom_comp (monoid_hom.comp (to_monoid_hom g) id_of_forget) (to_monoid_hom f)).symm),
end

noncomputable def fractions_adj_core : adjunction.core_hom_equiv fractions_functor forget_to_CommMonoid :=
⟨λ X Y, hom_equiv X Y, λ X' X Y, hom_equiv_naturality_left_symm', λ X Y Y', by tidy⟩

noncomputable def fractions_adjunction : adjunction fractions_functor forget_to_CommMonoid :=
adjunction.mk_of_hom_equiv fractions_adj_core

end


section
open localization localization.fraction_ring classical
variables (R : Type u) [integral_domain R] [decidable_eq R]

def non_zero_divisors' : submonoid R :=
⟨non_zero_divisors R, λ z hz, by rwa monoid.mul_one at hz,
 λ x₁ x₂ hx₁ hx₂ z hz,
 have z * x₁ * x₂ = 0, by rwa monoid.mul_assoc,
 hx₁ z $ hx₂ (z * x₁) this⟩

lemma ne_zero_of_non_zero_divisors' {x : non_zero_divisors' R} : (x : R) ≠ 0 :=
λ hm, absurd (x.2 1 (by rw [hm.symm, monoid.one_mul]; finish)).symm zero_ne_one

local notation `fracR` := fractions (⊤ : submonoid (non_zero_divisors' R))
variables {R}
lemma of_inv_eq {x : non_zero_divisors' R} : (of (x : R) :  fraction_ring R)⁻¹ = mk 1 x :=
by tidy

lemma ne_zero_of {x : non_zero_divisors' R} : (of x : fraction_ring R) ≠ 0 :=
λ h, absurd (of.injective (by rwa ←of_zero at h)) (ne_zero_of_non_zero_divisors' R)

variables (R)

@[reducible] def fraction_ring_map : non_zero_divisors' R →* units (fraction_ring R) :=
⟨λ r, to_units r, by tidy, λ x y, by tidy⟩

variables {R}

lemma map_eq : ⇑(fraction_ring_map R) = λ r, to_units r := rfl

lemma fraction_ring_mk_apply
  (x : R × non_zero_divisors R) : localization.mk x.1 x.2 = ⟦x⟧ :=
by tidy

@[reducible] def aux_nonzero (a : R × non_zero_divisors' R) (Ha : a.1 ∈ non_zero_divisors' R) :
  non_zero_divisors' R × (⊤ : submonoid (non_zero_divisors' R)) :=
prod.mk (⟨a.1, Ha⟩ : non_zero_divisors' R) (⟨a.2, mem_top a.2⟩ : (⊤ : submonoid (non_zero_divisors' R)))

lemma ne_zero_aux (a : R × non_zero_divisors R) (Ha : a.1 ≠ 0) : (localization.mk a.1 a.2) ≠ 0 :=
λ h, absurd
(by rw [mk_eq, units.inv_eq_inv, to_units_coe, mul_eq_zero, inv_eq_zero, ←coe_zero] at h;
    exact or.elim h (λ hl, of.injective (show of a.1 = of 0, from hl))
      (λ hr, absurd (of.injective (show localization.of ↑a.2 = _, from hr))
                    (ne_zero_of_non_zero_divisors' R))) Ha

lemma surjective_aux (a : R × non_zero_divisors R) (Ha : a.1 ≠ 0) :
  units.mk0 (localization.mk a.1 a.2) (ne_zero_aux a Ha) =
  (to_units (aux_nonzero a (mem_non_zero_divisors_iff_ne_zero.2 Ha)).1)*(to_units a.2)⁻¹ :=
by tidy

lemma eq_aux (x : fracR) :
aux (⊤ : submonoid (non_zero_divisors' R)) (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) x =
(fraction_ring_map R x.2)⁻¹ * (fraction_ring_map R x.1) :=
begin
sorry,
end

#exit

lemma surjective_fraction_hom : ∀ x≠(0 : fraction_ring R), ∃ y : fracR, units.mk0 x H =
  fractions_hom ⊤ (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) y :=
begin
intro x,
apply quotient.induction_on x,
intros,
have ha0 : a.1 ≠ 0, from λ h, absurd (eq.refl 0)
  (by rw [←fraction_ring_mk_apply, mk_eq, h, coe_zero, zero_mul, ne.def] at H; finish),
use fractions.mk (⊤ : submonoid (non_zero_divisors' R)) (aux_nonzero a (mem_coe.2 (mem_non_zero_divisors_iff_ne_zero.2 ha0))),
conv {to_lhs, congr, rw ←fraction_ring_mk_apply a},-- skip, whnf, rw aux_nonzero, simp only [map_eq]},
rw surjective_aux a ha0, rw coe_apply,
simp [map_eq], rw aux_nonzero,
conv {to_rhs, congr, whnf, congr, rw eq_of_left_inv (fraction_ring_map R (x.2 : _ )) (classical.some_spec _ _) (mul_left_inv _), simp, },
rw aux_nonzero,simp,
--suffices Hu : units.mk0 ⟦a⟧ H = (fraction_ring_map (aux_nonzero a this).1) * (fraction_ring_map (aux_nonzero a this).2)⁻¹, by
 --{simp * at *},
end

lemma universal_pred_of_fraction_ring :
  universal_pred ⊤ (fraction_ring_map R) (λ x, ⟨(fraction_ring_map R x)⁻¹, mul_left_inv _⟩) :=
sorry

def fractions_group_equiv : (units (fraction_ring R)) ≃* fractions (non_zero_divisors' R) :=
sorry

end


-/-/
