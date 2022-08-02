import group_theory.group_action.basic
import algebra.module.ulift

variables (M : Type*) [monoid M]
variables (A : Type*) [add_monoid A] [distrib_mul_action M A]
variables (A' : Type*) [add_group A'] [distrib_mul_action M A']
variables (B : Type*) [add_monoid B] [distrib_mul_action M B]
variables (B' : Type*) [add_group B'] [distrib_mul_action M B']
variables (C : Type*) [add_monoid C] [distrib_mul_action M C]
variables (R : Type*) [semiring R] [mul_semiring_action M R]
variables (R' : Type*) [ring R'] [mul_semiring_action M R']
variables (S : Type*) [semiring S] [mul_semiring_action M S]
variables (S' : Type*) [ring S'] [mul_semiring_action M S']
variables (T : Type*) [semiring T] [mul_semiring_action M T]
variables (G : Type*) [group G] (H : subgroup G)

set_option old_structure_cmd true

@[ancestor add_equiv distrib_mul_action_hom]
structure distrib_mul_action_equiv extends equiv A B, distrib_mul_action_hom M A B

notation A ` ≃+[`:25 M:25 `] `:0 B:0 := distrib_mul_action_equiv M A B

namespace distrib_mul_action_equiv

instance : has_coe_to_fun (A ≃+[M] B) _ :=
⟨distrib_mul_action_equiv.to_fun⟩

variables {M A B}

def to_add_equiv (f : A ≃+[M] B) : A ≃+ B :=
{ map_add' := f.map_add',
  ..f.to_equiv }

@[simp]
lemma to_fun_eq_coe {f : A ≃+[M] B} : f.to_fun = f := rfl

@[simp]
lemma coe_to_equiv {f : A ≃+[M] B} : ⇑f.to_equiv = f := rfl

@[simp]
lemma coe_to_distrib_mul_action_hom {f : A ≃+[M] B} : ⇑f.to_distrib_mul_action_hom = f := rfl

@[simp]
lemma coe_to_add_equiv {f : A ≃+[M] B} :  ⇑f.to_add_equiv = f := rfl

@[simp]
lemma map_add (f : A ≃+[M] B) : ∀ x y, f (x + y) = f x + f y := f.map_add'

@[simp]
lemma map_smul (f : A ≃+[M] B) : ∀ (r : M) x, f (r • x) = r • f x := f.map_smul'

@[simp]
lemma map_zero (h : A ≃+[M] B) : h 0 = 0 := h.map_zero'

@[simp]
lemma map_eq_zero_iff (h : A ≃+[M] B) {x : A} :
  h x = 0 ↔ x = 0 :=
h.map_zero ▸ h.to_equiv.apply_eq_iff_eq

def mk' (f : A ≃ B) (hsmul : ∀ (r : M) x, f (r • x) = r • f x)
  (hadd : ∀ x y, f (x + y) = f x + f y) : A ≃+[M] B :=
⟨f.1, f.2, f.3, f.4, hsmul,
begin
  rw [←add_zero (f.1 0), ←f.apply_symm_apply 0],
  show f 0 + _ = _,
  rw [←hadd, zero_add],
end,
  hadd⟩

protected lemma bijective (e : A ≃+[M] B) : function.bijective e := e.to_equiv.bijective

protected lemma injective (e : A ≃+[M] B) : function.injective e := e.to_equiv.injective

protected lemma surjective (e : A ≃+[M] B) : function.surjective e := e.to_equiv.surjective

variables (M A)
@[refl]
def refl : A ≃+[M] A :=
{ map_smul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  ..equiv.refl _ }

instance : inhabited (A ≃+[M] A) := ⟨refl M A⟩

variables {M A}

@[symm]
def symm (h : A ≃+[M] B) : B ≃+[M] A :=
{ map_smul' := (h.to_distrib_mul_action_hom.inverse h.to_equiv.symm h.left_inv h.right_inv).map_smul,
  map_zero' := (h.to_distrib_mul_action_hom.inverse h.to_equiv.symm h.left_inv h.right_inv).map_zero,
  map_add' := (h.to_distrib_mul_action_hom.inverse h.to_equiv.symm h.left_inv h.right_inv).map_add,
  .. h.to_equiv.symm }

--/-- See Note [custom simps projection] -/
def simps.symm_apply (e : A ≃+[M] B) : B → A := e.symm

initialize_simps_projections distrib_mul_action_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp]
theorem to_equiv_symm (f : A ≃+[M] B) : f.symm.to_equiv = f.to_equiv.symm := rfl

@[simp]
theorem coe_mk (f : A → B) (g h₁ h₂) (h₃ : ∀ (r : M) x, f (r • x) = r • f x) (h₄ h₅) :
  ⇑(distrib_mul_action_equiv.mk f g h₁ h₂ h₃ h₄ h₅) = f := rfl

@[simp]
lemma symm_symm : ∀ (f : A ≃+[M] B), f.symm.symm = f
| ⟨f, g, h₁, h₂, h₃, h₄, h₅⟩ := rfl

lemma symm_bijective : function.bijective (symm : (A ≃+[M] B) → (B ≃+[M] A)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp]
theorem symm_mk (f : A → B) (g h₁ h₂) (h₃ : ∀ (r : M) x, f (r • x) = r • f x) (h₄ h₅) :
  (distrib_mul_action_equiv.mk f g h₁ h₂ h₃ h₄ h₅).symm =
  { to_fun := g, inv_fun := f, ..(distrib_mul_action_equiv.mk f g h₁ h₂ h₃ h₄ h₅).symm} := rfl

variables {C}
@[trans]
def trans (h1 : A ≃+[M] B) (h2 : B ≃+[M] C) : (A ≃+[M] C) :=
{ map_smul' := λ r x, show h2 (h1 (r • x)) = r • h2 (h1 x),
    by rw [h1.map_smul, h2.map_smul],
  map_zero' := show h2 (h1 0) = 0, by rw [h1.map_zero, h2.map_zero],
  map_add' := λ x y, show h2 (h1 (x + y)) = h2 (h1 x) + h2 (h1 y),
    by rw [h1.map_add, h2.map_add],
  ..h1.to_equiv.trans h2.to_equiv }

@[simp]
lemma apply_symm_apply (e : A ≃+[M] B) : ∀ y, e (e.symm y) = y :=
e.to_equiv.apply_symm_apply

@[simp]
lemma symm_apply_apply (e : A ≃+[M] B) : ∀ x, e.symm (e x) = x :=
e.to_equiv.symm_apply_apply

@[simp]
theorem symm_comp_self (e : A ≃+[M] B) : e.symm ∘ e = id := funext e.symm_apply_apply

@[simp]
theorem self_comp_symm (e : A ≃+[M] B) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp]
theorem coe_refl : ⇑(refl M A) = id := rfl


theorem refl_apply (m : A) : refl M A m = m := rfl

@[simp]
theorem coe_trans (e₁ : A ≃+[M] B) (e₂ : B ≃+[M] C) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ := rfl


theorem trans_apply (e₁ : A ≃+[M] B) (e₂ : B ≃+[M] C) (m : A) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[simp] theorem apply_eq_iff_eq (e : A ≃+[M] B) {x y : A} : e x = e y ↔ x = y :=
e.injective.eq_iff

lemma apply_eq_iff_symm_apply (e : A ≃+[M] B) {x : A} {y : B} : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

lemma symm_apply_eq (e : A ≃+[M] B) {x y} : e.symm x = y ↔ x = e y :=
e.to_equiv.symm_apply_eq

lemma eq_symm_apply (e : A ≃+[M] B) {x y} : y = e.symm x ↔ e y = x :=
e.to_equiv.eq_symm_apply

@[ext]
lemma ext {f g : A ≃+[M] B} (h : ∀ x, f x = g x) : f = g :=
begin
  have h₁ : f.to_equiv = g.to_equiv := equiv.ext h,
  cases f, cases g, congr,
  { exact (funext h) },
  { exact congr_arg equiv.inv_fun h₁ }
end

lemma ext_iff {f g : A ≃+[M] B} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, ext⟩

@[simp] lemma mk_coe (e : A ≃+[M] B) (e' h₁ h₂ h₃ h₄ h₅) :
  (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A ≃+[M] B) = e := ext $ λ _, rfl

@[simp] lemma mk_coe' (e : A ≃+[M] B) (f h₁ h₂ h₃ h₄ h₅) :
  (distrib_mul_action_equiv.mk f ⇑e h₁ h₂ h₃ h₄ h₅ : B ≃+[M] A) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

protected lemma congr_arg {f : A ≃+[M] B} : Π {x x' : A}, x = x' → f x = f x'
| _ _ rfl := rfl

protected lemma congr_fun {f g : A ≃+[M] B} (h : f = g) (x : A) : f x = g x := h ▸ rfl

-- not sure I should have all these instance variables
def distrib_mul_action_equiv_of_unique_of_unique
  [unique A] [unique B] : A ≃+[M] B :=
{ map_smul' := λ _ _ , subsingleton.elim _ _,
  map_zero' := subsingleton.elim _ _,
  map_add' := λ _ _, subsingleton.elim _ _,
  ..equiv.equiv_of_unique _ _ }

instance [unique A] [unique B] : unique (A ≃+[M] B) :=
{ default := distrib_mul_action_equiv_of_unique_of_unique ,
  uniq := λ _, ext $ λ x, subsingleton.elim _ _}

end distrib_mul_action_equiv
namespace ulift

def distrib_mul_action_equiv : ulift A ≃+[M] A :=
{ to_fun := ulift.down,
  inv_fun := ulift.up,
  map_zero' := rfl,
  map_add' := λ x y, rfl,
  map_smul' := λ m x, rfl,
  left_inv := ulift.up_down,
  right_inv := ulift.down_up }


end ulift
