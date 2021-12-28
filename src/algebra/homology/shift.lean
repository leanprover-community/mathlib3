import category_theory.shift
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import data.int.parity
import tactic.ring

-- move this section
namespace int

def neg_one_pow (n : ℤ) : ℤ := @has_pow.pow (units ℤ) ℤ _ (-1) n

@[simp] lemma neg_one_pow_add (n m : ℤ) : neg_one_pow (n + m) = neg_one_pow n * neg_one_pow m :=
by { delta neg_one_pow, rw zpow_add, simp }

@[simp] lemma neg_one_pow_one : neg_one_pow 1 = -1 := rfl

@[simp] lemma neg_one_pow_neg_one : neg_one_pow (-1) = -1 := rfl

@[simp] lemma neg_one_pow_neg_zero : neg_one_pow 0 = 1 := rfl

lemma neg_one_pow_ite (n : ℤ) : neg_one_pow n = if even n then 1 else -1 :=
begin
  induction n using int.induction_on with n h n h,
  { simp [neg_one_pow] },
  { simp [h, apply_ite has_neg.neg] with parity_simps },
  { rw [sub_eq_add_neg, neg_one_pow_add],
    simp [h, apply_ite has_neg.neg] with parity_simps }
end

lemma neg_one_pow_eq_pow_abs (n : ℤ) : neg_one_pow n = (-1) ^ n.nat_abs :=
begin
  rw neg_one_pow_ite,
  convert (neg_one_pow_ite n.nat_abs).symm using 2,
  { simp with parity_simps },
  { delta neg_one_pow, simp }
end

lemma neg_one_pow_eq_neg_one_npow (n : ℕ) : neg_one_pow n = (-1) ^ n :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_neg (n : ℤ) : neg_one_pow (-n) = neg_one_pow n :=
by simp [neg_one_pow_ite] with parity_simps

@[simp] lemma neg_one_pow_sub (n m : ℤ) : neg_one_pow (n - m) = neg_one_pow n * neg_one_pow m :=
by rw [sub_eq_neg_add, neg_one_pow_add, neg_one_pow_neg, mul_comm]

@[simp] lemma neg_one_pow_mul_self (n : ℤ) : neg_one_pow n * neg_one_pow n = 1 :=
by { delta neg_one_pow, simp }

@[simp] lemma neg_one_pow_smul_self {α : Type*} [add_comm_group α] (n : ℤ) (X : α) :
  neg_one_pow n • neg_one_pow n • X = X :=
by simp [smul_smul]

end int

universes v u

open category_theory category_theory.limits category_theory.preadditive

variables (V : Type u) [category.{v} V] [preadditive V]

namespace homological_complex

lemma complex_shape.up'_add_right_cancel {α : Type*} [add_cancel_comm_monoid α] (a : α)
  {i j} (k : α) : (complex_shape.up' a).rel (i+k) (j+k) ↔ (complex_shape.up' a).rel i j :=
by { dsimp, rw [add_assoc, add_comm k a, ← add_assoc], exact add_left_inj _ }

lemma complex_shape.up_add_right_cancel {α : Type*} [add_cancel_comm_monoid α] [has_one α]
  {i j} (k : α) : (complex_shape.up α).rel (i+k) (j+k) ↔ (complex_shape.up α).rel i j :=
complex_shape.up'_add_right_cancel 1 k

local attribute [simp] zsmul_comp comp_zsmul

@[simps]
def shift_functor (n : ℤ) : cochain_complex V ℤ ⥤ cochain_complex V ℤ :=
{ obj := λ X,
  { X := λ i, X.X (i + n),
    d := λ i j, n.neg_one_pow • X.d _ _,
    shape' := λ i j h, by { rw [X.shape (i+n) (j+n), smul_zero],
      rwa complex_shape.up_add_right_cancel } },
  map := λ X Y f, { f := λ i, f.f _ } }

.

variables {V} {ι : Type*} {c : complex_shape ι}

-- @[simps]
-- def iso_of_components {X Y : homological_complex V c} (e : Π i, X.X i ≅ Y.X i)
--   (h : ∀ i j, c.rel i j → (e i).hom ≫ Y.d i j = X.d i j ≫ (e j).hom) : X ≅ Y :=
-- { hom := { f := λ i, (e i).hom },
--   inv := { f := λ i, (e i).inv,
--     comm' := λ i j r, by { rwa [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, h] } } }
-- .

def X_eq_to_iso (X : homological_complex V c) {i j : ι} (h : i = j) : X.X i ≅ X.X j :=
eq_to_iso $ congr_arg X.X h

@[simp]
lemma X_eq_to_iso_inv (X : homological_complex V c) {i j : ι} (h : i = j) :
  (X.X_eq_to_iso h).inv = (X.X_eq_to_iso h.symm).hom := rfl

@[simp, reassoc]
lemma X_eq_to_iso_d (X : homological_complex V c) {i j k : ι} (h : i = j) :
  (X.X_eq_to_iso h).hom ≫ X.d j k = X.d i k := by { subst h, exact category.id_comp _ }

@[simp, reassoc]
lemma X_d_eq_to_iso (X : homological_complex V c) {i j k : ι} (h : j = k) :
  X.d i j ≫ (X.X_eq_to_iso h).hom = X.d i k := by { subst h, exact category.comp_id _ }

@[simp, reassoc]
lemma X_eq_to_iso_trans (X : homological_complex V c) {i j k : ι} (h : i = j) (h' : j = k) :
  (X.X_eq_to_iso h).hom ≫ (X.X_eq_to_iso h').hom = (X.X_eq_to_iso (h.trans h')).hom :=
by { simp [X_eq_to_iso] }

@[simp]
lemma X_eq_to_iso_refl (X : homological_complex V c) {i : ι} :
  (X.X_eq_to_iso (refl i)).hom = 𝟙 _ := rfl

@[simp, reassoc]
lemma X_eq_to_iso_f {X Y : homological_complex V c} (f : X ⟶ Y) {i j : ι} (h : i = j) :
  (X.X_eq_to_iso h).hom ≫ f.f j = f.f i ≫ (Y.X_eq_to_iso h).hom :=
by { subst h, simp [X_eq_to_iso] }

@[simp]
lemma eq_to_hom_f {X Y : homological_complex V c} (h : X = Y) (i) :
  hom.f (eq_to_hom h) i = eq_to_hom (by rw h) := by { subst h, simp }

variables (V)

instance : has_shift (cochain_complex V ℤ) ℤ :=
has_shift_mk _ _
{ F := shift_functor V,
  ε := nat_iso.of_components (λ X, hom.iso_of_components (λ i, X.X_eq_to_iso (add_zero _).symm)
    (λ i j r, by { dsimp, simp })) (λ X Y f, by { ext, dsimp, simp }),
  μ := λ n m, nat_iso.of_components (λ X, hom.iso_of_components
    (λ i, X.X_eq_to_iso (by rw [add_comm n m, add_assoc]))
    (λ i j r, by { dsimp, simp [smul_smul, mul_comm] })) (λ i j f, by { ext, dsimp, simp }),
  associativity := λ m₁ m₂ m₃ X, by { ext, dsimp, simp [X_eq_to_iso] },
  left_unitality := λ n X, by { ext, dsimp, simpa [X_eq_to_iso] },
  right_unitality := λ n X, by { ext, dsimp, simpa [X_eq_to_iso] } }
.

local attribute[instance] endofunctor_monoidal_category

@[simp] lemma shift_X (X : cochain_complex V ℤ) (n m : ℤ) :
  (X⟦n⟧).X m = X.X (m + n) := rfl

@[simp] lemma shift_d (X : cochain_complex V ℤ) (n i j : ℤ) :
  (X⟦n⟧).d i j = n.neg_one_pow • X.d (i + n) (j + n) := rfl

@[simp] lemma shift_f {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (n i : ℤ) :
  (f⟦n⟧').f i = f.f (i + n) := rfl

instance (n : ℤ) : functor.additive ((shift_monoidal_functor (cochain_complex V ℤ) ℤ).obj n) := {}
instance shift_functor_additive (n : ℤ) : functor.additive (shift_functor V n) := {}

variable {V}

def homotopy_shift {X Y : cochain_complex V ℤ} {f g : X ⟶ Y} (h : homotopy f g) (n : ℤ)  :
  homotopy (f⟦n⟧') (g⟦n⟧') :=
{ hom := λ i j, n.neg_one_pow • h.hom _ _,
  zero' := λ i j r, by { rw ← complex_shape.up_add_right_cancel n at r, simp [h.zero _ _ r] },
  comm := λ i, begin
    dsimp,
    suffices : X.d (i + n) (i + n + 1) ≫ h.hom (i + n + 1) (i + n) +
      h.hom (i + n) (i + n - 1) ≫ Y.d (i + n - 1) (i + n) =
      X.d (i + n) (i + 1 + n) ≫ h.hom (i + 1 + n) (i + n) +
      h.hom (i + n) (i - 1 + n) ≫ Y.d (i - 1 + n) (i + n),
    { simpa [h.comm (i+n), d_next, prev_d, add_right_inj] },
    congr' 3; ring,
  end }

variable (V)

def homotopy_category.shift_functor (n : ℤ) :
  (homotopy_category V (complex_shape.up ℤ)) ⥤ (homotopy_category V (complex_shape.up ℤ)) :=
category_theory.quotient.lift _ (shift_functor _ n ⋙ homotopy_category.quotient _ _)
begin
  rintros X Y f g ⟨h⟩,
  apply homotopy_category.eq_of_homotopy,
  exact homotopy_shift h n,
end

def homotopy_category.shift_ε :
  𝟭 _ ≅ homotopy_category.shift_functor V 0 :=
begin
  refine nat_iso.of_components _ _,
  { rintro ⟨X⟩,
    refine (homotopy_category.quotient _ _).map_iso (hom.iso_of_components _ _),
    exact (λ i, X.X_eq_to_iso (add_zero _).symm),
    { introv, dsimp, simp } },
  { rintro ⟨X⟩ ⟨Y⟩ f, dsimp,
    rw ← homotopy_category.quotient_map_out f,
    erw quotient.lift_map_functor_map,
    simp only [functor.comp_map, ← functor.map_comp],
    congr' 1, ext, dsimp, simp }
end

def homotopy_category.shift_functor_add (n m : ℤ) :
  homotopy_category.shift_functor V n ⋙ homotopy_category.shift_functor V m ≅
    homotopy_category.shift_functor V (n + m) :=
begin
  refine nat_iso.of_components _ _,
  { rintro ⟨X⟩,
    refine (homotopy_category.quotient _ _).map_iso (hom.iso_of_components _ _),
    exact (λ i, X.X_eq_to_iso (by rw [add_comm n m, add_assoc])),
    { introv r, dsimp [homotopy_category.shift_functor], simp [smul_smul, mul_comm] } },
  { rintro ⟨X⟩ ⟨Y⟩ f, dsimp,
    rw ← homotopy_category.quotient_map_out f,
    erw quotient.lift_map_functor_map,
    conv_rhs { erw quotient.lift_map_functor_map },
    simp only [functor.comp_map, ← functor.map_comp],
    congr' 1, ext, dsimp, simp }
end
.

@[simp]
lemma homotopy_category.shift_functor_obj_as {X : cochain_complex V ℤ} (n : ℤ) :
  (homotopy_category.shift_functor V n).obj ⟨X⟩ = ⟨X⟦n⟧⟩ := rfl

@[simp]
lemma homotopy_category.shift_functor_map_quotient (n : ℤ) {X Y : cochain_complex V ℤ} (f : X ⟶ Y) :
  (homotopy_category.shift_functor V n).map ((homotopy_category.quotient V _).map f) =
  (homotopy_category.quotient V _).map (f⟦n⟧') := rfl

lemma quotient_eq_to_hom {X Y : homotopy_category V (complex_shape.up ℤ)} (h : X = Y) :
  eq_to_hom h = (homotopy_category.quotient V (complex_shape.up ℤ)).map (eq_to_hom (by rw h)) :=
by { subst h, simpa }

instance homotopy_category.has_shift : has_shift (homotopy_category V (complex_shape.up ℤ)) ℤ :=
has_shift_mk _ _
{ F := homotopy_category.shift_functor V,
  ε := homotopy_category.shift_ε V,
  μ := homotopy_category.shift_functor_add V,
  associativity := λ m₁ m₂ m₃ ⟨X⟩, by { dsimp [homotopy_category.shift_functor_add],
    rw quotient_eq_to_hom, simp only [← functor.map_comp], congr' 1, ext, simp [X_eq_to_iso] },
  left_unitality := λ n ⟨X⟩, by { dsimp [homotopy_category.shift_ε,
    homotopy_category.shift_functor_add], rw quotient_eq_to_hom, simp only [← functor.map_comp],
    congr' 1, ext, simp [X_eq_to_iso] },
  right_unitality := λ n ⟨X⟩, by { dsimp [homotopy_category.shift_ε,
    homotopy_category.shift_functor_add], rw quotient_eq_to_hom, simp only [← functor.map_comp],
    congr' 1, ext, simp [X_eq_to_iso] } }
.
@[simp] lemma homotopy_category.quotient_obj_shift (X : cochain_complex V ℤ) (n : ℤ) :
  ((homotopy_category.quotient V _).obj X)⟦n⟧ = ⟨X⟦n⟧⟩ := rfl

@[simp] lemma homotopy_category.shift_as (X : homotopy_category V (complex_shape.up ℤ)) (n : ℤ) :
  (X⟦n⟧).as = X.as⟦n⟧ := rfl

@[simp] lemma homotopy_category.quotient_map_shift {X Y : cochain_complex V ℤ} (f : X ⟶ Y) (n : ℤ) :
  ((homotopy_category.quotient V _).map f)⟦n⟧' = (homotopy_category.quotient V _).map (f⟦n⟧') := rfl


end homological_complex
