import category_theory.graded_object
import category_theory.abelian.additive_functor
import data.int.basic
/-!
!!!This file is not by me; I copied and pasted it from the LTE repo so I could
use the new complexes.!!!

# Complexes of objects in a category

This file contains an experimental definition of a complex of objects
in a category. There is a "lawless" version `differential_object` (which
Scott says should be called something else) and an extension
of this called `complex_like` (assuming the underlying category is
preadditive) which contains the hypothesis d^2=0.
One rather strange thing to note here is that these complexes
have maps d : X_i → X_j for all i and j, and these maps are assumed
to be zero if i ≠ j + 1 (resp. j ≠ i + 1, depending on a boolean
input which says which way the maps are going). The concept of a
homotopy is also defined.

-/

open category_theory category_theory.limits

section succ_pred

/-
=== ATTENTION ===

Consider using `has_succ_rel` which should be a relation
that says that `i` and `j` are a "successive pair".
That way, we can even put a `has_succ_rel` on types like `fin n`,
where there is a last element, that doesn't have a proper successor.
-/

variables (α : Type*)

class has_succ := (succ : α → α)

class has_succ_pred extends α ≃ α.

instance has_succ_pred.has_succ [e : has_succ_pred α] : has_succ α :=
⟨e.to_equiv⟩

variables {α}

-- fix this to something better?
def succ [has_succ α] (a : α) := has_succ.succ a
def succ_equiv (α) [has_succ_pred α] : equiv.perm α := has_succ_pred.to_equiv
def pred [has_succ_pred α] (a : α) := (succ_equiv α).symm a

variables [has_succ_pred α] (a : α)

@[simp] lemma coe_succ_equiv : (succ_equiv α : α → α) = succ := rfl

lemma succ_equiv_apply : succ_equiv α a = succ a := rfl

@[simp] lemma succ_pred : succ (pred a) = a :=
equiv.apply_symm_apply _ a

@[simp] lemma pred_succ : pred (succ a) = a :=
equiv.symm_apply_apply _ a

-- do we want this for every semiring??
instance : has_succ ℕ := ⟨λ n, n + 1⟩
instance : has_succ_pred ℤ :=
{ to_fun := λ n, n + 1,
  inv_fun := λ n, n - 1,
  left_inv := λ n, add_sub_cancel n 1,
  right_inv := λ n, sub_add_cancel n 1 }

@[simp] lemma succ_nat (n : ℕ) : succ n = n + 1 := rfl
@[simp] lemma succ_int (n : ℤ) : succ n = n + 1 := rfl
@[simp] lemma pred_int (n : ℤ) : pred n = n - 1 := rfl

end succ_pred

@[ext]
structure differential_object (ι : Type) (V : Type*) [category V] :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)

variables (ι : Type) (V : Type*) {cov : bool}

namespace differential_object
variables [category V]

variables{ι V} (C C₁ C₂ C₃ : differential_object ι V)

section category

@[ext]
structure hom :=
(f (i : ι) : C₁.X i ⟶ C₂.X i)
(comm (i j : ι) : C₁.d i j ≫ f j = f i ≫ C₂.d i j)

attribute [reassoc] hom.comm

variables {C₁ C₂ C₃}

protected def id : hom C C :=
{ f := λ i, 𝟙 _,
  comm := by { intros, rw [category.id_comp, category.comp_id] } }

def comp (f : hom C₁ C₂) (g : hom C₂ C₃) : hom C₁ C₃ :=
{ f := λ i, f.f i ≫ g.f i,
  comm := λ i j, by { rw [hom.comm_assoc, hom.comm, category.assoc] } }

instance : category (differential_object ι V) :=
{ hom := hom,
  id := differential_object.id,
  comp := λ _ _ _, comp,
  id_comp' := by { intros, ext, exact category.id_comp _ },
  comp_id' := by { intros, ext, exact category.comp_id _ },
  assoc' := by { intros, ext, dsimp [id, comp], rw [category.assoc] } }

@[simp] lemma id_f (i : ι) : (𝟙 C : C ⟶ C).f i = 𝟙 (C.X i) := rfl

@[simp] lemma comp_f (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i := rfl

@[simp, reassoc]
lemma eq_to_hom_f (f : C₁ ⟶ C₂) (i j : ι) (h : i = j) :
  eq_to_hom (congr_arg _ h) ≫ f.f j = f.f i ≫ eq_to_hom (congr_arg _ h) :=
by { cases h, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simp, reassoc]
lemma eq_to_hom_d (i i' j j' : ι) :
  ∀ (hi : i = i') (hj : j = j'),
  eq_to_hom (congr_arg _ hi) ≫ C.d i' j' = C.d i j ≫ eq_to_hom (congr_arg _ hj) :=
by { rintro rfl rfl, simp only [eq_to_hom_refl, category.id_comp, category.comp_id] }

@[simps]
def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { rw [← comp_f, f.hom_inv_id, id_f] },
  inv_hom_id' := by { rw [← comp_f, f.inv_hom_id, id_f] } }

@[simps]
def iso_of_components (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, C₁.d i j ≫ (f j).hom = (f i).hom ≫ C₂.d i j) :
  C₁ ≅ C₂ :=
{ hom :=
  { f := λ i, (f i).hom,
    comm := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm := λ i j,
    calc C₂.d i j ≫ (f j).inv
        = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv : by simp
    ... = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv : by rw hf
    ... = (f i).inv ≫ C₁.d i j : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

instance [has_zero_morphisms V] : has_zero_morphisms (differential_object ι V) :=
{ has_zero := λ C₁ C₂, ⟨{ f := λ i, 0, comm := λ _ _, by rw [zero_comp, comp_zero] }⟩,
  comp_zero' := by { intros, ext, rw [comp_f, comp_zero] },
  zero_comp' := by { intros, ext, rw [comp_f, zero_comp] } }

section preadditive

open category_theory.preadditive

variables [preadditive V]

instance : has_add (C₁ ⟶ C₂) :=
⟨λ f g, { f := λ i, f.f i + g.f i, comm := λ i j, by rw [comp_add, add_comp, f.comm, g.comm] }⟩

instance : has_sub (C₁ ⟶ C₂) :=
⟨λ f g, { f := λ i, f.f i - g.f i, comm := λ i j, by rw [comp_sub, sub_comp, f.comm, g.comm] }⟩

instance : has_neg (C₁ ⟶ C₂) :=
⟨λ f, { f := λ i, -f.f i, comm := λ i j, by rw [comp_neg, neg_comp, f.comm] }⟩

@[simp] lemma add_f (f g : C₁ ⟶ C₂) (i : ι) : (f + g).f i = f.f i + g.f i := rfl

@[simp] lemma sub_f (f g : C₁ ⟶ C₂) (i : ι) : (f - g).f i = f.f i - g.f i := rfl

@[simp] lemma neg_f (f : C₁ ⟶ C₂) (i : ι) : (-f).f i = -f.f i := rfl

instance : add_comm_group (C₁ ⟶ C₂) :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  sub := has_sub.sub,
  add_assoc := by { intros, ext, apply add_assoc },
  zero_add := by { intros, ext, apply zero_add },
  add_zero := by { intros, ext, apply add_zero },
  sub_eq_add_neg := by {intros, ext, apply sub_eq_add_neg },
  add_left_neg := by {intros, ext, apply add_left_neg },
  add_comm := by {intros, ext, apply add_comm } }

variables (ι V)

instance : preadditive (differential_object ι V) :=
{ hom_group := λ C₁ C₂, infer_instance,
  add_comp' := by { intros, ext, simp only [comp_f, add_f, add_comp] },
  comp_add' := by { intros, ext, simp only [comp_f, add_f, comp_add] } }

@[simps]
def shift [has_succ ι] :
  differential_object ι V ⥤ differential_object ι V :=
{ obj := λ C,
  { X := λ i, C.X (succ i),
    d := λ i j, -C.d _ _ },
  map := λ C₁ C₂ f,
  { f := λ i, f.f (succ i),
    comm := λ i j, by simp only [neg_comp, comp_neg, neg_inj, f.comm] } }

@[simps]
def iso_shift' [has_succ ι] (C : differential_object ι V) (i : ι) :
  ((shift ι V).obj C).X i ≅ C.X (succ i) := iso.refl _

variables [has_succ_pred ι]

instance : has_shift (differential_object ι V) :=
{ shift :=
  { functor := shift ι V,
    inverse := @shift ι V _ _ ⟨pred⟩,
    unit_iso := nat_iso.of_components
      (λ C, iso_of_components (λ i, eq_to_iso $ congr_arg C.X $ (succ_pred i).symm)
        (λ i j, by { dsimp, rw [neg_neg, eq_to_hom_d] }))
      (λ C₁ C₂ f, by { ext i, dsimp, rw [eq_to_hom_f] }),
    counit_iso := nat_iso.of_components
      (λ C, iso_of_components (λ i, eq_to_iso $ congr_arg C.X $ pred_succ i)
        (λ i j, by { dsimp, rw [neg_neg, ← eq_to_hom_d] }))
      (λ C₁ C₂ f, by { ext i, dsimp, rw [← eq_to_hom_f] }),
    functor_unit_iso_comp' :=
    by { intros, ext i, dsimp, simp only [eq_to_hom_refl, eq_to_hom_trans] } } }
.

variables {ι V}

@[simps] def iso_shift_zero : C⟦0⟧ ≅ C := iso.refl _

@[simps] def iso_shift_one (i : ι) : C⟦1⟧.X i ≅ C.X (succ i) := iso.refl _

@[simps] def iso_shift_neg_one (i : ι) : C⟦-1⟧.X i ≅ C.X (pred i) := iso.refl _

-- #print equivalence.int.has_pow

-- def iso_shift : ∀ (i : ι) (n : ℤ), C⟦n⟧.X i ≅ C.X (((succ_equiv ι)^n : equiv.perm ι) i)
-- | i (0:ℕ)       := iso_app (iso_shift_zero _) i
-- | i (1:ℕ)       := iso_shift_one _ _
-- | i (n+2:ℕ)     :=
--  by { simp,
--   change (((category_theory.shift (differential_object ι V)).trans
--    (category_theory.shift (differential_object ι V))^((n+1:ℕ) : ℤ)).functor.obj C).X i ≅ _,
--   let f := iso_shift (succ i) (n+1),  }
-- | i -[1+ 0]     := iso_shift_neg_one _ _
-- | i -[1+ (n+1)] := _

end preadditive

variables (ι V)

@[simps]
def forget : differential_object ι V ⥤ graded_object ι V :=
{ obj := λ C, C.X,
  map := λ _ _ f, f.f }

end category

end differential_object
namespace differential_object

variables {ι V} [has_succ ι] [category V] [has_zero_morphisms V]

def coherent_indices : Π (cov : bool) (i j : ι), Prop
| ff i j := i = succ j
| tt i j := succ i = j

variables (ι V)

set_option old_structure_cmd true

@[ext]
structure complex_like (cov : bool) extends differential_object ι V :=
(d_comp_d : ∀ i j k, d i j ≫ d j k = 0)
(d_eq_zero : ∀ ⦃i j⦄, ¬ coherent_indices cov i j → d i j = 0)

@[simp]
lemma complex_like.to_differential_object_X {cov : bool} (BD : complex_like ι V cov) :
  (complex_like.to_differential_object BD).X = BD.X := rfl

@[simp]
lemma complex_like.to_differential_object_d {cov : bool} (BD : complex_like ι V cov) :
  (complex_like.to_differential_object BD).d = BD.d := rfl

attribute [reassoc] complex_like.d_comp_d

variables {ι V}

theorem complex_like.ext' {C D : complex_like ι V cov}
  (H : ∀ i j, coherent_indices cov i j → arrow.mk (C.d i j) = arrow.mk (D.d i j)) : C = D :=
begin
  cases C,
  cases D,
  cases show C_X = D_X, by {
    ext i,
    cases cov,
    { exact congr_arg comma.right (H _ i rfl) },
    { exact congr_arg comma.left (H i _ rfl) } },
  congr, ext i j,
  by_cases coherent_indices cov i j,
  { injection H i j h, exact eq_of_heq h_3 },
  { simp only [C_d_eq_zero h, D_d_eq_zero h] }
end

instance coherent_indices_decidable [decidable_eq ι] (cov : bool) (i j : ι) :
  decidable (coherent_indices cov i j) :=
by { cases cov; dsimp [coherent_indices]; apply_instance }

instance : category (complex_like ι V cov) :=
induced_category.category complex_like.to_differential_object

-- generalise this to arbitrary induced categories
instance [has_zero_morphisms V] : has_zero_morphisms (complex_like ι V cov) :=
{ has_zero := λ C₁ C₂,
  show has_zero (C₁.to_differential_object ⟶ C₂.to_differential_object), by apply_instance,
  comp_zero' := λ _ _ _ _, comp_zero,
  zero_comp' := λ _ _ _ _, zero_comp }

-- generalise this to arbitrary induced categories
instance [preadditive V] : preadditive (complex_like ι V cov) :=
{ hom_group := λ C₁ C₂,
  show add_comm_group (C₁.to_differential_object ⟶ C₂.to_differential_object), by apply_instance,
  add_comp' := by { intros, apply preadditive.add_comp },
  comp_add' := by { intros, apply preadditive.comp_add } }

variables {C₁ C₂ : complex_like ι V cov}

@[simps]
def hom.mk' (f : Π i, C₁.X i ⟶ C₂.X i)
  (hf : ∀ i j, coherent_indices cov i j → C₁.d i j ≫ f j = f i ≫ C₂.d i j) :
  C₁ ⟶ C₂ :=
{ f := f,
  comm := λ i j,
  begin
    by_cases h : coherent_indices cov i j,
    { exact hf i j h },
    { show C₁.d i j ≫ f j = f i ≫ C₂.d i j,
      rw [C₁.d_eq_zero h, C₂.d_eq_zero h, zero_comp, comp_zero] }
  end }

variables (C₁ C₂)
/- More flexible homs.? -/
@[ext]
structure hom' :=
(f (i j : ι) : C₁.X i ⟶ C₂.X j)
(f_eq_zero (i j : ι) (h : i ≠ j) : f i j = 0)
(comm (i j k l : ι) : j = k → i = l → C₁.d i j ≫ f j k = f i l ≫ C₂.d l k)

variables {C₁ C₂}

def hom'.to_hom (f : hom' C₁ C₂) : C₁ ⟶ C₂ :=
{ f := λ i, f.f i i,
  comm := λ i j, f.comm i j j i rfl rfl }

@[simps]
def complex_like.iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
{ hom := f.hom.f i,
  inv := f.inv.f i,
  hom_inv_id' := by { erw [← comp_f, f.hom_inv_id, id_f], refl },
  inv_hom_id' := by { erw [← comp_f, f.inv_hom_id, id_f], refl } }

structure is_complex_like (C : differential_object ι V) (cov : bool) : Prop :=
(d_comp_d : ∀ i j k, C.d i j ≫ C.d j k = 0)
(d_eq_zero : ∀ ⦃i j⦄, ¬ coherent_indices cov i j → C.d i j = 0)

abbreviation is_cochain_complex (C : differential_object ι V) := C.is_complex_like tt
abbreviation is_chain_complex (C : differential_object ι V) := C.is_complex_like ff

lemma complex_like.is_complex_like (X : complex_like ι V cov) :
  X.to_differential_object.is_complex_like cov :=
{ .. X }

lemma is_complex_like.iso {C₁ C₂ : differential_object ι V}
  (h : C₁.is_complex_like cov) (f : C₁ ≅ C₂) :
  C₂.is_complex_like cov :=
{ d_comp_d := λ i j k,
  begin
    calc C₂.d i j ≫ C₂.d j k
        = C₂.d i j ≫ C₂.d j k ≫ f.inv.f k ≫ f.hom.f k : _
    ... = f.inv.f i ≫ C₁.d i j ≫ C₁.d j k ≫ f.hom.f k : _
    ... = 0 : _,
    { rw [← comp_f, f.inv_hom_id, id_f, category.comp_id] },
    { simp only [f.inv.comm_assoc] },
    { slice_lhs 2 3 { rw h.d_comp_d }, rw [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij,
  begin
    calc C₂.d i j = C₂.d i j ≫ f.inv.f j ≫ f.hom.f j : _
    ... = 0 : _,
    { rw [← comp_f, f.inv_hom_id, id_f, category.comp_id] },
    { rw [f.inv.comm_assoc, h.d_eq_zero hij, zero_comp, comp_zero] }
  end }

@[simps]
def mk_complex_like (C : differential_object ι V) (hC : C.is_complex_like cov) :
  complex_like ι V cov :=
{ .. C, .. hC }

@[simps]
def mk_complex_like_iso (C : differential_object ι V) (hC : C.is_complex_like cov) :
  (induced_functor complex_like.to_differential_object).obj (C.mk_complex_like hC) ≅ C :=
eq_to_iso $ by { cases C, refl }

section lift_functor

variables {C : Type*} [category C] (F : C ⥤ differential_object ι V)

@[simps]
def lift_functor (h : ∀ X, (F.obj X).is_complex_like cov) :
  C ⥤ complex_like ι V cov :=
{ obj := λ X, (F.obj X).mk_complex_like (h X),
  map := λ X Y f, show ((F.obj X).mk_complex_like (h X)).to_differential_object ⟶ _,
    from ((F.obj X).mk_complex_like_iso (h X)).hom ≫ F.map f ≫
         ((F.obj Y).mk_complex_like_iso (h Y)).inv,
  map_id' := λ X,
  by { dsimp, simp only [category.id_comp, category_theory.functor.map_id,
    eq_to_hom_refl, eq_to_hom_trans], refl },
  map_comp' := λ X Y Z f g,
  begin
    dsimp,
    erw [category.assoc, category.assoc, eq_to_hom_trans_assoc, eq_to_hom_refl,
      category.id_comp, category_theory.functor.map_comp, category.assoc]
  end }

@[simps]
def lift_functor_nat_iso (h : ∀ X, (F.obj X).is_complex_like cov) :
  (lift_functor F h) ⋙ (induced_functor complex_like.to_differential_object) ≅ F :=
nat_iso.of_components (λ X, mk_complex_like_iso _ _) $ λ X Y f,
by { rw [← iso.eq_comp_inv, category.assoc], refl }

lemma lift_functor_d (h : ∀ X, (F.obj X).is_complex_like cov) (x : C) (i j : ι) :
  ((lift_functor F h).obj x).d i j = (F.obj x).d i j :=
rfl

end lift_functor

-- this is a major pain, but we might not need it
def lift_equivalence (F : differential_object ι V ≌ differential_object ι V)
  (h : ∀ X, (F.functor.obj X).is_complex_like cov ↔ X.is_complex_like cov) :
  complex_like ι V cov ≌ complex_like ι V cov :=
{ functor := lift_functor ((induced_functor complex_like.to_differential_object) ⋙ F.functor) $
    by { intro X, dsimp, rw h, exact X.is_complex_like },
  inverse := lift_functor ((induced_functor complex_like.to_differential_object) ⋙ F.inverse) $
    by { intro X, dsimp, rw ← h, apply X.is_complex_like.iso, exact (F.counit_iso.app _).symm },
  unit_iso := nat_iso.of_components sorry sorry,
  counit_iso := sorry,
  functor_unit_iso_comp' := sorry }

end differential_object

namespace differential_object

namespace complex_like

instance has_zero_morphisms'
  {T : Type*} [category V] [preadditive V] [category T] :
  has_zero_morphisms (T ⥤ V) :=
{ has_zero := λ X Y, { zero :=
  { app := λ Z, 0,
    naturality' := λ x y z, by rw [zero_comp, comp_zero] } },
  comp_zero' := λ X Y f Z, by ext; simp only [comp_zero, nat_trans.comp_app],
  zero_comp' := λ X Y Z f, by ext; simp only [zero_comp, nat_trans.comp_app]}
/-- A complex of functors gives a functor to complexes

jmc: This is functorial, but I'm getting timeouts, and I think this is all we need -/
def as_functor {T : Type*} [has_succ ι] [category V] [preadditive V] [category T]
  (C : complex_like ι (T ⥤ V) cov) :
  T ⥤ complex_like ι V cov :=
{ obj := λ t,
  { X := λ i, (C.X i).obj t,
    d := λ i j, (C.d i j).app t,
    d_comp_d := λ i j k,
    begin
      have := C.d_comp_d i j k,
      rw [nat_trans.ext_iff, function.funext_iff] at this,
      exact this t
    end,
    d_eq_zero := λ i j h,
    begin
      have := C.d_eq_zero h,
      rw [nat_trans.ext_iff, function.funext_iff] at this,
      exact this t
    end },
  map := λ t₁ t₂ h,
  { f := λ i, (C.X i).map h,
    comm := λ i j, show (C.d i j).app t₁ ≫ (C.X j).map h = (C.X i).map h ≫ (C.d i j).app t₂,
      by rw [nat_trans.naturality] },
  map_id' := λ t, by { ext i, dsimp, rw (C.X i).map_id, refl },
  map_comp' := λ t₁ t₂ t₃ h₁ h₂, by { ext i, dsimp, rw functor.map_comp, refl } }

section shift

variables [has_succ_pred ι] [category V] [preadditive V]

open category_theory.preadditive

@[simps]
def shift : complex_like ι V cov ⥤ complex_like ι V cov :=
lift_functor ((induced_functor complex_like.to_differential_object) ⋙ shift ι V)
begin
  rintro ⟨X, d, h1, h2⟩,
  split; dsimp,
  { intros i j k, simp only [neg_comp, comp_neg, neg_neg], apply h1 },
  { intros i j hij, rw neg_eq_zero, apply h2,
    intro H, apply hij,
    cases cov; dsimp [coherent_indices] at H ⊢; apply (succ_equiv ι).injective; exact H }
end

lemma shift_d (C : complex_like ι V cov) (i j : ι) :
  ((shift _ _).obj C).d i j = -C.d (succ i) (succ j) :=
rfl

instance shift.additive : (shift ι V : complex_like ι V cov ⥤ complex_like ι V cov).additive :=
{ map_zero' :=
  by { rintro ⟨⟩ ⟨⟩, ext, dsimp [shift], simp only [category.id_comp, category.comp_id], refl },
  map_add' :=
  by { rintro ⟨⟩ ⟨⟩ f g, ext, dsimp [shift], simp only [category.id_comp, category.comp_id] } }


-- this is a major pain, but we might not need it
instance : has_shift (differential_object.complex_like ι V cov) :=
 { shift := differential_object.lift_equivalence (category_theory.shift _) $ λ X,
   begin
     admit
   end }

end shift

open category_theory.preadditive

variables {ι V} [has_succ ι] [category V] [preadditive V]

@[simps]
def f_hom {C₁ C₂ : complex_like ι V cov} (i : ι) : (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
add_monoid_hom.mk' (λ f, differential_object.hom.f f i) (λ _ _, rfl)

@[simps]
def iso_of_components {C₁ C₂ : complex_like ι V cov} (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, C₁.d i j ≫ (f j).hom = (f i).hom ≫ C₂.d i j) :
  C₁ ≅ C₂ :=
{ hom :=
  { f := λ i, (f i).hom,
    comm := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm := λ i j,
    calc C₂.d i j ≫ (f j).inv
        = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv : by simp
    ... = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv : by rw hf
    ... = (f i).inv ≫ C₁.d i j : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

def htpy_idx_rel₁ (cov : bool) (i j : ι) :=
(coherent_indices cov i j) ∨ ((∀ k, ¬ coherent_indices cov k j) ∧ i = j)

def htpy_idx_rel₂ (cov : bool) (i j : ι) :=
(coherent_indices cov i j) ∨ ((∀ k, ¬ coherent_indices cov j k) ∧ i = j)

@[simp] lemma htpy_idx_rel₁_ff_nat (i j : ℕ) :
  htpy_idx_rel₁ ff i j ↔ i = j + 1 :=
begin
  dsimp [htpy_idx_rel₁, coherent_indices, succ_nat],
  simp only [← not_exists, exists_eq, not_true, or_false, false_and],
end

@[simp] lemma htpy_idx_rel₂_ff_nat (j k : ℕ) :
  htpy_idx_rel₂ ff j k ↔ j = k + 1 ∨ (j = 0 ∧ k = 0) :=
begin
  dsimp [htpy_idx_rel₂, coherent_indices, succ_nat],
  refine or_congr iff.rfl ⟨_, _⟩,
  { rintro ⟨hjk, rfl⟩,
    rw and_self,
    cases j, { refl },
    exact (hjk j rfl).elim },
  { rintro ⟨rfl, rfl⟩,
    refine ⟨_, rfl⟩,
    intro i, exact (nat.succ_ne_zero i).symm }
end

@[simp] lemma htpy_idx_rel₁_tt_nat (i j : ℕ) :
  htpy_idx_rel₁ tt i j ↔ i + 1 = j ∨ (i = 0 ∧ j = 0) :=
begin
  dsimp [htpy_idx_rel₁, coherent_indices, succ_nat],
  refine or_congr iff.rfl ⟨_, _⟩,
  { rintro ⟨hij, rfl⟩,
    rw and_self,
    cases i, { refl },
    exact (hij i rfl).elim },
  { rintro ⟨rfl, rfl⟩, exact ⟨nat.succ_ne_zero, rfl⟩ }
end

@[simp] lemma htpy_idx_rel₂_tt_nat (j k : ℕ) :
  htpy_idx_rel₂ tt j k ↔ j + 1 = k :=
begin
  dsimp [htpy_idx_rel₂, coherent_indices, succ_nat],
  simp only [← not_exists, exists_eq', not_true, or_false, false_and],
end

structure homotopy {C₁ C₂ : complex_like ι V cov} (f g : C₁ ⟶ C₂) :=
(h : Π j i, C₁.X j ⟶ C₂.X i)
(h_eq_zero : ∀ i j, ¬ coherent_indices cov i j → h j i = 0)
(comm : ∀ i j k, htpy_idx_rel₁ cov i j → htpy_idx_rel₂ cov j k →
  h j i ≫ C₂.d i j + C₁.d j k ≫ h k j = f.f j - g.f j)

variables {C₁ C₂ C₃ : complex_like ι V cov} {f g f₁ g₁ f' f'' : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}

@[reassoc] lemma h_comp_d (h : homotopy f g) (i j k : ι)
  (hij: htpy_idx_rel₁ cov i j) (hjk: htpy_idx_rel₂ cov j k) :
  h.h j i ≫ C₂.d i j = f.f j - g.f j - C₁.d j k ≫ h.h k j :=
begin
  rw eq_sub_iff_add_eq,
  exact h.comm i j k hij hjk
end

@[reassoc] lemma d_comp_h (h : homotopy f g) (i j k : ι)
  (hij: htpy_idx_rel₁ cov i j) (hjk: htpy_idx_rel₂ cov j k) :
  C₁.d j k ≫ h.h k j = f.f j - g.f j - h.h j i ≫ C₂.d i j :=
begin
  rw [eq_sub_iff_add_eq, add_comm],
  exact h.comm i j k hij hjk
end

@[simps]
def homotopy.of_eq (h : f = g) : homotopy f g :=
{ h := 0,
  h_eq_zero := λ _ _ _, rfl,
  comm := by { intros, simp only [add_zero, zero_comp, pi.zero_apply, comp_zero, sub_self, h] } }

@[simps] def homotopy.refl : homotopy f f := homotopy.of_eq rfl

@[simps]
def homotopy.symm (h : homotopy f g) : homotopy g f :=
{ h := λ j i, -h.h j i,
  h_eq_zero := λ i j hij, by rw [h.h_eq_zero i j hij, neg_zero],
  comm := λ i j k hij hjk,
    by simp only [neg_comp, comp_neg, ← neg_add, h.comm i j k hij hjk, neg_sub] }

@[simps]
def homotopy.trans (h : homotopy f f') (h' : homotopy f' f'') : homotopy f f'' :=
{ h := λ j i, h.h j i + h'.h j i,
  h_eq_zero := λ i j hij, by rw [h.h_eq_zero i j hij, h'.h_eq_zero i j hij, add_zero],
  comm :=
  begin
    intros i j k hij hjk,
    calc (h.h j i + h'.h j i) ≫ C₂.d i j + C₁.d j k ≫ (h.h k j + h'.h k j)
        = h.h j i ≫ C₂.d i j + h'.h j i ≫ C₂.d i j +
            (C₁.d j k ≫ h.h k j + C₁.d j k ≫ h'.h k j) : by rw [add_comp, comp_add]
    ... = h.h j i ≫ C₂.d i j + C₁.d j k ≫ h.h k j +
            (h'.h j i ≫ C₂.d i j + C₁.d j k ≫ h'.h k j) : by abel
    ... = f.f j - f'.f j + (f'.f j - f''.f j) : by rw [h.comm i j k hij hjk, h'.comm i j k hij hjk]
    ... = f.f j - f''.f j : by abel
  end }

@[simps]
def homotopy.comp_const (h : homotopy f₁ g₁) (f₂ : C₂ ⟶ C₃) : homotopy (f₁ ≫ f₂) (g₁ ≫ f₂) :=
{ h := λ j i, h.h j i ≫ f₂.f i,
  h_eq_zero := λ i j hij, by rw [h.h_eq_zero i j hij, zero_comp],
  comm :=
  begin
    intros i j k hij hjk,
    calc (h.h j i ≫ f₂.f i) ≫ C₃.d i j + C₁.d j k ≫ h.h k j ≫ f₂.f j
        = (h.h j i ≫ C₂.d i j + C₁.d j k ≫ h.h k j) ≫ f₂.f j : _
    ... = (f₁.f j - g₁.f j) ≫ f₂.f j : by rw [h.comm i j k hij hjk]
    ... = (f₁ ≫ f₂).f j - (g₁ ≫ f₂).f j : by erw [comp_f, comp_f, sub_comp],
    simp only [add_comp, category.assoc],
    erw [f₂.comm]; refl
  end }

@[simps]
def homotopy.const_comp (f₁ : C₁ ⟶ C₂) (h : homotopy f₂ g₂) : homotopy (f₁ ≫ f₂) (f₁ ≫ g₂) :=
{ h := λ j i, f₁.f j ≫ h.h j i,
  h_eq_zero := λ i j hij, by rw [h.h_eq_zero i j hij, comp_zero],
  comm :=
  begin
    intros i j k hij hjk,
    calc (f₁.f j ≫ h.h j i) ≫ C₃.d i j + C₁.d j k ≫ f₁.f k ≫ h.h k j
        = f₁.f j ≫ (h.h j i ≫ C₃.d i j + C₂.d j k ≫ h.h k j) : _
    ... = f₁.f j ≫ (f₂.f j - g₂.f j) : by rw [h.comm i j k hij hjk]
    ... = (f₁ ≫ f₂).f j - (f₁ ≫ g₂).f j : by erw [comp_f, comp_f, comp_sub],
    simp only [comp_add, ← category.assoc],
    erw [f₁.comm]; refl
  end }

@[simps]
def homotopy.comp (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
(h₁.comp_const _).trans (h₂.const_comp _)

end complex_like

end differential_object

section

variables (ι V) [has_succ ι] [category V] [has_zero_morphisms V]

abbreviation cochain_complex := differential_object.complex_like ι V tt
abbreviation chain_complex := differential_object.complex_like ι V ff

end

namespace cochain_complex

variables {ι V} [decidable_eq ι] [has_succ ι] [category V] [has_zero_morphisms V]

@[simps]
def mk' (X : ι → V) (d : Π i, X i ⟶ X (succ i)) (h : ∀ i, d i ≫ d (succ i) = 0) :
  cochain_complex ι V :=
{ X := X,
  d := λ i j, if h : succ i = j then d i ≫ eq_to_hom (congr_arg _ h) else 0,
  d_comp_d := λ i j k,
  begin
    split_ifs with h1 h2,
    { subst k, subst j, simp only [category.comp_id, eq_to_hom_refl, h] },
    all_goals { simp only [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij, dif_neg hij }

@[simp] lemma mk'_d' (X : ι → V) (d : Π i, X i ⟶ X (succ i))
  (h : ∀ i, d i ≫ d (succ i) = 0) (i : ι) :
  (mk' X d h).d i (succ i) = d i :=
calc (mk' X d h).d i (succ i)
    = d i ≫ eq_to_hom (congr_arg _ rfl) : dif_pos rfl
... = d i : by simp only [category.comp_id, eq_to_hom_refl]

theorem ext {C D : cochain_complex ι V}
  (H : ∀ i, arrow.mk (C.d i (succ i)) = arrow.mk (D.d i (succ i))) : C = D :=
differential_object.complex_like.ext' $ by rintro _ _ ⟨⟩; apply H

end cochain_complex

namespace chain_complex

variables {ι V} [decidable_eq ι] [has_succ ι] [category V] [has_zero_morphisms V]

@[simps]
def mk' (X : ι → V) (d : Π i, X (succ i) ⟶ X i) (h : ∀ i, d (succ i) ≫ d i = 0) :
  chain_complex ι V :=
{ X := X,
  d := λ i j, if h : i = succ j then eq_to_hom (congr_arg _ h) ≫ d j else 0,
  d_comp_d := λ i j k,
  begin
    split_ifs with h1 h2,
    { subst i, subst j, simp only [category.id_comp, eq_to_hom_refl, h] },
    all_goals { simp only [zero_comp, comp_zero] }
  end,
  d_eq_zero := λ i j hij, dif_neg hij }

@[simp] lemma mk'_d' (X : ι → V) (d : Π i, X (succ i) ⟶ X i)
  (h : ∀ i, d (succ i) ≫ d i = 0) (i : ι) :
  (mk' X d h).d (succ i) i = d i :=
calc (mk' X d h).d (succ i) i
    = eq_to_hom (congr_arg _ rfl) ≫ d i : dif_pos rfl
... = d i : by simp only [category.id_comp, eq_to_hom_refl]

theorem ext {C D : chain_complex ι V}
  (H : ∀ i, arrow.mk (C.d (succ i) i) = arrow.mk (D.d (succ i) i)) : C = D :=
differential_object.complex_like.ext' $ by rintro _ _ ⟨⟩; apply H

end chain_complex

namespace category_theory

open differential_object (complex_like)

variables {ι} {V₁ V₂ : Type*} [category V₁] [category V₂]

section has_zero_morphisms
variables [has_zero_morphisms V₁] [has_zero_morphisms V₂]

@[simps]
def functor.map_differential_object (F : V₁ ⥤ V₂) :
  differential_object ι V₁ ⥤ differential_object ι V₂ :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    d := λ i j, F.map (C.d i j) },
  map := λ C₁ C₂ f,
  { f := λ i, F.map (f.f i),
    comm := λ i j, by simp only [← F.map_comp, f.comm] },
  map_id' := by { intros, ext, exact F.map_id _ },
  map_comp' := by { intros, ext, exact F.map_comp _ _ } }

@[simps]
def functor.map_complex_like' [has_succ ι] (F : V₁ ⥤ V₂) (hF : ∀ x y, F.map (0 : x ⟶ y) = 0) :
  complex_like ι V₁ cov ⥤ complex_like ι V₂ cov :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    d := λ i j, F.map (C.d i j),
    d_comp_d := λ _ _ _, by simp only [← F.map_comp, C.d_comp_d, hF],
    d_eq_zero := λ _ _ h, by simp only [C.d_eq_zero h, hF] },
  map := λ C₁ C₂ f, (F.map_differential_object.map f),
  map_id' := by { intros, ext, exact F.map_id _ },
  map_comp' := by { intros, ext, exact F.map_comp _ _ } }

@[simps]
def functor.map_complex_like_nat_trans' [has_succ ι]
  (F G : V₁ ⥤ V₂) (hF : ∀ x y, F.map (0 : x ⟶ y) = 0) (hG : ∀ x y, G.map (0 : x ⟶ y) = 0)
  (α : F ⟶ G) :
  F.map_complex_like' hF ⟶ (G.map_complex_like' hG : complex_like ι V₁ cov ⥤ _) :=
{ app := λ C,
  { f := λ i, α.app _,
    comm := λ i j, α.naturality _ },
  naturality' := λ C₁ C₂ f, by { ext i, exact α.naturality _ } }

end has_zero_morphisms

section preadditive
variables [preadditive V₁] [preadditive V₂]

@[simps]
def functor.map_complex_like [has_succ ι] (F : V₁ ⥤ V₂) [F.additive] :
  complex_like ι V₁ cov ⥤ complex_like ι V₂ cov :=
F.map_complex_like' $ λ x y, functor.additive.map_zero'

@[simps]
def functor.map_complex_like_nat_trans [has_succ ι] (F G : V₁ ⥤ V₂) [F.additive] [G.additive]
  (α : F ⟶ G) :
  F.map_complex_like ⟶ (G.map_complex_like : complex_like ι V₁ cov ⥤ _) :=
functor.map_complex_like_nat_trans' _ _ _ _ α

end preadditive

end category_theory
