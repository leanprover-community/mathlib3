import algebra.group group_theory.subgroup
import category_theory.instances.groups
import category_theory.functor_category
import data.set.function

universes v v₁ v₂ v₃ u u₁ u₂ u₃ -- declare the `v`'s first; see `category_theory.category` for an explanation

def translate (n : ℤ) : ℤ ⥤ ℤ :=
{ obj := λ i, i + n,
  map := by tidy }

namespace category_theory
open set is_group_hom instances
variables (C : Type u₁) [𝒞 : category.{v₁} C]
include 𝒞

def sequence := ℤ ⥤ C

namespace sequence

instance : category (sequence C) := functor.category _ _

variables {C} (X : sequence C)

def delta (i : ℤ) {i' : ℤ} (h : i = i' . obviously) :
  X.obj i' ⟶ X.obj (i'+1) :=
X.map $ by tidy

section
variables (obj : ℤ → C) (map : Π i, obj i ⟶ obj (i+1))
include obj map

def comp_of_delta {i : ℤ} : Π (k : ℕ), obj i ⟶ obj (i + k) :=
nat.rec _ _
-- | 0     := by convert 𝟙 _; simp
-- | (n+1) := _

def mk_of_delta : sequence C :=
{ obj := obj,
  map := _,
  map_id' := _,
  map_comp' := _ }

end

def shift (n : ℤ) : sequence C ⥤ sequence C :=
{ obj := λ X, (translate n) ⋙ X,
  map := λ X Y f, whisker_left _ f }

omit 𝒞
variable (A : sequence Group)

#print delta

def is_complex :=
∀ (i : ℤ), range (@delta _ _ A (i-1) _ begin exact rfl, end) ⊆
  ker (@delta _ _ A i (i-1+1) begin by tidy end)

def is_bounded_below_by (n : ℤ) :=
∀ i < n, A.obj i ≅ 1

end sequence

end category_theory



local attribute [instance] classical.prop_decidable



namespace group

structure sequence :=
(obj : ℤ → Type u)
(grp : Π i, group $ obj i)
(map : Π i, obj i → obj (i+1))
(hom : Π i, is_group_hom $ map i)

namespace sequence
open set is_group_hom

variable (A : sequence)

instance (i : ℤ) : group $ A.obj i := A.grp i

instance (i : ℤ) : is_group_hom $ A.map i := A.hom i

def is_complex : Prop :=
∀ i, A.map _ ∘ A.map (i-1) = λ a, 1

def is_bounded_below : Prop :=
∃ n, ∀ i ≤ n, subsingleton $ A.obj i

def is_bounded_above : Prop :=
∃ n, ∀ i ≥ n, subsingleton $ A.obj i

def is_exact_at (i : ℤ) : Prop :=
range (A.map (i-1)) = ker (A.map _)

def is_exact : Prop :=
∀ i, A.is_exact_at i

lemma is_complex_of_is_exact (h : A.is_exact) :
A.is_complex :=
begin
  intro i,
  funext a,
  delta function.comp,
  rw ← mem_ker _,
  have := h i,
  delta is_exact_at at this,
  rw ← this,
  exact mem_range_self _,
end

def is_short_exact : Prop :=
∃ n,
  (∀ i < (n-1), subsingleton $ A.obj i) ∧
  (∀ i > (n+1), subsingleton $ A.obj i) ∧
  A.is_exact_at (n-1) ∧
  A.is_exact_at n ∧
  A.is_exact_at (n+1)

def is_left_exact : Prop :=
∃ n,
  (∀ i < (n-1), subsingleton $ A.obj i) ∧
  (∀ i > (n+1), subsingleton $ A.obj i) ∧
  A.is_exact_at (n-1) ∧
  A.is_exact_at n

def is_right_exact : Prop :=
∃ n,
  (∀ i < (n-1), subsingleton $ A.obj i) ∧
  (∀ i > (n+1), subsingleton $ A.obj i) ∧
  A.is_exact_at n ∧
  A.is_exact_at (n+1)

lemma is_exact_at_of_subsingleton (i : ℤ) [h : subsingleton (A.obj i)] :
  A.is_exact_at i :=
begin
  have : (i : ℤ) = i - 1 + 1, by simp,
  rw this at h,
  ext a,
  replace : a = 1,
    resetI,
    apply subsingleton.elim,
  rw this,
  split; intro H;
  apply is_submonoid.one_mem,
end

lemma is_short_exact_iff :
  A.is_short_exact ↔ A.is_left_exact ∧ A.is_right_exact :=
begin
  split; intro h,
  { rcases h with ⟨n,below,above,left,middle,right⟩,
    repeat {split}, assumption' },
  { rcases h with ⟨⟨n₁,below₁,above₁,left₁,middle₁⟩,
                   ⟨n₂,below₂,above₂,middle₂,right₂⟩⟩,
    refine ⟨n₁,below₁,above₁,left₁,middle₁,_⟩,
    by_contradiction,
    have claim₁ : ¬ subsingleton (A.obj $ n₁ + 1),
      intro, resetI, apply a,
      apply is_exact_at_of_subsingleton,
    have claim₂ : ¬ n₁ + 1 > n₂ + 1,
      intro, apply claim₁, apply above₂, assumption,
    simp at *,
  }
end




end sequence

end group
