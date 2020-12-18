--import order.boolean_algebra
--import algebra.algebra.basic
import order.filter.ultrafilter
import order.filter.partial
import topology.basic
--import order.lattice
--import data.finset.basic

open set filter classical
open_locale classical filter
--set_option old_structure_cmd true

--variables {α : Type*}

--#check (0 : α)
--#check (1 : α)
--#check distrib α

--variables {X : Type*}
--#check (distrib_lattice X)

/-- A `sus` on `α`. -/
@[protect_proj, ext] structure sus (α : Type*) :=
(is_su       : set α → Prop)
(is_su_univ  : is_su univ)
(is_su_empty : is_su ∅)
(is_su_inter : ∀s t, is_su s → is_su t → is_su (s ∩ t))
(is_su_union : ∀s t, is_su s → is_su t → is_su (s ∪ t))

attribute [class] sus

/-- A constructor for `sus` using complements of the given `sus` structure. -/
def sus.comp {α : Type*} (f : sus α) : sus α :=
{ is_su       := λ X, f.is_su Xᶜ,
  is_su_univ  := by simp [sus.is_su_empty],
  is_su_empty := by simp [sus.is_su_univ],
  is_su_inter := λ s t hs ht, by { rw compl_inter, exact sus.is_su_union f sᶜ tᶜ hs ht },
  is_su_union := λ s t hs ht, by { rw compl_union, exact sus.is_su_inter f sᶜ tᶜ hs ht },
}

section sus

variables {α : Type*} {β : Type*} {ι : Sort*} {a : α} {s s₁ s₂ : set α} {p p₁ p₂ : α → Prop}

@[ext]
lemma sus_eq : ∀ {f g : sus α}, f.is_su = g.is_su → f = g
| ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ rfl := rfl

section
variables [t : sus α]
include t

/-- `is_su s` means that `s` is sus in the ambient `sus` on `α` -/
def is_su (s : set α) : Prop := sus.is_su t s

@[simp]
lemma is_su_univ : is_su (univ : set α) := sus.is_su_univ t

@[simp]
lemma is_su_empty : is_su (∅ : set α) := sus.is_su_empty t

lemma is_su_inter (h₁ : is_su s₁) (h₂ : is_su s₂) : is_su (s₁ ∩ s₂) :=
sus.is_su_inter t s₁ s₂ h₁ h₂

lemma is_su_union (h₁ : is_su s₁) (h₂ : is_su s₂) : is_su (s₁ ∪ s₂) :=
sus.is_su_union t s₁ s₂ h₁ h₂

end

def tsus (X : Type*) [sus X] : Type* := { a : set X // is_su a }

variables {X : Type*} [sus X]
#check tsus
#check (tsus X)


def has_add_su : tsus X → tsus X → tsus X := λ u v, ⟨u.1 ∪ v.1, is_su_union u.2 v.2⟩

lemma add_assoc_su : ∀ a b c : tsus X,
  has_add_su (has_add_su a b) c = has_add_su a (has_add_su b c) :=
by { unfold has_add_su, simp [union_assoc] }

def zero_su : tsus X := ⟨_, is_su_empty⟩

@[simp] lemma add_zero_su : ∀ a : tsus X,
  has_add_su a zero_su = a :=
by { unfold has_add_su, unfold zero_su, simp [union_empty] }

@[simp] lemma zero_add_su : ∀ a : tsus X,
  has_add_su zero_su a = a :=
by { unfold has_add_su, unfold zero_su, simp [union_empty] }

lemma add_comm_su : ∀ a b : tsus X,
  has_add_su a b = has_add_su b a :=
by { unfold has_add_su, simp [union_comm] }

def has_mul_su : tsus X → tsus X → tsus X := λ u v, ⟨u.1 ∩ v.1, is_su_inter u.2 v.2⟩

lemma mul_assoc_su : ∀ a b c : tsus X,
  has_mul_su (has_mul_su a b) c = has_mul_su a (has_mul_su b c) :=
by { unfold has_mul_su, simp [inter_assoc] }

def one_su : tsus X := ⟨_, is_su_univ⟩

@[simp] lemma mul_one_su : ∀ a : tsus X,
  has_mul_su a one_su = a :=
by { unfold has_mul_su, unfold one_su, simp [inter_univ] }

@[simp] lemma one_mul_su : ∀ a : tsus X,
  has_mul_su one_su a = a :=
by { unfold has_mul_su, unfold one_su, simp [inter_univ] }

lemma mul_comm_su : ∀ a b : tsus X,
  has_mul_su a b = has_mul_su b a :=
by { unfold has_mul_su, simp [inter_comm] }

lemma zero_mul_su : ∀ a : tsus X,
  has_mul_su zero_su a = zero_su :=
by { unfold has_mul_su, unfold zero_su, simp [inter_empty] }

lemma mul_zero_su : ∀ a : tsus X,
  has_mul_su a zero_su = zero_su :=
by { unfold has_mul_su, unfold zero_su, simp [inter_empty] }

lemma one_add_su : ∀ a : tsus X,
  has_add_su one_su a = one_su :=
by { unfold has_add_su, unfold one_su, simp }

lemma mul_zero_su : ∀ a : tsus X,
  has_mul_su a zero_su = zero_su :=
by { unfold has_mul_su, unfold zero_su, simp [inter_empty] }

lemma left_distrib_su : ∀ (a b c : tsus X),
  has_mul_su a (has_add_su b c) = has_add_su (has_mul_su a b) (has_mul_su a c) :=
by { unfold has_add_su, unfold has_mul_su, simp [inter_union_distrib_left] }

lemma right_distrib_su : ∀ (a b c : tsus X),
  has_mul_su (has_add_su a b) c = has_add_su (has_mul_su a c) (has_mul_su b c) :=
by { unfold has_add_su, unfold has_mul_su, simp [union_inter_distrib_right] }

instance : has_add (tsus X) := ⟨has_add_su⟩
instance : has_zero (tsus X) := ⟨⟨_, is_su_empty⟩⟩
instance : has_mul (tsus X) := ⟨has_mul_su⟩

def ser_union_add (X : Type*) [sus X] : semiring (tsus X) :=
{ add := has_add_su,
  add_assoc := add_assoc_su,
  zero := ⟨_, is_su_empty⟩,
  zero_add := zero_add_su,
  add_zero := add_zero_su,
  add_comm := add_comm_su,
  mul := has_mul_su,
  mul_assoc := mul_assoc_su,
  one := one_su,
  one_mul := one_mul_su,
  mul_one := mul_one_su,
  zero_mul := zero_mul_su,
  mul_zero := mul_zero_su,
  left_distrib := left_distrib_su,
  right_distrib := right_distrib_su }

def ser_inter_add (X : Type*) [sus X] : semiring (tsus X) :=
{ add := has_mul_su,
  add_assoc := mul_assoc_su,
  zero := ⟨_, is_su_univ⟩,
  zero_add := one_mul_su,
  add_zero := mul_one_su,
  add_comm := mul_comm_su,
  mul := has_add_su,
  mul_assoc := add_assoc_su,
  one := zero_su,
  one_mul := zero_add_su,
  mul_one := add_zero_su,
  zero_mul := --one_add_su,
  mul_zero := --mul_zero_su,
  left_distrib := left_distrib_su,
  right_distrib := right_distrib_su }

def top_to_sus {X : Type*} [topological_space X] : sus X :=
{ is_su := is_open,
  is_su_univ := is_open_univ,
  is_su_empty := is_open_empty,
  is_su_inter := λ _ _, is_open_inter,
  is_su_union := λ _ _, is_open_union }

#exit
begin

  fconstructor,
end


#exit

structure sus (Y : Type*) :=
( su : set Y → Prop )
( bot : su ∅ )
( top : su set.univ )
( is_su_union : ∀u v, su u → su v → su (u ∪ v) )
( is_su_inter : ∀ {u v : set Y}, su u → su v → su (u ∩ v) )

attribute [class] sus

namespace sus
variables {X : Type*} [sus X]
--#print sus



def seu (Y : Type*) [sus Y] : Type* := {u : set Y // su _inst_2 u}

def has_union_su : seu X → seu X → seu X := λ u v, ⟨u.1 ∪ v.1, is_su_union u.2 v.2⟩

def le_su : seu X → seu X → Prop := λ u v, u.1 ⊆ v.1

def lt_su : seu X → seu X → Prop := λ u v, u.1 ⊆ v.1 ∧ ¬ v.1 ⊆ u.1

def le_refl_seu (a : seu X) : le_su a a := by unfold le_su

def le_trans_seu (a b c : seu X) : le_su a b → le_su b c → le_su a c := λ ab bc x y, bc (ab y)

def has_inter_seu : seu X → seu X → seu X := λ u v, ⟨u.1 ∩ v.1, is_su_inter u.2 v.2⟩

#print topological_space


def finset_lattice (X : Type*) [topological_space X]: distrib_lattice {a : set X // is_open a} :=
{ sup := has_union_topo,
  le := le_topo,
  lt := lt_topo,
  le_refl := le_refl_topo,
  le_trans := le_trans_topo,
  lt_iff_le_not_le := _,
  le_antisymm := _,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,
  le_sup_inf := _ }

end sus

#exit

variables {X : Type*} [topological_space X]

#check {a // is_open a}

def opens (X : Type*) [topological_space X] : Type* := {a : set X // is_open a}

#check opens X

def has_union_topo {X : Type*} [topological_space X] : (opens X) → (opens X) → (opens X) :=
λ u v, ⟨u.1 ∪ v.1, is_open_union u.2 v.2⟩

def le_topo {X : Type*} [topological_space X] : (opens X) → (opens X) → Prop :=
λ u v, u.1 ⊆ v.1

def lt_topo {X : Type*} [topological_space X] : (opens X) → (opens X) → Prop :=
λ u v, u.1 ⊆ v.1 ∧ ¬ v.1 ⊆ u.1

def le_refl_topo {X : Type*} [topological_space X] (a : opens X) : le_topo a a :=
by unfold le_topo

def le_trans_topo {X : Type*} [topological_space X] (a b c : opens X) :
  le_topo a b → le_topo b c → le_topo a c :=
λ ab bc x y, bc (ab y)

def has_inter_topo {X : Type*} [topological_space X] : (opens X) → (opens X) → (opens X) :=
λ u v, ⟨u.1 ∩ v.1, is_open_inter u.2 v.2⟩



def finset_lattice (X : Type*) [topological_space X]: distrib_lattice {a : set X // is_open a} :=
{ sup := has_union_topo,
  le := le_topo,
  lt := lt_topo,
  le_refl := le_refl_topo,
  le_trans := le_trans_topo,
  lt_iff_le_not_le := _,
  le_antisymm := _,
  le_sup_left := _,
  le_sup_right := _,
  sup_le := _,
  inf := _,
  inf_le_left := _,
  inf_le_right := _,
  le_inf := _,
  le_sup_inf := _ }

#exit
begin
  intros a,
  simp only [finset.left_eq_union_iff_subset, finset.sup_eq_union],
  use a,refl,
  {
    simp only [finset.sup_eq_union, exists_imp_distrib],
    intros a b c d bad e cbe,
    use d ∪ e,
    simp only [*, finset.union_assoc] },
  simp only [not_exists, auto_param_eq, finset.sup_eq_union, finset.le_iff_subset],
  intros a b,
  split;intro h,
  refine ⟨⟨b, _⟩, _⟩,simp only [finset.right_eq_union_iff_subset, h],
  rintros x rfl,cases h with h1 h2,
  apply h2,
  {simp at *, intros a ha,
    apply set.mem_of_mem_of_subset _ h1,
    simp at *,
    right,assumption, },


  use (λ a b, a ⊓ b),
end

#exit

def finset_lattice (X : Type*) [topological_space X]: distrib_lattice {a : set X // is_open a} :=
begin
  refine ⟨λ a b, a ∪ b, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩,
  intros a b,
  exact ∃ c : finset X, b = a ⊔ c,
  intros a b,
  exact a ≤ b ∧ ¬ a = b,
  intros a,
  simp only [finset.left_eq_union_iff_subset, finset.sup_eq_union],
  use a,refl,
  {
    simp only [finset.sup_eq_union, exists_imp_distrib],
    intros a b c d bad e cbe,
    use d ∪ e,
    simp only [*, finset.union_assoc] },
  simp only [not_exists, auto_param_eq, finset.sup_eq_union, finset.le_iff_subset],
  intros a b,
  split;intro h,
  refine ⟨⟨b, _⟩, _⟩,simp only [finset.right_eq_union_iff_subset, h],
  rintros x rfl,cases h with h1 h2,
  apply h2,
  {simp at *, intros a ha,
    apply set.mem_of_mem_of_subset _ h1,
    simp at *,
    right,assumption, },


  use (λ a b, a ⊓ b),
end

#exit

∪
class semirng (α : Type*) extends add_comm_monoid α, semigroup α, distrib α, mul_zero_class α


--instance : semirng (finset X) :=




#exit

class fs_algebra α extends semiring α :=--, add_comm_monoid α, has_mul α, :=
(mul_assoc : ∀ a b c : α, a * b * c = (a * b) * c)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)
