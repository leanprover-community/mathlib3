import algebra.ring
import algebra.module

universes u' v'

class vector_space (α : inout Type u')  (β : Type v') [field α] extends module α β

instance field.to_vector_space {K : Type} [field K] :
vector_space K K := ⟨ring.to_module⟩

lemma eq_zero_of_add_self_eq {α : Type} [add_group α]
{a : α} (H : a + a = a) : a = 0 :=
add_left_cancel (by {rw add_zero, exact H})

class subspace (K : Type) (V : Type) [field K] [vector_space K V] (p : set V) :=
(zero : (0:V) ∈ p)
(add : ∀ u v, u ∈ p → v ∈ p → u + v ∈ p)
(neg : ∀ v, v ∈ p → -v ∈ p)
(smul : ∀ c v, v ∈ p → c • v ∈ p)

namespace subspace

variables (K : Type) {V : Type} [field K] [vector_space K V]
variables {p : set V} [subspace K V p]
variables {c d : K} (u v : {x // x ∈ p})

include K

instance : has_add {x // x ∈ p} := ⟨(λ u v,
{ val := u.val + v.val,
  property := add K u.val v.val u.property v.property })⟩

instance : has_zero {x // x ∈ p} := ⟨
{ val := 0,
  property := zero K p }⟩

instance : has_neg {x // x ∈ p} := ⟨(λ v,
{ val := -v.val,
  property := neg K v.val v.property })⟩

instance : has_scalar K {x // x ∈ p} := ⟨(λ c v,
{ val := c • v.val,
  property := smul c v.val v.property })⟩

@[simp] lemma add_val : (u + v).val = u.val + v.val := rfl
@[simp] lemma zero_val : (0 : {x // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val : (-v).val = -v.val := rfl
@[simp] lemma smul_val : (c • v).val = c • v.val := rfl

instance : vector_space K {x // x ∈ p} :=
{ add                := has_add.add,
  add_assoc          := (λ u v w, subtype.eq (by simp [add_assoc])),
  zero               := has_zero.zero _,
  zero_add           := (λ v, subtype.eq (by simp [zero_add])),
  add_zero           := (λ v, subtype.eq (by simp [add_zero])),
  neg                := has_neg.neg,
  add_left_neg       := (λ v, subtype.eq (by simp [add_left_neg])),
  add_comm           := (λ u v, subtype.eq (by simp [add_comm])),
  smul               := has_scalar.smul,
  smul_left_distrib  := (λ c u v, subtype.eq (by simp [smul_left_distrib])),
  smul_right_distrib := (λ c u v, subtype.eq (by simp [smul_right_distrib])),
  mul_smul           := (λ c d v, subtype.eq (by simp [mul_smul])),
  one_smul           := (λ v, subtype.eq (by simp [one_smul])) }

end subspace


structure linear_space (K V W : Type) [field K] [vector_space K V] [vector_space K W] :=
(T : V → W)
(map_add : ∀ u v, T (u+v) = T u + T v)
(map_smul : ∀ (c:K) v, T (c • v) = c • (T v))

namespace linear_space

variables {K V W : Type} [field K] [vector_space K V] [vector_space K W]
variables {c d : K}

section basic

variables {u v : V} {A B C : linear_space K V W}

instance : has_coe_to_fun (linear_space K V W) := ⟨_, T⟩

@[simp] lemma map_add_vec : A (u+v) = A u + A v := map_add A u v
@[simp] lemma map_smul_vec : A (c•v) = c • (A v) := map_smul A c v

theorem ext (HAB : ∀ v, A v = B v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] lemma map_zero : A 0 = 0 :=
begin
  have := eq.symm (map_add A 0 0),
  rw [add_zero] at this,
  exact eq_zero_of_add_self_eq this
end

@[simp] lemma map_neg : A (-v) = -(A v) :=
eq_neg_of_add_eq_zero (by {rw [←map_add_vec], simp})

@[simp] lemma map_sub : A (u-v) = A u - A v := by simp

end basic


@[simp] def ker (A : linear_space K V W) : set V := {v | A v = 0}

namespace ker

variables {A : linear_space K V W}
variables {u v : V}

@[simp] lemma vec_ker : v ∈ A.ker ↔ A v = 0 := ⟨id, id⟩

theorem ker_of_map_eq_map (Huv : A u = A v) : u-v ∈ A.ker :=
by {rw [vec_ker,map_sub], exact sub_eq_zero_of_eq Huv}

theorem inj_of_trivial_ker (H: ∀ v, A.ker v → v = 0) (Huv: A u = A v) : u = v :=
eq_of_sub_eq_zero (H _ (ker_of_map_eq_map Huv))

variables (u v)

theorem add_ker (HU : u ∈ A.ker) (HV : v ∈ A.ker) : u + v ∈ A.ker :=
by {rw [vec_ker] at *, simp [HU,HV]}

theorem zero_ker : (0:V) ∈ A.ker := map_zero

theorem neg_ker (HV : v ∈ A.ker) : -v ∈ A.ker :=
by {rw [vec_ker] at *, simp [HV]}

theorem sub_ker (HU : u ∈ A.ker) (HV : v ∈ A.ker) : u - v ∈ A.ker :=
by {rw [vec_ker] at *, simp [HU,HV]}

theorem smul_ker (c : K) (v : V) (HV : v ∈ A.ker) : c • v ∈ A.ker :=
by {rw [vec_ker] at *, simp [HV]}

instance : subspace K V A.ker :=
{ add  := add_ker,
  zero := zero_ker,
  neg  := neg_ker,
  smul := smul_ker }

end ker


@[simp] def im (A : linear_space K V W) : set W := {w | ∃ v, A v = w}

namespace im

variables {A : linear_space K V W}
variables (u v w : W)

@[simp] lemma vec_im : w ∈ A.im ↔ ∃ v, A v = w := ⟨id, id⟩

theorem add_im (HU : u ∈ A.im) (HV : v ∈ A.im) : u + v ∈ A.im :=
begin
  unfold im at *,
  cases HU with x hx,
  cases HV with y hy,
  existsi (x + y),
  simp [hx, hy]
end

theorem zero_im : (0:W) ∈ A.im := ⟨0, map_zero⟩

theorem neg_im (HV : v ∈ A.im) : -v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (-y),
  simp [hy]
end

theorem smul_im (c : K) (v : W) (HV : v ∈ A.im) : c • v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (c • y),
  simp [hy]
end

instance : subspace K W A.im :=
{ add  := add_im,
  zero := zero_im,
  neg  := neg_im,
  smul := smul_im }

end im


section Hom

variables {u v : V} {A B C : linear_space K V W}

def add (A B : linear_space K V W) : (linear_space K V W) :=
{ T        := (λ v, (A v) + (B v)),
  map_add  := (λ u v, by simp),
  map_smul := (λ c v, by simp [smul_left_distrib]) }

def zero : linear_space K V W :=
{ T        := (λ v, 0),
  map_add  := (λ u v, by simp),
  map_smul := (λ c v, by simp) }

def neg (A : linear_space K V W) : linear_space K V W :=
{ T        := (λ v, -A v),
  map_add  := (λ u v, by simp),
  map_smul := (λ c v, by simp) }

instance : has_add (linear_space K V W) := ⟨add⟩
instance : has_zero (linear_space K V W) := ⟨zero⟩
instance : has_neg (linear_space K V W) := ⟨neg⟩

@[simp] lemma add_vec : (A + B) v = A v + B v := rfl
@[simp] lemma zero_vec : (0:linear_space K V W) v = 0 := rfl
@[simp] lemma neg_vec : (-A) v = -(A v) := rfl

def smul (c : K) (A : linear_space K V W) : linear_space K V W :=
{ T        := (λ v, c•(A v)),
  map_add  := (λ u v, by simp [smul_left_distrib]),
  map_smul := (λ k v, by simp [smul_smul]) }

instance : has_scalar K (linear_space K V W) := ⟨smul⟩

@[simp] lemma smul_vec : (c • A) v = c • (A v) := rfl

variables (c d u v A B C)

theorem add_zero : A + 0 = A := ext (λ v, by simp [add_zero])
theorem zero_add : 0 + A = A := ext (λ v, by simp [zero_add])
theorem add_right_neg : A + (-A) = 0 := ext (λ v, by simp [add_right_neg])
theorem add_left_neg : (-A) + A = 0 := ext (λ v, by simp [add_left_neg])
theorem add_assoc : A + B + C = A + (B + C) := ext (λ v, by simp [add_assoc])
theorem add_comm : A + B = B + A := ext (λ v, by simp [add_comm])
theorem smul_left_distrib : c•(A+B) = c•A + c•B := ext (λ v, by simp [smul_left_distrib])
theorem smul_right_distrib : (c+d)•A = c•A + d•A := ext (λ v, by simp [smul_right_distrib])
theorem mul_smul : (c*d)•A = c•(d•A) := ext (λ v, by simp [mul_smul])
theorem one_smul : (1:K) • A = A := ext (λ v, by simp [one_smul])

instance : vector_space K (linear_space K V W) :=
{ add                 := add,
  add_assoc           := add_assoc,
  zero                := zero,
  zero_add            := zero_add,
  add_zero            := add_zero,
  neg                 := neg,
  add_left_neg        := add_left_neg,
  add_comm            := add_comm,
  smul                := smul,
  smul_left_distrib   := smul_left_distrib,
  smul_right_distrib  := smul_right_distrib,
  mul_smul            := mul_smul,
  one_smul            := one_smul }

end Hom

variable (V)
def vector_space.dual := linear_space K V K
variable {V}

section matrix_ring

variables {v : V} {A B C : linear_space K V V}

def id : linear_space K V V :=
{ T        := id,
  map_add  := (λ u v, rfl),
  map_smul := (λ u v, rfl) }

def comp (A B : linear_space K V V) : linear_space K V V :=
{ T        := A ∘ B,
  map_add  := (λ u v, by simp [function.comp]),
  map_smul := (λ c v, by simp [function.comp]) }

instance : has_mul (linear_space K V V) := ⟨comp⟩

@[simp] lemma id_vec : (id : linear_space K V V) v = v := rfl
@[simp] lemma comp_vec : (A * B) v = A (B v) := rfl

variables (v A B C)

@[simp] lemma comp_id : A * id = A := ext (λ v, rfl)
@[simp] lemma id_comp : id * A = A := ext (λ v, rfl)
theorem comp_assoc : (A * B) * C = A * (B * C) := ext (λ v, rfl)
theorem comp_add : A * (B + C) = A * B + A * C := ext (λ v, by simp)
theorem add_comp : (A + B) * C = A * C + B * C := ext (λ v, rfl)

instance : ring (linear_space K V V) :=
{ add             := add,
  add_assoc       := add_assoc,
  zero            := zero,
  zero_add        := zero_add,
  add_zero        := add_zero,
  neg             := neg,
  add_left_neg    := add_left_neg,
  add_comm        := add_comm,
  mul             := comp,
  mul_assoc       := comp_assoc,
  one             := id,
  one_mul         := id_comp,
  mul_one         := comp_id,
  left_distrib    := comp_add,
  right_distrib   := add_comp }

end matrix_ring

variables (K V)

def general_linear_group := invertible (linear_space K V V)

end linear_space
