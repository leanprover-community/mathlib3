/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import data.fin.tuple
import data.list.range
import group_theory.group_action.pi
import algebra.ring.pi

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : fin 4 → α`.
Nesting vectors gives a matrix, so `![![a, b], ![c, d]] : fin 2 → fin 2 → α`.
Later we will define `matrix m n α` to be `m → n → α`, so the type of `![![a, b], ![c, d]]`
can be written as `matrix (fin 2) (fin 2) α`.

## Main definitions

* `vec_empty` is the empty vector (or `0` by `n` matrix) `![]`
* `vec_cons` prepends an entry to a vector, so `![a, b]` is `vec_cons a (vec_cons b vec_empty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vec_cons a (vec_cons b vec_empty)`.

## Examples

Examples of usage can be found in the `test/matrix.lean` file.
-/

namespace matrix

universe u
variables {α : Type u}

section matrix_notation

/-- `![]` is the vector with no entries. -/
def vec_empty : fin 0 → α :=
fin_zero_elim

/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vec_cons {n : ℕ} (h : α) (t : fin n → α) : fin n.succ → α :=
fin.cons h t

notation `![` l:(foldr `, ` (h t, vec_cons h t) vec_empty `]`) := l

/-- `vec_head v` gives the first entry of the vector `v` -/
def vec_head {n : ℕ} (v : fin n.succ → α) : α :=
v 0

/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vec_tail {n : ℕ} (v : fin n.succ → α) : fin n → α :=
v ∘ fin.succ

variables {m n : ℕ}

/-- Use `![...]` notation for displaying a vector `fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
instance pi_fin.has_repr [has_repr α] : has_repr (fin n → α) :=
{ repr := λ f, "![" ++ (string.intercalate ", " ((list.fin_range n).map (λ n, repr (f n)))) ++ "]" }

end matrix_notation

variables {m n o : ℕ} {m' n' o' : Type*}

lemma empty_eq (v : fin 0 → α) : v = ![] := subsingleton.elim _ _

section val

@[simp] lemma head_fin_const (a : α) : vec_head (λ (i : fin (n + 1)), a) = a := rfl

@[simp] lemma cons_val_zero (x : α) (u : fin m → α) : vec_cons x u 0 = x := rfl

lemma cons_val_zero' (h : 0 < m.succ) (x : α) (u : fin m → α) :
  vec_cons x u ⟨0, h⟩ = x :=
rfl

@[simp] lemma cons_val_succ (x : α) (u : fin m → α) (i : fin m) :
  vec_cons x u i.succ = u i :=
by simp [vec_cons]

@[simp] lemma cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : fin m → α) :
  vec_cons x u ⟨i.succ, h⟩ = u ⟨i, nat.lt_of_succ_lt_succ h⟩ :=
by simp only [vec_cons, fin.cons, fin.cases_succ']

@[simp] lemma head_cons (x : α) (u : fin m → α) :
  vec_head (vec_cons x u) = x :=
rfl

@[simp] lemma tail_cons (x : α) (u : fin m → α) :
  vec_tail (vec_cons x u) = u :=
by { ext, simp [vec_tail] }

@[simp] lemma empty_val' {n' : Type*} (j : n') :
  (λ i, (![] : fin 0 → n' → α) i j) = ![] :=
empty_eq _

@[simp] lemma cons_head_tail (u : fin m.succ → α) :
 vec_cons (vec_head u) (vec_tail u) = u :=
fin.cons_self_tail _

@[simp] lemma range_cons (x : α) (u : fin n → α) :
  set.range (vec_cons x u) = {x} ∪ set.range u :=
set.ext $ λ y, by simp [fin.exists_fin_succ, eq_comm]

@[simp] lemma range_empty (u : fin 0 → α) : set.range u = ∅ :=
set.range_eq_empty _

@[simp] lemma vec_cons_const (a : α) : vec_cons a (λ k : fin n, a) = λ _, a :=
funext $ fin.forall_fin_succ.2 ⟨rfl, cons_val_succ _ _⟩

lemma vec_single_eq_const (a : α) : ![a] = λ _, a :=
funext $ unique.forall_iff.2 rfl

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp] lemma cons_val_one (x : α) (u : fin m.succ → α) :
  vec_cons x u 1 = vec_head u :=
by { rw [← fin.succ_zero_eq_one, cons_val_succ], refl }

@[simp] lemma cons_val_fin_one (x : α) (u : fin 0 → α) (i : fin 1) :
  vec_cons x u i = x :=
by { refine fin.forall_fin_one.2 _ i, refl }

lemma cons_fin_one (x : α) (u : fin 0 → α) : vec_cons x u = (λ _, x) :=
funext (cons_val_fin_one x u)

/-! ### Numeral (`bit0` and `bit1`) indices
The following definitions and `simp` lemmas are to allow any
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `fin n`).
-/

@[simp] lemma empty_append (v : fin n → α) : fin.append (zero_add _).symm ![] v = v :=
by { ext, simp [fin.append] }

@[simp] lemma cons_append (ho : o + 1 = m + 1 + n) (x : α) (u : fin m → α) (v : fin n → α) :
  fin.append ho (vec_cons x u) v =
    vec_cons x (fin.append (by rwa [add_assoc, add_comm 1, ←add_assoc,
                                  add_right_cancel_iff] at ho) u v) :=
begin
  ext i,
  simp_rw [fin.append],
  split_ifs with h,
  { rcases i with ⟨⟨⟩ | i, hi⟩,
    { simp },
    { simp only [nat.succ_eq_add_one, add_lt_add_iff_right, fin.coe_mk] at h,
      simp [h] } },
  { rcases i with ⟨⟨⟩ | i, hi⟩,
    { simpa using h },
    { rw [not_lt, fin.coe_mk, nat.succ_eq_add_one, add_le_add_iff_right] at h,
      simp [h] } }
end

/-- `vec_alt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
def vec_alt0 (hm : m = n + n) (v : fin m → α) (k : fin n) : α :=
v ⟨(k : ℕ) + k, hm.symm ▸ add_lt_add k.property k.property⟩

/-- `vec_alt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
def vec_alt1 (hm : m = n + n) (v : fin m → α) (k : fin n) : α :=
v ⟨(k : ℕ) + k + 1, hm.symm ▸ nat.add_succ_lt_add k.property k.property⟩

lemma vec_alt0_append (v : fin n → α) : vec_alt0 rfl (fin.append rfl v v) = v ∘ bit0 :=
begin
  ext i,
  simp_rw [function.comp, bit0, vec_alt0, fin.append],
  split_ifs with h; congr,
  { rw fin.coe_mk at h,
    simp only [fin.ext_iff, fin.coe_add, fin.coe_mk],
    exact (nat.mod_eq_of_lt h).symm },
  { rw [fin.coe_mk, not_lt] at h,
    simp only [fin.ext_iff, fin.coe_add, fin.coe_mk, nat.mod_eq_sub_mod h],
    refine (nat.mod_eq_of_lt _).symm,
    rw tsub_lt_iff_left h,
    exact add_lt_add i.property i.property }
end

lemma vec_alt1_append (v : fin (n + 1) → α) : vec_alt1 rfl (fin.append rfl v v) = v ∘ bit1 :=
begin
  ext i,
  simp_rw [function.comp, vec_alt1, fin.append],
  cases n,
  { simp, congr },
  { split_ifs with h; simp_rw [bit1, bit0]; congr,
    { simp only [fin.ext_iff, fin.coe_add, fin.coe_mk],
      rw fin.coe_mk at h,
      rw fin.coe_one,
      rw nat.mod_eq_of_lt (nat.lt_of_succ_lt h),
      rw nat.mod_eq_of_lt h },
    { rw [fin.coe_mk, not_lt] at h,
      simp only [fin.ext_iff, fin.coe_add, fin.coe_mk, nat.mod_add_mod, fin.coe_one,
                 nat.mod_eq_sub_mod h],
      refine (nat.mod_eq_of_lt _).symm,
      rw tsub_lt_iff_left h,
      exact nat.add_succ_lt_add i.property i.property } }
end

@[simp] lemma vec_head_vec_alt0 (hm : (m + 2) = (n + 1) + (n + 1)) (v : fin (m + 2) → α) :
  vec_head (vec_alt0 hm v) = v 0 := rfl

@[simp] lemma vec_head_vec_alt1 (hm : (m + 2) = (n + 1) + (n + 1)) (v : fin (m + 2) → α) :
  vec_head (vec_alt1 hm v) = v 1 :=
by simp [vec_head, vec_alt1]

@[simp] lemma cons_vec_bit0_eq_alt0 (x : α) (u : fin n → α) (i : fin (n + 1)) :
  vec_cons x u (bit0 i) = vec_alt0 rfl (fin.append rfl (vec_cons x u) (vec_cons x u)) i :=
by rw vec_alt0_append

@[simp] lemma cons_vec_bit1_eq_alt1 (x : α) (u : fin n → α) (i : fin (n + 1)) :
  vec_cons x u (bit1 i) = vec_alt1 rfl (fin.append rfl (vec_cons x u) (vec_cons x u)) i :=
by rw vec_alt1_append

@[simp] lemma cons_vec_alt0 (h : m + 1 + 1 = (n + 1) + (n + 1)) (x y : α) (u : fin m → α) :
  vec_alt0 h (vec_cons x (vec_cons y u)) = vec_cons x (vec_alt0
    (by rwa [add_assoc n, add_comm 1, ←add_assoc, ←add_assoc, add_right_cancel_iff,
             add_right_cancel_iff] at h) u) :=
begin
  ext i,
  simp_rw [vec_alt0],
  rcases i with ⟨⟨⟩ | i, hi⟩,
  { refl },
  { simp [vec_alt0, nat.add_succ, nat.succ_add] }
end

-- Although proved by simp, extracting element 8 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp] lemma empty_vec_alt0 (α) {h} : vec_alt0 h (![] : fin 0 → α) = ![] :=
by simp

@[simp] lemma cons_vec_alt1 (h : m + 1 + 1 = (n + 1) + (n + 1)) (x y : α) (u : fin m → α) :
  vec_alt1 h (vec_cons x (vec_cons y u)) = vec_cons y (vec_alt1
    (by rwa [add_assoc n, add_comm 1, ←add_assoc, ←add_assoc, add_right_cancel_iff,
             add_right_cancel_iff] at h) u) :=
begin
  ext i,
  simp_rw [vec_alt1],
  rcases i with ⟨⟨⟩ | i, hi⟩,
  { refl },
  { simp [vec_alt1, nat.add_succ, nat.succ_add] }
end

-- Although proved by simp, extracting element 9 of a five-element
-- vector does not work by simp unless this lemma is present.
@[simp] lemma empty_vec_alt1 (α) {h} : vec_alt1 h (![] : fin 0 → α) = ![] :=
by simp

end val

section smul

variables {M : Type*} [has_scalar M α]

@[simp] lemma smul_empty (x : M) (v : fin 0 → α) : x • v = ![] := empty_eq _

@[simp] lemma smul_cons (x : M) (y : α) (v : fin n → α) :
  x • vec_cons y v = vec_cons (x • y) (x • v) :=
by { ext i, refine fin.cases _ _ i; simp }

end smul

section add

variables [has_add α]

@[simp] lemma empty_add_empty (v w : fin 0 → α) : v + w = ![] := empty_eq _

@[simp] lemma cons_add (x : α) (v : fin n → α) (w : fin n.succ → α) :
  vec_cons x v + w = vec_cons (x + vec_head w) (v + vec_tail w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma add_cons (v : fin n.succ → α) (y : α) (w : fin n → α) :
  v + vec_cons y w = vec_cons (vec_head v + y) (vec_tail v + w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma cons_add_cons (x : α) (v : fin n → α) (y : α) (w : fin n → α) :
  vec_cons x v + vec_cons y w = vec_cons (x + y) (v + w) :=
by simp

@[simp] lemma head_add (a b : fin n.succ → α) : vec_head (a + b) = vec_head a + vec_head b := rfl

@[simp] lemma tail_add (a b : fin n.succ → α) : vec_tail (a + b) = vec_tail a + vec_tail b := rfl

end add

section sub

variables [has_sub α]

@[simp] lemma empty_sub_empty (v w : fin 0 → α) : v - w = ![] := empty_eq _

@[simp] lemma cons_sub (x : α) (v : fin n → α) (w : fin n.succ → α) :
  vec_cons x v - w = vec_cons (x - vec_head w) (v - vec_tail w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma sub_cons (v : fin n.succ → α) (y : α) (w : fin n → α) :
  v - vec_cons y w = vec_cons (vec_head v - y) (vec_tail v - w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma cons_sub_cons (x : α) (v : fin n → α) (y : α) (w : fin n → α) :
  vec_cons x v - vec_cons y w = vec_cons (x - y) (v - w) :=
by simp

@[simp] lemma head_sub (a b : fin n.succ → α) : vec_head (a - b) = vec_head a - vec_head b := rfl

@[simp] lemma tail_sub (a b : fin n.succ → α) : vec_tail (a - b) = vec_tail a - vec_tail b := rfl

end sub

section one

variables [has_one α]

@[simp, to_additive] lemma one_empty : (1 : fin 0 → α) = ![] :=
empty_eq _

@[simp, to_additive] lemma cons_one_one : vec_cons (1 : α) (1 : fin n → α) = 1 :=
by { ext i j, refine fin.cases _ _ i, { refl }, simp }

@[simp, to_additive] lemma head_one : vec_head (1 : fin n.succ → α) = 1 := rfl

@[simp, to_additive] lemma tail_one : vec_tail (1 : fin n.succ → α) = 1 := rfl

@[simp, to_additive] lemma cons_eq_one_iff {v : fin n → α} {x : α} :
  vec_cons x v = 1 ↔ x = 1 ∧ v = 1 :=
⟨ λ h, ⟨ congr_fun h 0, by { convert congr_arg vec_tail h, simp } ⟩,
  λ ⟨hx, hv⟩, by simp [hx, hv] ⟩

open_locale classical

lemma cons_ne_one_iff {v : fin n → α} {x : α} :
  vec_cons x v ≠ 1 ↔ (x ≠ 1 ∨ v ≠ 1) :=
⟨ λ h, not_and_distrib.mp (h ∘ cons_eq_one_iff.mpr),
  λ h, mt cons_eq_one_iff.mp (not_and_distrib.mpr h) ⟩

end one

section neg

variables [has_neg α]

@[simp] lemma neg_empty (v : fin 0 → α) : -v = ![] := empty_eq _

@[simp] lemma neg_cons (x : α) (v : fin n → α) :
  -(vec_cons x v) = vec_cons (-x) (-v) :=
by { ext i, refine fin.cases _ _ i; simp }

@[simp] lemma head_neg (a : fin n.succ → α) : vec_head (-a) = -vec_head a := rfl

@[simp] lemma tail_neg (a : fin n.succ → α) : vec_tail (-a) = -vec_tail a := rfl

end neg

section map

variables {β γ : Type*}

/-- `matrix.vec_map f v` is like composition, but `vec_map f ![a, b, c] = ![f a, f b, f c]` by
definition. -/
def vec_map (f : α → β) : ∀ {n}, (fin n → α) → (fin n → β)
| 0 v := ![]
| (n + 1) v := matrix.vec_cons (f (matrix.vec_head v)) (vec_map $ matrix.vec_tail v)

example (f : α → β) (a b c : α) : vec_map f ![a, b, c] = ![f a, f b, f c] := rfl

@[simp] lemma vec_map_nil (f : α → β) : vec_map f ![] = ![] := rfl
@[simp] lemma vec_map_cons (f : α → β) (a : α) (v : fin n → α) :
  vec_map f (vec_cons a v) = vec_cons (f a) (vec_map f v) :=
by rw [vec_map, tail_cons, head_cons]

lemma vec_map_eq_comp (f : α → β) : ∀ {n} (v : fin n → α), vec_map f v = f ∘ v
| 0 v := subsingleton.elim _ _
| (n + 1) v := (congr_arg2 _ rfl $ vec_map_eq_comp _).trans $ cons_head_tail (f ∘ v)

@[simp] lemma vec_map_apply (f : α → β) {n} (v : fin n → α) (i : fin n) : vec_map f v i = f (v i) :=
congr_fun (vec_map_eq_comp _ _) _

@[simp, to_additive] lemma vec_map_one [has_one α] [has_one β] (f : α → β) (hf : f 1 = 1) {n}:
  vec_map f (1 : fin n → α) = 1 :=
(vec_map_eq_comp _ _).trans $ funext $ λ _, hf

@[simp, to_additive] lemma vec_map_mul [has_mul α] [has_mul β] (f : α → β)
  (hf : ∀ x y, f (x * y) = f x * f y) {n} (u v : fin n → α) :
  vec_map f (u * v) = vec_map f u * vec_map f v :=
begin
  rw [vec_map_eq_comp, vec_map_eq_comp, vec_map_eq_comp],
  ext x,
  exact hf _ _,
end

lemma vec_map_smul {R S} [has_scalar R α] [has_scalar S β] (f : α → β)
  (r : R) (s : S) (hf : ∀ x, f (r • x) = s • f x) {n} (u : fin n → α) :
  vec_map f (r • u) = s • vec_map f u :=
begin
  rw [vec_map_eq_comp, vec_map_eq_comp],
  ext x,
  exact hf (u x),
end


/-- `matrix.vec_map₂ f v` is like composition, but `vec_map f ![a, b, c] = ![f a, f b, f c]` by
definition. -/
def vec_map₂ (f : α → β → γ) : ∀ {n}, (fin n → α) → (fin n → β) → (fin n → γ)
| 0 u v := ![]
| (n + 1) u v := matrix.vec_cons (f (matrix.vec_head u) (matrix.vec_head v))
                                 (vec_map₂ (matrix.vec_tail u) (matrix.vec_tail v))

example (f : α → β → γ) (a b : α) (c d : β) : vec_map₂ f ![a, b] ![c, d] = ![f a c, f b d] := rfl

@[simp] lemma vec_map₂_nil (f : α → β → γ) : vec_map₂ f ![] ![] = ![] := rfl
@[simp] lemma vec_map₂_cons (f : α → β → γ) (a : α) (u : fin n → α) (b : β) (v : fin n → β)  :
  vec_map₂ f (vec_cons a u) (vec_cons b v) = vec_cons (f a b) (vec_map₂ f u v) :=
by rw [vec_map₂, tail_cons, head_cons, tail_cons, head_cons]

lemma vec_map₂_eq (f : α → β → γ) :
  ∀ {n} (u : fin n → α) (v : fin n → β), vec_map₂ f u v = λ x, f (u x) (v x)
| 0 u v := subsingleton.elim _ _
| (n + 1) u v := (congr_arg2 _ rfl $ vec_map₂_eq _ _).trans $ cons_head_tail (λ x, f (u x) (v x))

@[simp, to_additive] lemma vec_map_one [has_one α] [has_one β] (f : α → β) (hf : f 1 = 1) {n}:
  vec_map f (1 : fin n → α) = 1 :=
(vec_map_eq_comp _ _).trans $ funext $ λ _, hf

@[simp, to_additive] lemma vec_map_mul [has_mul α] [has_mul β] (f : α → β)
  (hf : ∀ x y, f (x * y) = f x * f y) {n} (u v : fin n → α) :
  vec_map f (u * v) = vec_map f u * vec_map f v :=
begin
  rw [vec_map_eq_comp, vec_map_eq_comp, vec_map_eq_comp],
  ext x,
  exact hf _ _,
end

lemma vec_map_smul {R S} [has_scalar R α] [has_scalar S β] (f : α → β)
  (r : R) (s : S) (hf : ∀ x, f (r • x) = s • f x) {n} (u : fin n → α) :
  vec_map f (r • u) = s • vec_map f u :=
begin
  rw [vec_map_eq_comp, vec_map_eq_comp],
  ext x,
  exact hf (u x),
end

/-- `matrix.map_vec` preserves `monoid_hom` structures. -/
@[to_additive /-" `matrix.map_vec` preserves `add_monoid_hom` structures. "-/,
  simps {fully_applied := ff}]
def _root_.monoid_hom.map_vec [mul_one_class α] [mul_one_class β] (f : α →* β) {n} :
  (fin n → α) →* (fin n → β) :=
{ to_fun := vec_map f,
  map_one' := vec_map_one f f.map_one,
  map_mul' := vec_map_mul f f.map_mul }

/-- `matrix.map_vec` preserves `ring_hom` structures. -/
@[simps {fully_applied := ff}]
def _root_.ring_hom.map_vec [non_assoc_semiring α] [non_assoc_semiring β] (f : α →+* β) {n} :
  (fin n → α) →+* (fin n → β) :=
{ to_fun := vec_map f,
  ..f.to_monoid_hom.map_vec,
  ..f.to_add_monoid_hom.map_vec }

variables [add_comm_monoid α] [add_comm_monoid β]

example [add_comm_monoid α] [add_comm_monoid β] (f1 : α →+ β) (f2 : α →+ β) :
  α →+ (fin 2 → β) :=
begin
  let : fin 2 → (α →+ β) := ![f1, f2],
  let f := λ x : α, vec_map (add_monoid_hom.eval x) this,
  have := (add_monoid_hom.eval).flip.map_vec this,
end


end

end map

end matrix
