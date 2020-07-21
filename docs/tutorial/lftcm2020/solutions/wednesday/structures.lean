import data.rat.basic
import data.nat.parity
import tactic.basic

open nat

noncomputable theory -- definitions are allowed to not compute in this file
open_locale classical -- use classical logic in this file

/-!
## Structures and Classes

In this session we will discuss structures together,
and then you can solve the exercises yourself.

Before we start, run the following in a terminal:
```
  cd /path/to/lftcm2020/
  git pull
  leanproject get-mathlib-cache
```
If `git pull` didn't work because you edited one of the files in the repository,
first copy the files to a backup version and then run `git checkout -- .`
(this will remove all changes to files you edited, so be careful!)


### Declaring a Structure

Structures are a way to bundle information together.

For example, the first example below makes a new structure
  `even_natural_number`, which consists of pairs, where the first
  component is a natural number, and the second component is a
  proof that the natural number is even. These are called the *fields* of the structure.
-/
structure even_natural_number : Type :=
  (n : ℕ)
  (even_n : even n)

/-! We can also group propositions together, for example this is a proposition
  stating that `n` is an even cube greater than 100.
  Note that this is a property of a natural number, while the previous structure
  was a natural number with a property "bundled" together. -/
structure is_even_cube_above_100 (n : ℕ) : Prop :=
  (even : even n)
  (is_cube : ∃ k, n = k^3)
  (gt_100 : n > 100)

/-! Here we give the upper bounds for a function `f`. We can omit the type of the structure. -/
structure bounds (f : ℕ → ℕ) :=
  (bound : ℕ)
  (le_bound : ∀ (n : ℕ), f n ≤ bound)

/-! You can use `#print` to print the type and all fields of a structure. -/
#print even_natural_number
#print is_even_cube_above_100
#print bounds

/-!
  ### Exercise 1
  * Define a structure of eventually constant sequences `ℕ → ℕ`. The first field will be
    `seq : ℕ → ℕ`, and the second field will be the statement that `seq` is eventually constant.
  * Define a structure of a type with 2 points that are unequal.
    (hint: omit the type of the structure, Lean might complain if you give it explicitly)

  Lean will not tell you if you got the right definition, but it will complain if you make a syntax
  error. If you are unsure, ask a mentor to check whether your solution is correct.
-/

-- omit
/- There are different ways to do these, here is one way. -/
structure eventually_constant_sequence : Type :=
(seq : ℕ → ℕ)
(eventually_constant : ∃ k v, ∀ n ≥ k, seq n = v)

structure bipointed_type :=
(A : Type)
(x y : A)
(x_ne_y : x ≠ y)
-- omit

/-! ### Projections of a structure -/

/-! The field names are declared in the namespace of the structure.
  This means that their names have the form `<structure_name>.<field_name>`. -/
example (n : ℕ) (hn : is_even_cube_above_100 n) : n > 100 :=
is_even_cube_above_100.gt_100 hn

/-! You can also `open` the namespace, to use the abbreviated form.
  We put this `open` command inside a section, so that the namespace
  is closed at the end of the `section`. -/
section
open is_even_cube_above_100
example (n : ℕ) (hn : is_even_cube_above_100 n) : n > 100 :=
gt_100 hn
end

/-! Another useful technique is to use *projection notation*. Instead of writing
`is_even_cube_above_100.even hn` we can write `hn.even`.

  Lean will look at the type of `hn` and see that it is `is_even_cube_above_100 n`.
  Then it looks for the lemma with the name `is_even_cube_above_100.even` and apply it to `hn`. -/
example (n : ℕ) (hn : is_even_cube_above_100 n) : even n :=
hn.even

example (n : ℕ) (hn : is_even_cube_above_100 n) : even n ∧ ∃ k, n = k^3 :=
⟨ hn.even, hn.is_cube ⟩

/-! You can also use `.1`, `.2`, `.3`, ... for the fields of a structure. -/
example (n : ℕ) (hn : is_even_cube_above_100 n) : even n ∧ n > 100 ∧ (∃ k, n = k^3) :=
⟨ hn.1, hn.3, hn.2 ⟩

/-! We could have alternatively stated `is_even_cube_above_100`
  as a conjunction of three statements, as below.
  That gives the same proposition, but doesn't give a name to the three components. -/
def is_even_cube_above_100' (n : ℕ) : Prop :=
even n ∧ (∃ k, n = k^3) ∧ n > 100

/-! If we have a structure that mixes data (elements of types, like `ℕ`, `ℝ`, and so on) and
  properties of the data, we can alternatively declare them using *subtypes*.
  This consists of pairs of a natural number and a proof that the natural number is even. -/
def even_natural_number' : Type :=
{ n : ℕ // even n }

/-! The notation for subtypes is almost the same as the notation for set comprehension.
 Note that `//` is used for subtypes, and `|` is used for sets. -/
def set_of_even_natural_numbers : set ℕ :=
{ n : ℕ | even n }

/-! We can construct objects of a structure using the *anonymous constructor* `⟨...⟩`.
  This can construct an object of any structure, including conjunctions,
  existential statements and subtypes. -/
example : even_natural_number → even_natural_number' :=
λ n, ⟨n.1, n.2⟩

example (n : ℕ) : is_even_cube_above_100 n → is_even_cube_above_100' n :=
λ hn, ⟨hn.even, hn.is_cube, hn.gt_100⟩

/-! An alternative way is to use the *structure notation*. The syntax for this is
  ```
    { structure_name . field1_name := value, field2_name := value, ... }
  ```
  You can prove the fields in any order you want.
-/
example : even_natural_number' → even_natural_number :=
λ n,
{ even_natural_number .
  n      := n.1,
  even_n := n.2 }

/-! The structure name is optional if the structure in question is clear from context. -/
example (n : ℕ) : is_even_cube_above_100' n → is_even_cube_above_100 n :=
λ ⟨h1n, h2n, h3n⟩,
{ even    := h1n,
  is_cube := h2n,
  gt_100  := h3n }

/-!
  ### Exercise 2
  * Define `bounds` (given above) again, but now using a the subtype notation `{ _ : _ // _ }`.
  * Define functions back and forth from the structure `bounds` given above and `bounds` given here.
    Try different variations using the anonymous constructor and the projection notation.
-/
#print bounds

def bounds' (f : ℕ → ℕ) : Type :=
/- inline sorry -/ { n : ℕ // ∀ (m : ℕ), f m ≤ n } /- inline sorry -/

example (f : ℕ → ℕ) : bounds f → bounds' f :=
/- inline sorry -/ λ ⟨n, hn⟩, ⟨n, hn⟩ /- inline sorry -/

/- In the example below, replace the `sorry` by an underscore `_`.
  A small yellow lightbulb will appear. Click it, and then select
  `Generate skeleton for the structure under construction`.
  This will automatically give an outline of the structure for you. -/
example (f : ℕ → ℕ) : bounds' f → bounds f :=
λ n, /- inline sorry -/ { bound := n.1, le_bound := n.2 } /- inline sorry -/


/-! Before you continue, watch the second pre-recorded video. -/

/-! ### Classes

Classes are special kind of types or propositions that Lean will automatically find inhabitants for.

You can declare a class by giving it the `@[class]` attribute.

As an example, in this section, we will implement square root on natural numbers, that can only be
applied to natural numbers that are squares. -/
@[class] def is_square (n : ℕ) : Prop := ∃k : ℕ, k^2 = n

namespace is_square

/-! Hypotheses with a class as type should be written in square brackets `[...]`.
This tells Lean that they are implicit, and Lean will try to fill them in automatically.

We define the square root as the (unique) number `k` such that `k^2 = n`. Such `k` exists by the
`is_square n` hypothesis. -/
def sqrt (n : ℕ) [hn : is_square n] : ℕ := classical.some hn

prefix `√`:(max+1) := sqrt -- notation for `sqrt`

/-! The following is the defining property of `√n`. Note that when we write `√n`,
Lean will automatically insert the implicit argument `hn` it found it the context.
This is called *type-class inference*.
We mark this lemma with the `@[simp]` attribute to tell `simp` to simplify using this lemma. -/
@[simp] lemma square_sqrt (n : ℕ) [hn : is_square n] : (√n) ^ 2 = n :=
classical.some_spec hn

/-! ### Exercise:
  Fill in all `sorry`s in the remainder of this section.
-/

/-! Prove this lemma. Again we mark it `@[simp]` so that `simp` can simplify
  equalities involving `√`. Also, hypotheses in square brackets do not need a name.

  Hint: use `pow_left_inj` -/
@[simp] lemma sqrt_eq_iff (n k : ℕ) [is_square n] : √n = k ↔ n = k^2 :=
begin
  -- sorry
  split; intro h,
  { simp [← h] },
  { exact pow_left_inj (nat.zero_le _) (nat.zero_le k) two_pos (by simp [h]) }
  -- sorry
end

/-! To help type-class inference, we have to tell it that some numbers are always squares.
  Here we show that `n^2` is always a square. We mark it as `instance`, which is like
  `lemma` or `def`, except that it is automatically used by type-class inference. -/
instance square_square (n : ℕ) : is_square (n^2) :=
⟨n, rfl⟩

lemma sqrt_square (n : ℕ) : √(n ^ 2) = n :=
by simp

/-! Instances can depend on other instances: here we show that if `n` and `m` are squares, then
`n * m` is one, too.

When writing `√n`, Lean will use a simple search algorithm to find a proof that `n` is a square, by
repeatedly applying previously declared instances, and arguments in the local context. -/
instance square_mul (n m : ℕ) [is_square n] [is_square m] : is_square (n*m) :=
⟨√n * √m, by simp [nat.mul_pow]⟩

/-! Hint: use `nat.mul_pow` -/
#check nat.mul_pow
lemma sqrt_mul (n m : ℕ) [is_square n] [is_square m] : √(n * m) = √n * √m :=
begin
  -- sorry
  simp [nat.mul_pow]
  -- sorry
end

/-! Note that Lean automatically inserts the proof that `n * m ^ 2` is a square,
  using the previously declared instances. -/
example (n m : ℕ) [is_square n] : √(n * m ^ 2) = √n * m :=
begin
  -- sorry
  simp [sqrt_mul, sqrt_square],
  -- sorry
end


/-! Hint: use `nat.le_mul_self` and `nat.pow_two` -/
#check nat.le_mul_self
#check nat.pow_two
lemma sqrt_le (n : ℕ) [is_square n] : √n ≤ n :=
begin
  -- sorry
  conv_rhs { rw [← square_sqrt n, nat.pow_two] }, apply nat.le_mul_self
  -- sorry
end

end is_square

/- At this point, feel free do the remaining exercises in any order. -/


/-! ### Exercise: Bijections and equivalences -/

section bijections

open function

variables {α β : Type*}

/-
An important structure is the type of equivalences, which gives an equivalence (bijection)
between two types:
```
structure equiv (α β : Type*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)
```
In this section we show that this is the same as the bijections from `α` to `β`.
-/
#print equiv

structure bijection (α β : Type*) :=
  (to_fun : α → β)
  (injective : injective to_fun)
  (surjective : surjective to_fun)

/- We declare a *coercion*. This allows us to treat `f` as a function if `f : bijection α β`. -/
instance : has_coe_to_fun (bijection α β) :=
⟨_, λ f, f.to_fun⟩

/-! To show that two bijections are equal, it is sufficient that the underlying functions are
  equal on all inputs. We mark it as `@[ext]` so that we can later use the tactic `ext` to show that
  two bijections are equal. -/
@[ext] def bijection.ext {f g : bijection α β} (hfg : ∀ x, f x = g x) : f = g :=
by { cases f, cases g, congr, ext, exact hfg x }

/-! This lemma allows `simp` to reduce the application of a bijection to an argument. -/
@[simp] lemma coe_mk {f : α → β} {h1f : injective f} {h2f : surjective f} {x : α} :
  { bijection . to_fun := f, injective := h1f, surjective := h2f } x = f x := rfl

/- There is a lemma in the library that almost states this.
  You can use the tactic `suggest` to get suggested lemmas from Lean
  (the one you want has `bijective` in the name). -/
def equiv_of_bijection (f : bijection α β) : α ≃ β :=
begin
  -- sorry
  exact equiv.of_bijective f ⟨f.injective, f.surjective⟩
  -- sorry
end

def bijection_of_equiv (f : α ≃ β) : bijection α β :=
-- sorry
{ to_fun := f,
  injective := f.injective,
  surjective := f.surjective }
-- sorry

/-! Show that bijections are the same (i.e. equivalent) to equivalences. -/
def bijection_equiv_equiv : bijection α β ≃ (α ≃ β) :=
-- sorry
{ to_fun := equiv_of_bijection,
  inv_fun := bijection_of_equiv,
  left_inv := by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] },
  right_inv := by { intro f, ext, simp [bijection_of_equiv, equiv_of_bijection] } }
-- sorry

end bijections



/-! ### Exercise: Bundled groups -/

/-! Below is a possible definition of a group in Lean.
  It's not the definition we use use in mathlib. The actual definition uses classes,
  and will be explained in detail in the next session. -/

structure Group :=
  (G : Type*)
  (op : G → G → G)
  (infix * := op) -- temporary notation `*` for `op`, just inside this structure declaration
  (op_assoc' : ∀ (x y z : G), (x * y) * z = x * (y * z))
  (id : G)
  (notation 1 := id) -- temporary notation `1` for `id`, just inside this structure declaration
  (id_op' : ∀ (x : G), 1 * x = x)
  (inv : G → G)
  (postfix ⁻¹ := inv) -- temporary notation `⁻¹` for `inv`, just inside this structure declaration
  (op_left_inv' : ∀ (x : G), x⁻¹ * x = 1)

/-! You can use the `extend` command to define a structure that adds fields
  to one or more existing structures. -/
structure CommGroup extends Group :=
  (infix * := op)
  (op_comm : ∀ (x y : G), x * y = y * x)

/- Here is an example: the rationals form a group under addition. -/
def rat_Group : Group :=
{ G := ℚ,
  op := (+), -- you can put parentheses around an infix operation to talk about the operation itself.
  op_assoc' := add_assoc,
  id := 0,
  id_op' := zero_add,
  inv := λ x, -x,
  op_left_inv' := neg_add_self }

/-- You can extend an object of a structure by using the structure notation and using
  `..<existing object>`. -/
def rat_CommGroup : CommGroup :=
{ G := ℚ, op_comm := add_comm, ..rat_Group }

namespace Group

variables {G : Group} /- Let `G` be a group -/

/- The following line declares that if `G : Group`, then we can also view `G` as a type. -/
instance : has_coe_to_sort Group := ⟨_, Group.G⟩
/- The following lines declare the notation `*`, `⁻¹` and `1` for the fields of `Group`. -/
instance : has_mul G := ⟨G.op⟩
instance : has_inv G := ⟨G.inv⟩
instance : has_one G := ⟨G.id⟩

/- the axioms for groups are satisfied -/
lemma op_assoc (x y z : G) : (x * y) * z = x * (y * z) := G.op_assoc' x y z

lemma id_op (x : G) : 1 * x = x := G.id_op' x

lemma op_left_inv (x : G) : x⁻¹ * x = 1 := G.op_left_inv' x

/- Use the axioms `op_assoc`, `id_op` and `op_left_inv` to prove the following lemma.
  The fields `op_assoc'`, `id_op'` and `op_left_inv'` should not be used directly, nor can you use
  any lemmas from the library about `mul`. -/
lemma eq_id_of_op_eq_self {G : Group} {x : G} : x * x = x → x = 1 :=
begin
  -- sorry
  intro hx, rw [←id_op x, ← op_left_inv x, op_assoc, hx]
  -- sorry
end

/- Apply the previous lemma to show that `⁻¹` is also a right-sided inverse. -/
lemma op_right_inv {G : Group} (x : G) : x * x⁻¹ = 1 :=
begin
  -- sorry
  apply eq_id_of_op_eq_self,
  rw [op_assoc x x⁻¹ (x * x⁻¹), ← op_assoc x⁻¹ x x⁻¹, op_left_inv, id_op]
  -- sorry
end

/- we can prove that `1` is also a right identity. -/
lemma op_id {G : Group} (x : G) : x * 1 = x :=
begin
  -- sorry
  rw [← op_left_inv x, ← op_assoc, op_right_inv, id_op]
  -- sorry
end

/-!
  However, it is inconvenient to use this group instance directly.
  One reason is that to use these group operations we now have to write
  `(x y : rat_Group)` instead of `(x y : ℚ)`.
  That's why in Lean we use classes for algebraic structures,
  explained in the next lecture.
-/

/- show that the cartesian product of two groups is a group. The underlying type will be `G × H`. -/

def prod_Group (G H : Group) : Group :=
-- sorry
{ G := G × H,
  op := λ x y, (x.1 * y.1, x.2 * y.2),
  op_assoc' := by { intros, ext; simp; rw [op_assoc] },
  id := (1, 1),
  id_op' := by { intros, ext; simp; rw [id_op] },
  inv := λ x, (x.1⁻¹, x.2⁻¹),
  op_left_inv' := by { intros, ext; simp; rw [op_left_inv] } }
-- sorry

end Group



/-! ### Exercise: Pointed types -/

structure pointed_type :=
(type : Type*)
(point : type)

namespace pointed_type
variables {A B : pointed_type}

/- The following line declares that if `A : pointed_type`, then we can also view `A` as a type. -/
instance : has_coe_to_sort pointed_type := ⟨_, pointed_type.type⟩

/- The product of two pointed types is a pointed type.
  The `@[simps point]` is a hint to `simp` that it can unfold the point of this definition. -/
@[simps point]
def prod (A B : pointed_type) : pointed_type :=
{ type := A × B,
  point := (A.point, B.point) }


end pointed_type

structure pointed_map (A B : pointed_type) :=
(to_fun : A → B)
(to_fun_point : to_fun A.point = B.point)

namespace pointed_map

infix ` →. `:25 := pointed_map

variables {A B C D : pointed_type}
variables {h : C →. D} {g : B →. C} {f f₁ f₂ : A →. B}

instance : has_coe_to_fun (A →. B) := ⟨λ _, A → B, pointed_map.to_fun⟩

@[simp] lemma coe_mk {f : A → B} {hf : f A.point = B.point} {x : A} :
  { pointed_map . to_fun := f, to_fun_point := hf } x = f x := rfl
@[simp] lemma coe_point : f A.point = B.point := f.to_fun_point

@[ext] protected lemma ext (hf₁₂ : ∀ x, f₁ x = f₂ x) : f₁ = f₂ :=
begin
  -- sorry
  cases f₁ with f₁ hf₁, cases f₂ with f₂ hf₂, congr, ext x, exact hf₁₂ x
  -- sorry
end

/-! Below we show that pointed types form a category. -/

def comp (g : B →. C) (f : A →. B) : A →. C :=
-- sorry
{ to_fun := g ∘ f,
  to_fun_point := by simp }
-- sorry

def id : A →. A :=
-- sorry
{ to_fun := id,
  to_fun_point := by simp }
-- sorry

/-! You can use projection notation for any declaration declared in the same namespace as the
  structure. For example, `g.comp f` means `pointed_map.comp g f` -/
lemma comp_assoc : h.comp (g.comp f) = (h.comp g).comp f :=
-- sorry
by { ext x, refl }
-- sorry

lemma id_comp : f.comp id = f :=
-- sorry
by { ext x, refl }
-- sorry

lemma comp_id : id.comp f = f :=
-- sorry
by { ext x, refl }
-- sorry

/-! Below we show that `A.prod B` (that is, `pointed_type.prod A B`) is a product in the category of
  pointed types. -/

def fst : A.prod B →. A :=
-- sorry
{ to_fun := prod.fst,
  to_fun_point := rfl }
-- sorry

def snd : A.prod B →. B :=
-- sorry
{ to_fun := prod.snd,
  to_fun_point := rfl }
-- sorry

def pair (f : C →. A) (g : C →. B) : C →. A.prod B :=
-- sorry
{ to_fun := λ c, (f c, g c),
  to_fun_point := by simp }
-- sorry

lemma fst_pair (f : C →. A) (g : C →. B) : fst.comp (f.pair g) = f :=
-- sorry
by { ext, simp [pair, fst, comp] }
-- sorry

lemma snd_pair (f : C →. A) (g : C →. B) : snd.comp (f.pair g) = g :=
-- sorry
by { ext, simp [pair, snd, comp] }
-- sorry

lemma pair_unique (f : C →. A) (g : C →. B) (u : C →. A.prod B) (h1u : fst.comp u = f)
  (h2u : snd.comp u = g) : u = f.pair g :=
begin
  -- sorry
  ext,
  { have : fst (u x) = f x, { rw [←h1u], simp [comp] }, simpa using this },
  { have : snd (u x) = g x, { rw [←h2u], simp [comp] }, simpa using this }
  -- sorry
end


end pointed_map

/-! As an advanced exercise, you can show that the category of pointed type has coproducts.
  For this we need quotients, the basic interface is given with the declarations
  `quot r`: the quotient of the equivalence relation generated by relation `r` on `A`
  `quot.mk r : A → quot r`,
  `quot.sound`
  `quot.lift` (see below)
  -/

#print quot
#print quot.mk
#print quot.sound
#print quot.lift

open sum

/-! We want to define the coproduct of pointed types `A` and `B` as the coproduct `A ⊕ B` of the
  underlying type, identifying the two basepoints.

  First define a relation that *only* relates `inl A.point ~ inr B.point`.
-/
def coprod_rel (A B : pointed_type) : (A ⊕ B) → (A ⊕ B) → Prop :=
-- sorry
λ x y, x = inl A.point ∧ y = inr B.point
-- sorry

namespace pointed_type

-- @[simps point]
-- omit
@[simps point]
-- omit
def coprod (A B : pointed_type) : pointed_type :=
-- sorry
{ type := quot (coprod_rel A B),
  point := quot.mk _ (inl A.point) }
-- sorry
end pointed_type

namespace pointed_map

variables {A B C D : pointed_type}

def inl : A →. A.coprod B :=
-- sorry
{ to_fun := quot.mk _ ∘ sum.inl,
  to_fun_point := rfl }
-- sorry

def inr : B →. A.coprod B :=
-- sorry
{ to_fun := quot.mk _ ∘ sum.inr,
  to_fun_point := by { refine (quot.sound _).symm, exact ⟨rfl, rfl⟩ } }
-- sorry

def elim (f : A →. C) (g : B →. C) : A.coprod B →. C :=
-- sorry
{ to_fun := quot.lift (sum.elim f g) (by { rintro _ _ ⟨rfl, rfl⟩, simp }),
  to_fun_point := by simp }
-- sorry

lemma elim_comp_inl (f : A →. C) (g : B →. C) : (f.elim g).comp inl = f :=
-- sorry
by { ext, simp [elim, inl, comp] }
-- sorry

lemma elim_comp_inr (f : A →. C) (g : B →. C) : (f.elim g).comp inr = g :=
-- sorry
by { ext, simp [elim, inr, comp] }
-- sorry

lemma elim_unique (f : A →. C) (g : B →. C) (u : A.coprod B →. C) (h1u : u.comp inl = f)
  (h2u : u.comp inr = g) : u = f.elim g :=
begin
  -- sorry
  ext (x|y),
  { have : u (inl x) = f x, { rw [←h1u], simp [comp] }, simpa [elim, inl] using this },
  { have : u (inr y) = g y, { rw [←h2u], simp [comp] }, simpa [elim, inl] using this }
  -- sorry
end

end pointed_map
