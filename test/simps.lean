import tactic.simps
import algebra.group.hom

universe variables v u w
-- set_option trace.simps.verbose true
-- set_option trace.simps.debug true
-- set_option trace.app_builder true

open function tactic expr


structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

local infix ` ≃ `:25 := equiv

-- initialize_simps_projections equiv

/- Since `prod` and `pprod` are a special case for `@[simps]`, we define a new structure to test
  the basic functionality.-/
structure my_prod (α β : Type*) := (fst : α) (snd : β)

def myprod.map {α α' β β'} (f : α → α') (g : β → β') (x : my_prod α β) : my_prod α' β' :=
⟨f x.1, g x.2⟩

namespace foo
@[simps] protected def rfl {α} : α ≃ α :=
⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

/- simps adds declarations -/
run_cmd do
  e ← get_env,
  e.get `foo.rfl_to_fun,
  e.get `foo.rfl_inv_fun,
  success_if_fail (e.get `foo.rfl_left_inv),
  success_if_fail (e.get `foo.rfl_right_inv)

example (n : ℕ) : foo.rfl.to_fun n = n := by rw [foo.rfl_to_fun, id]
example (n : ℕ) : foo.rfl.inv_fun n = n := by rw [foo.rfl_inv_fun]

/- the declarations are simp-lemmas -/
@[simps] def foo : ℕ × ℤ := (1, 2)

example : foo.1 = 1 := by simp
example : foo.2 = 2 := by simp
example : foo.1 = 1 := by { dsimp, refl } -- check that dsimp also unfolds
example : foo.2 = 2 := by { dsimp, refl }
example {α} (x : α) : foo.rfl.to_fun x = x := by simp
example {α} (x : α) : foo.rfl.inv_fun x = x := by simp
example {α} (x : α) : foo.rfl.to_fun = @id α := by { success_if_fail {simp}, refl }

/- check some failures -/
def bar1 : ℕ := 1 -- type is not a structure
noncomputable def bar2 {α} : α ≃ α :=
classical.choice ⟨foo.rfl⟩

run_cmd do
  success_if_fail_with_msg (simps_tac `foo.bar1)
    "Invalid `simps` attribute. Target nat is not a structure",
  success_if_fail_with_msg (simps_tac `foo.bar2)
    "Invalid `simps` attribute. The body is not a constructor application:
  classical.choice bar2._proof_1",
  e ← get_env,
  let nm := `foo.bar1,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  simps_add_projections e nm "" d.type lhs d.value [] d.univ_params ff {} [] []


/- test that if a non-constructor is given as definition, then
  `{rhs_md := semireducible, simp_rhs := tt}` is applied automatically. -/
@[simps] def rfl2 {α} : α ≃ α := foo.rfl

example {α} (x : α) : rfl2.to_fun x = x ∧ rfl2.inv_fun x = x :=
begin
  dsimp only [rfl2_to_fun, rfl2_inv_fun],
  guard_target (x = x ∧ x = x),
  exact ⟨rfl, rfl⟩
end

/- test `fully_applied` option -/

@[simps {fully_applied := ff}] def rfl3 {α} : α ≃ α := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

end foo

/- we reduce the type when applying [simps] -/
def my_equiv := equiv
@[simps] def baz : my_equiv ℕ ℕ := ⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

/- test name clashes -/
def name_clash_fst := 1
def name_clash_snd := 1
def name_clash_snd_2 := 1
@[simps] def name_clash := (2, 3)

run_cmd do
  e ← get_env,
  e.get `name_clash_fst_2,
  e.get `name_clash_snd_3

/- check projections for nested structures -/

namespace count_nested
@[simps {attrs := [`simp, `norm]}] def nested1 : my_prod ℕ $ my_prod ℤ ℕ :=
⟨2, -1, 1⟩

@[simps {attrs := []}] def nested2 : ℕ × my_prod ℕ ℕ :=
⟨2, myprod.map nat.succ nat.pred ⟨1, 2⟩⟩

end count_nested

run_cmd do
  e ← get_env,
  e.get `count_nested.nested1_fst,
  e.get `count_nested.nested1_snd_fst,
  e.get `count_nested.nested1_snd_snd,
  e.get `count_nested.nested2_fst,
  e.get `count_nested.nested2_snd,
  is_simp_lemma `count_nested.nested1_fst >>= λ b, guard b, -- simp attribute is global
  is_simp_lemma `count_nested.nested2_fst >>= λ b, guard $ ¬b, --lemmas_only doesn't add simp lemma
  guard $ 7 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `count_nested then 1 else 0)

-- testing with arguments
@[simps] def bar {α : Type*} (n m : ℕ) : ℕ × ℤ :=
⟨n - m, n + m⟩

structure equiv_plus_data (α β) extends α ≃ β :=
(P : (α → β) → Prop)
(data : P to_fun)

structure automorphism_plus_data α extends α ⊕ α ≃ α ⊕ α :=
(P : (α ⊕ α → α ⊕ α) → Prop)
(data : P to_fun)
(extra : bool → my_prod ℕ ℕ)

@[simps]
def refl_with_data {α} : equiv_plus_data α α :=
{ P := λ f, f = id,
  data := rfl,
  ..foo.rfl }

@[simps]
def refl_with_data' {α} : equiv_plus_data α α :=
{ P := λ f, f = id,
  data := rfl,
  to_equiv := foo.rfl }

/- test whether eta expansions are reduced correctly -/
@[simps]
def test {α} : automorphism_plus_data α :=
{ P := λ f, f = id,
  data := rfl,
  extra := λ b, ⟨(⟨3, 5⟩ : my_prod _ _).1, (⟨3, 5⟩ : my_prod _ _).2⟩,
  ..foo.rfl }

/- test whether this is indeed rejected as a valid eta expansion -/
@[simps]
def test_sneaky {α} : automorphism_plus_data α :=
{ P := λ f, f = id,
  data := rfl,
  extra := λ b, ⟨(3,5).1,(3,5).2⟩,
  ..foo.rfl }

run_cmd do
  e ← get_env,
  e.get `refl_with_data_to_equiv,
  e.get `refl_with_data'_to_equiv,
  e.get `test_extra,
  e.get `test_sneaky_extra_fst,
  success_if_fail (e.get `refl_with_data_to_equiv_to_fun),
  success_if_fail (e.get `refl_with_data'_to_equiv_to_fun),
  success_if_fail (e.get `test_extra_fst),
  success_if_fail (e.get `test_sneaky_extra)

structure partially_applied_str :=
(data : ℕ → my_prod ℕ ℕ)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[simps]
def partially_applied_term : partially_applied_str := ⟨my_prod.mk 3⟩

run_cmd do
  e ← get_env,
  e.get `partially_applied_term_data_fst,
  e.get `partially_applied_term_data_snd

structure very_partially_applied_str :=
(data : ∀β, ℕ → β → my_prod ℕ β)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded.
  (this is not very useful, and we could remove this behavior if convenient) -/
@[simps]
def very_partially_applied_term : very_partially_applied_str := ⟨@my_prod.mk ℕ⟩

run_cmd do
  e ← get_env,
  e.get `very_partially_applied_term_data_fst,
  e.get `very_partially_applied_term_data_snd

@[simps] def let1 : ℕ × ℤ :=
let n := 3 in ⟨n + 4, 5⟩

@[simps] def let2 : ℕ × ℤ :=
let n := 3, m := 4 in let k := 5 in ⟨n + m, k⟩

@[simps] def let3 : ℕ → ℕ × ℤ :=
λ n, let m := 4, k := 5 in ⟨n + m, k⟩

@[simps] def let4 : ℕ → ℕ × ℤ :=
let m := 4, k := 5 in λ n, ⟨n + m, k⟩

run_cmd do
  e ← get_env,
  e.get `let1_fst, e.get `let2_fst, e.get `let3_fst, e.get `let4_fst,
  e.get `let1_snd, e.get `let2_snd, e.get `let3_snd, e.get `let4_snd


namespace specify
@[simps fst] def specify1 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd] def specify2 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd_fst] def specify3 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd snd_snd snd_snd] def specify4 : ℕ × ℕ × ℕ := (1, 2, 3) -- last argument is ignored
@[simps] noncomputable def specify5 : ℕ × ℕ × ℕ := (1, classical.choice ⟨(2, 3)⟩)
end specify

run_cmd do
  e ← get_env,
  e.get `specify.specify1_fst, e.get `specify.specify2_snd,
  e.get `specify.specify3_snd_fst, e.get `specify.specify4_snd_snd, e.get `specify.specify4_snd,
  e.get `specify.specify5_fst, e.get `specify.specify5_snd,
  guard $ 12 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `specify then 1 else 0),
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["fst_fst"])
    "Invalid simp-lemma specify.specify1_fst_fst.
Projection fst doesn't exist, because target is not a structure.",
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["foo_fst"])
    "Invalid simp-lemma specify.specify1_foo_fst. Structure prod does not have projection foo.
The known projections are:
  [fst, snd]
You can also see this information by running
  `initialize_simps_projections? prod`.
Note: these projection names might not correspond to the projection names of the structure.",
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["snd_bar"])
    "Invalid simp-lemma specify.specify1_snd_bar. Structure prod does not have projection bar.
The known projections are:
  [fst, snd]
You can also see this information by running
  `initialize_simps_projections? prod`.
Note: these projection names might not correspond to the projection names of the structure.",
  success_if_fail_with_msg (simps_tac `specify.specify5 {} ["snd_snd"])
    "Invalid simp-lemma specify.specify5_snd_snd.
The given definition is not a constructor application:
  classical.choice specify.specify5._proof_1"


/- We also eta-reduce if we explicitly specify the projection. -/
attribute [simps extra] test
run_cmd do
  e ← get_env,
  d1 ← e.get `test_extra,
  d2 ← e.get `test_extra_2,
  guard $ d1.type =ₐ d2.type,
  skip

/- check short_name option -/
@[simps {short_name := tt}] def short_name1 : my_prod ℕ ℕ × my_prod ℕ ℕ := ⟨⟨1, 2⟩, 3, 4⟩
run_cmd do
  e ← get_env,
  e.get `short_name1_fst, e.get `short_name1_fst_2,
  e.get `short_name1_snd, e.get `short_name1_snd_2

/- check simp_rhs option -/
@[simps {simp_rhs := tt}] def equiv.trans {α β γ} (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
⟨g.to_fun ∘ f.to_fun, f.inv_fun ∘ g.inv_fun,
  by { intro x, simp [equiv.left_inv _ _] }, by { intro x, simp [equiv.right_inv _ _] }⟩


example {α β γ : Type} (f : α ≃ β) (g : β ≃ γ) (x : α) :
  (f.trans g).to_fun x = (f.trans g).to_fun x :=
begin
  dsimp only [equiv.trans_to_fun],
  guard_target g.to_fun (f.to_fun x) = g.to_fun (f.to_fun x),
  refl,
end

local attribute [simp] nat.zero_add nat.one_mul nat.mul_one
@[simps {simp_rhs := tt}] def my_nat_equiv : ℕ ≃ ℕ :=
⟨λ n, 0 + n, λ n, 1 * n * 1, by { intro n, simp }, by { intro n, simp }⟩

run_cmd success_if_fail (has_attribute `_refl_lemma `my_nat_equiv_to_fun) >>
  has_attribute `_refl_lemma `equiv.trans_to_fun

example (n : ℕ) : my_nat_equiv.to_fun (my_nat_equiv.to_fun $ my_nat_equiv.inv_fun n) = n :=
by { success_if_fail { refl }, simp only [my_nat_equiv_to_fun, my_nat_equiv_inv_fun] }

@[simps {simp_rhs := tt}] def succeed_without_simplification_possible : ℕ ≃ ℕ :=
⟨λ n, n, λ n, n, by { intro n, refl }, by { intro n, refl }⟩


/- test that we don't recursively take projections of `prod` and `pprod` -/
@[simps] def pprod_equiv_prod : pprod ℕ ℕ ≃ ℕ × ℕ :=
{ to_fun := λ x, ⟨x.1, x.2⟩,
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

run_cmd do
  e ← get_env,
  e.get `pprod_equiv_prod_to_fun,
  e.get `pprod_equiv_prod_inv_fun

attribute [simps to_fun_fst inv_fun_snd] pprod_equiv_prod

run_cmd do
  e ← get_env,
  e.get `pprod_equiv_prod_to_fun_fst,
  e.get `pprod_equiv_prod_inv_fun_snd

-- we can disable this behavior with the option `not_recursive`.
@[simps {not_recursive := []}] def pprod_equiv_prod2 : pprod ℕ ℕ ≃ ℕ × ℕ :=
pprod_equiv_prod

run_cmd do
  e ← get_env,
  e.get `pprod_equiv_prod2_to_fun_fst,
  e.get `pprod_equiv_prod2_to_fun_snd,
  e.get `pprod_equiv_prod2_inv_fun_fst,
  e.get `pprod_equiv_prod2_inv_fun_snd

/- Tests with universe levels -/
class has_hom (obj : Type u) : Type (max u (v+1)) :=
(hom : obj → obj → Type v)

infixr ` ⟶ `:10 := has_hom.hom -- type as \h

class category_struct (obj : Type u) extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

@[simps] instance types : category_struct (Type u) :=
{ hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f }

example (X : Type u) : (X ⟶ X) = (X → X) := by simp
example (X : Type u) : 𝟙 X = (λ x, x) := by { funext, simp }
example (X Y Z : Type u) (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := by { funext, simp }

namespace coercing

structure foo_str :=
 (c : Type)
 (x : c)

instance : has_coe_to_sort foo_str := ⟨_, foo_str.c⟩

@[simps] def foo : foo_str := ⟨ℕ, 3⟩
@[simps] def foo2 : foo_str := ⟨ℕ, 34⟩

example : ↥foo = ℕ := by simp only [foo_c]
example : foo.x = (3 : ℕ) := by simp only [foo_x]

structure voo_str (n : ℕ) :=
 (c : Type)
 (x : c)

instance has_coe_voo_str (n : ℕ) : has_coe_to_sort (voo_str n) := ⟨_, voo_str.c⟩

@[simps] def voo : voo_str 7 := ⟨ℕ, 3⟩
@[simps] def voo2 : voo_str 4 := ⟨ℕ, 34⟩

example : ↥voo = ℕ := by simp only [voo_c]
example : voo.x = (3 : ℕ) := by simp only [voo_x]

structure equiv2 (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

instance {α β} : has_coe_to_fun $ equiv2 α β := ⟨_, equiv2.to_fun⟩

@[simps] protected def rfl2 {α} : equiv2 α α :=
⟨λ x, x, λ x, x, λ x, rfl, λ x, rfl⟩

example {α} (x : α) : coercing.rfl2 x = x := by rw [coercing.rfl2_to_fun]
example {α} (x : α) : coercing.rfl2 x = x := by simp
example {α} (x : α) : coercing.rfl2.inv_fun x = x := by simp

@[simps] protected def equiv2.symm {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.inv_fun, f, f.right_inv, f.left_inv⟩

@[simps] protected def equiv2.symm2 {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.inv_fun, f.to_fun, f.right_inv, f.left_inv⟩

/- we can use the `md` attribute to not unfold the `has_coe_to_fun` attribute, so that `@[simps]`
  doesn't recognize that the type of `⇑f` is still a function type. -/
@[simps {type_md := reducible}] protected def equiv2.symm3 {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.inv_fun, f, f.right_inv, f.left_inv⟩

example {α β} (f : equiv2 α β) (y : β) : f.symm y = f.inv_fun y := by simp
example {α β} (f : equiv2 α β) (x : α) : f.symm.inv_fun x = f x := by simp

example {α β} (f : equiv2 α β) : f.symm.inv_fun = f := by { success_if_fail {simp}, refl }
example {α β} (f : equiv2 α β) : f.symm3.inv_fun = f := by simp

section
set_option old_structure_cmd true
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
end

@[simps] instance {α β} [semigroup α] [semigroup β] : semigroup (α × β) :=
{ mul := λ x y, (x.1 * y.1, x.2 * y.2),
  mul_assoc := by { intros, simp only [semigroup.mul_assoc], refl } }

example {α β} [semigroup α] [semigroup β] (x y : α × β) : x * y = (x.1 * y.1, x.2 * y.2) :=
by simp
example {α β} [semigroup α] [semigroup β] (x y : α × β) : (x * y).1 = x.1 * y.1 := by simp

structure Semigroup :=
  (G : Type*)
  (op : G → G → G)
  (infix * := op)
  (op_assoc : ∀ (x y z : G), (x * y) * z = x * (y * z))

namespace Group

instance : has_coe_to_sort Semigroup := ⟨_, Semigroup.G⟩
-- We could try to generate lemmas with this `has_mul` instance, but it is unused in mathlib.
-- Therefore, this is ignored.
instance (G : Semigroup) : has_mul G := ⟨G.op⟩

@[simps] def prod_Semigroup (G H : Semigroup) : Semigroup :=
{ G := G × H,
  op := λ x y, (x.1 * y.1, x.2 * y.2),
  op_assoc := by { intros, dsimp [Group.has_mul], simp [Semigroup.op_assoc] }}


end Group

section
set_option old_structure_cmd true
class extending_stuff (G : Type u) extends has_mul G, has_zero G, has_neg G, has_subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)
end

@[simps] def bar : extending_stuff ℕ :=
{ mul := (*),
  zero := 0,
  neg := nat.succ,
  subset := λ x y, true,
  new_axiom := λ x, trivial }

section
local attribute [instance] bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end

class new_extending_stuff (G : Type u) extends has_mul G, has_zero G, has_neg G, has_subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)

@[simps] def new_bar : new_extending_stuff ℕ :=
{ mul := (*),
  zero := 0,
  neg := nat.succ,
  subset := λ x y, true,
  new_axiom := λ x, trivial }

section
local attribute [instance] new_bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end


end coercing

namespace manual_coercion

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := manual_coercion.equiv

variables {α β γ : Sort*}

instance : has_coe_to_fun $ α ≃ β := ⟨_, equiv.to_fun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

/-- See Note [custom simps projection] -/
def equiv.simps.inv_fun (e : α ≃ β) : β → α := e.symm

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps {simp_rhs := tt}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [equiv.trans_inv_fun]

end manual_coercion

namespace faulty_manual_coercion

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := faulty_manual_coercion.equiv

variables {α β γ : Sort*}

/-- See Note [custom simps projection] -/
noncomputable def equiv.simps.inv_fun (e : α ≃ β) : β → α := classical.choice ⟨e.inv_fun⟩

run_cmd do e ← get_env, success_if_fail_with_msg (simps_get_raw_projections e `faulty_manual_coercion.equiv)
"Invalid custom projection:
  λ {α : Sort u_1} {β : Sort u_2} (e : α ≃ β), classical.choice _
Expression is not definitionally equal to
  λ (α : Sort u_1) (β : Sort u_2) (x : α ≃ β), x.inv_fun"

end faulty_manual_coercion

namespace manual_initialize
/- defining a manual coercion. -/
variables {α β γ : Sort*}

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := manual_initialize.equiv

instance : has_coe_to_fun $ α ≃ β := ⟨_, equiv.to_fun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for equiv.symm than for equiv
def equiv.simps.inv_fun (e : α ≃ β) : β → α := e.symm

initialize_simps_projections equiv

run_cmd has_attribute `_simps_str `manual_initialize.equiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps {simp_rhs := tt}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

end manual_initialize

namespace faulty_universes

variables {α β γ : Sort*}

structure equiv (α : Sort u) (β : Sort v) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := faulty_universes.equiv

instance : has_coe_to_fun $ α ≃ β := ⟨_, equiv.to_fun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different names for the universe variables for equiv.symm than for
-- equiv
def equiv.simps.inv_fun {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.symm

run_cmd do e ← get_env,
  success_if_fail_with_msg (simps_get_raw_projections e `faulty_universes.equiv)
"Invalid custom projection:
  λ {α : Type u} {β : Type v} (e : α ≃ β), ⇑(e.symm)
Expression has different type than faulty_universes.equiv.inv_fun. Given type:
  Π {α : Type u} {β : Type v} (e : α ≃ β), has_coe_to_fun.F e.symm
Expected type:
  Π (α : Sort u) (β : Sort v), α ≃ β → β → α"

end faulty_universes

namespace manual_universes

variables {α β γ : Sort*}

structure equiv (α : Sort u) (β : Sort v) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := manual_universes.equiv

instance : has_coe_to_fun $ α ≃ β := ⟨_, equiv.to_fun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for equiv.symm than for equiv
def equiv.simps.inv_fun {α : Sort w} {β : Sort u} (e : α ≃ β) : β → α := e.symm

-- check whether we can generate custom projections even if the universe names don't match
initialize_simps_projections equiv

end manual_universes

namespace manual_projection_names

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := manual_projection_names.equiv

variables {α β γ : Sort*}

instance : has_coe_to_fun $ α ≃ β := ⟨_, equiv.to_fun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

/-- See Note [custom simps projection] -/
def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
-- set_option trace.simps.debug true
initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)

run_cmd do
  e ← get_env,
  data ← simps_get_raw_projections e `manual_projection_names.equiv,
  guard $ data.2.map prod.fst = [`apply, `symm_apply]

@[simps {simp_rhs := tt}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) :=
by simp only [equiv.trans_apply]

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [equiv.trans_symm_apply]

-- the new projection names are parsed correctly (the old projection names won't work anymore)
@[simps apply symm_apply] protected def equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

-- initialize_simps_projections equiv

end manual_projection_names


-- test transparency setting
structure set_plus (α : Type) :=
(s : set α)
(x : α)
(h : x ∈ s)

@[simps] def nat_set_plus : set_plus ℕ := ⟨set.univ, 1, trivial⟩

example : nat_set_plus.s = set.univ :=
begin
  dsimp only [nat_set_plus_s],
  guard_target @set.univ ℕ = set.univ,
  refl
end

@[simps {type_md := semireducible}] def nat_set_plus2 : set_plus ℕ := ⟨set.univ, 1, trivial⟩

example : nat_set_plus2.s = set.univ :=
begin
  success_if_fail { dsimp only [nat_set_plus2_s] }, refl
end

@[simps {rhs_md := semireducible}] def nat_set_plus3 : set_plus ℕ := nat_set_plus

example : nat_set_plus3.s = set.univ :=
begin
  dsimp only [nat_set_plus3_s],
  guard_target @set.univ ℕ = set.univ,
  refl
end

namespace nested_non_fully_applied

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := nested_non_fully_applied.equiv

variables {α β γ : Sort*}

@[simps] def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun⟩

@[simps {rhs_md := semireducible, fully_applied := ff}] def equiv.symm2 : (α ≃ β) ≃ (β ≃ α) :=
⟨equiv.symm, equiv.symm⟩

example (e : α ≃ β) : (equiv.symm2.inv_fun e).to_fun = e.inv_fun :=
begin
  dsimp only [equiv.symm2_inv_fun_to_fun],
  guard_target e.inv_fun = e.inv_fun,
  refl
end

/- do not prematurely unfold `equiv.symm`, unless necessary -/
@[simps to_fun to_fun_to_fun {rhs_md := semireducible}] def equiv.symm3 : (α ≃ β) ≃ (β ≃ α) :=
equiv.symm2

example (e : α ≃ β) (y : β) : (equiv.symm3.to_fun e).to_fun y = e.inv_fun y ∧
  (equiv.symm3.to_fun e).to_fun y = e.inv_fun y :=
begin
  split,
  { dsimp only [equiv.symm3_to_fun], guard_target e.symm.to_fun y = e.inv_fun y, refl },
  { dsimp only [equiv.symm3_to_fun_to_fun], guard_target e.inv_fun y = e.inv_fun y, refl }
end

end nested_non_fully_applied

-- test that type classes which are props work
class prop_class (n : ℕ) : Prop :=
(has_true : true)

instance has_prop_class (n : ℕ) : prop_class n := ⟨trivial⟩

structure needs_prop_class (n : ℕ) [prop_class n] :=
(t : true)

@[simps] def test_prop_class : needs_prop_class 1 :=
{ t := trivial }

/- check that when the coercion is given in eta-expanded form, we can also find the coercion. -/
structure alg_hom (R A B : Type*) :=
(to_fun : A → B)

instance (R A B : Type*) : has_coe_to_fun (alg_hom R A B) := ⟨_, λ f, f.to_fun⟩

@[simps] def my_alg_hom : alg_hom unit bool bool :=
{ to_fun := id }

example (x : bool) : my_alg_hom x = id x := by simp only [my_alg_hom_to_fun]

structure ring_hom (A B : Type*) :=
(to_fun : A → B)

instance (A B : Type*) : has_coe_to_fun (ring_hom A B) := ⟨_, λ f, f.to_fun⟩

@[simps] def my_ring_hom : ring_hom bool bool :=
{ to_fun := id }

example (x : bool) : my_ring_hom x = id x := by simp only [my_ring_hom_to_fun]

/- check interaction with the `@[to_additive]` attribute -/

@[to_additive, simps]
instance {M N} [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩

run_cmd do
  e ← get_env,
  e.get `prod.has_mul_mul,
  e.get `prod.has_add_add,
  has_attribute `to_additive `prod.has_mul,
  has_attribute `to_additive `prod.has_mul_mul,
  has_attribute `simp `prod.has_mul_mul,
  has_attribute `simp `prod.has_add_add

example {M N} [has_mul M] [has_mul N] (p q : M × N) : p * q = ⟨p.1 * q.1, p.2 * q.2⟩ := by simp
example {M N} [has_add M] [has_add N] (p q : M × N) : p + q = ⟨p.1 + q.1, p.2 + q.2⟩ := by simp

/- The names of the generated simp lemmas for the additive version are not great if the definition
  had a custom additive name -/
@[to_additive my_add_instance, simps]
instance my_instance {M N} [has_one M] [has_one N] : has_one (M × N) := ⟨(1, 1)⟩

run_cmd do
  e ← get_env,
  e.get `my_instance_one,
  e.get `my_instance_zero,
  has_attribute `to_additive `my_instance,
  has_attribute `to_additive `my_instance_one,
  has_attribute `simp `my_instance_one,
  has_attribute `simp `my_instance_zero

example {M N} [has_one M] [has_one N] : (1 : M × N) = ⟨1, 1⟩ := by simp
example {M N} [has_zero M] [has_zero N] : (0 : M × N) = ⟨0, 0⟩ := by simp

section
/-! Test `dsimp, simp` with the option `simp_rhs` -/

local attribute [simp] nat.add

structure my_type :=
(A : Type)

@[simps {simp_rhs := tt}] def my_type_def : my_type := ⟨{ x : fin (nat.add 3 0) // 1 + 1 = 2 }⟩

example (h : false) (x y : { x : fin (nat.add 3 0) // 1 + 1 = 2 }) : my_type_def.A = unit :=
begin
  simp only [my_type_def_A],
  guard_target ({ x : fin 3 // true } = unit),
  /- note: calling only one of `simp` or `dsimp` does not produce the current target,
  as the following tests show. -/
  success_if_fail { guard_hyp x : { x : fin 3 // true } },
  dsimp at x,
  success_if_fail { guard_hyp x : { x : fin 3 // true } },
  simp at y,
  success_if_fail { guard_hyp y : { x : fin 3 // true } },
  simp at x, dsimp at y,
  guard_hyp x : { x : fin 3 // true },
  guard_hyp y : { x : fin 3 // true },
  contradiction
end

/- Test that `to_additive` copies the `@[_refl_lemma]` attribute correctly -/
@[to_additive, simps]
def monoid_hom.my_comp {M N P : Type*} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ to_fun := hnp ∘ hmn, map_one' := by simp, map_mul' := by simp, }

-- `simps` adds the `_refl_lemma` attribute to `monoid_hom.my_comp_apply`
example {M N P : Type*} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) :=
by { dsimp, guard_target (hnp (hmn m) = hnp (hmn m)), refl }

-- `to_additive` adds the `_refl_lemma` attribute to `add_monoid_hom.my_comp_apply`
example {M N P : Type*} [add_zero_class M] [add_zero_class N] [add_zero_class P]
  (hnp : N →+ P) (hmn : M →+ N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) :=
by { dsimp, guard_target (hnp (hmn m) = hnp (hmn m)), refl }

end

/- Test custom compositions of projections. -/

section comp_projs

instance {α β} : has_coe_to_fun (α ≃ β) := ⟨λ _, α → β, equiv.to_fun⟩

@[simps] protected def equiv.symm {α β} (f : α ≃ β) : β ≃ α :=
⟨f.inv_fun, f, f.right_inv, f.left_inv⟩

structure decorated_equiv (α : Sort*) (β : Sort*) extends equiv α β :=
(P_to_fun    : function.injective to_fun )
(P_inv_fun   : function.injective inv_fun)

instance {α β} : has_coe_to_fun (decorated_equiv α β) := ⟨λ _, α → β, λ f, f.to_equiv⟩

def decorated_equiv.symm {α β : Sort*} (e : decorated_equiv α β) : decorated_equiv β α :=
{ to_equiv := e.to_equiv.symm,
  P_to_fun := e.P_inv_fun,
  P_inv_fun := e.P_to_fun }

def decorated_equiv.simps.apply {α β : Sort*} (e : decorated_equiv α β) : α → β := e
def decorated_equiv.simps.symm_apply {α β : Sort*} (e : decorated_equiv α β) : β → α := e.symm

initialize_simps_projections decorated_equiv
  (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply, -to_equiv)

@[simps] def foo (α : Type) : decorated_equiv α α :=
{ to_fun    := λ x, x,
  inv_fun   := λ x, x,
  left_inv  := λ x, rfl,
  right_inv := λ x, rfl,
  P_to_fun  := λ x y h, h,
  P_inv_fun := λ x y h, h }

example {α : Type} (x : α) : (foo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps to_equiv apply symm_apply] def foo2 (α : Type) : decorated_equiv α α :=
{ P_to_fun  := λ x y h, h,
  P_inv_fun := λ x y h, h, ..foo.rfl }

example {α : Type} (x : α) : (foo2 α).to_equiv x = x :=
by { dsimp, guard_target (foo.rfl x = x), refl }

example {α : Type} (x : α) : foo2 α x = x :=
by { dsimp, guard_target (x = x), refl }

structure further_decorated_equiv (α : Sort*) (β : Sort*) extends decorated_equiv α β :=
(Q_to_fun    : function.surjective to_fun )
(Q_inv_fun   : function.surjective inv_fun )

instance {α β} : has_coe_to_fun (further_decorated_equiv α β) :=
⟨λ _, α → β, λ f, f.to_decorated_equiv⟩

def further_decorated_equiv.symm {α β : Sort*} (e : further_decorated_equiv α β) :
  further_decorated_equiv β α :=
{ to_decorated_equiv := e.to_decorated_equiv.symm,
  Q_to_fun := e.Q_inv_fun,
  Q_inv_fun := e.Q_to_fun }

def further_decorated_equiv.simps.apply {α β : Sort*} (e : further_decorated_equiv α β) : α → β := e
def further_decorated_equiv.simps.symm_apply {α β : Sort*} (e : further_decorated_equiv α β) :
  β → α := e.symm

initialize_simps_projections further_decorated_equiv
  (to_decorated_equiv_to_equiv_to_fun → apply, to_decorated_equiv_to_equiv_inv_fun → symm_apply,
  -to_decorated_equiv, to_decorated_equiv_to_equiv → to_equiv, -to_equiv)

@[simps] def ffoo (α : Type) : further_decorated_equiv α α :=
{ to_fun    := λ x, x,
  inv_fun   := λ x, x,
  left_inv  := λ x, rfl,
  right_inv := λ x, rfl,
  P_to_fun  := λ x y h, h,
  P_inv_fun := λ x y h, h,
  Q_to_fun  := λ y, ⟨y, rfl⟩,
  Q_inv_fun := λ y, ⟨y, rfl⟩ }

example {α : Type} (x : α) : (ffoo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps] def ffoo3 (α : Type) : further_decorated_equiv α α :=
{ Q_to_fun  := λ y, ⟨y, rfl⟩, Q_inv_fun  := λ y, ⟨y, rfl⟩, .. foo α }

@[simps apply to_equiv_to_fun to_decorated_equiv_apply]
def ffoo4 (α : Type) : further_decorated_equiv α α :=
{ Q_to_fun  := λ y, ⟨y, rfl⟩, Q_inv_fun  := λ y, ⟨y, rfl⟩, to_decorated_equiv := foo α }

structure one_more (α : Sort*) (β : Sort*) extends further_decorated_equiv α β

instance {α β} : has_coe_to_fun (one_more α β) :=
⟨λ _, α → β, λ f, f.to_further_decorated_equiv⟩

def one_more.symm {α β : Sort*} (e : one_more α β) :
  one_more β α :=
{ to_further_decorated_equiv := e.to_further_decorated_equiv.symm }

def one_more.simps.apply {α β : Sort*} (e : one_more α β) : α → β := e
def one_more.simps.symm_apply {α β : Sort*} (e : one_more α β) : β → α := e.symm

initialize_simps_projections one_more
  (to_further_decorated_equiv_to_decorated_equiv_to_equiv_to_fun → apply,
   to_further_decorated_equiv_to_decorated_equiv_to_equiv_inv_fun → symm_apply,
  -to_further_decorated_equiv, to_further_decorated_equiv_to_decorated_equiv → to_dequiv,
  -to_dequiv)
set_option trace.simps.debug true

@[simps] def fffoo (α : Type) : one_more α α :=
{ to_fun    := λ x, x,
  inv_fun   := λ x, x,
  left_inv  := λ x, rfl,
  right_inv := λ x, rfl,
  P_to_fun  := λ x y h, h,
  P_inv_fun := λ x y h, h,
  Q_to_fun  := λ y, ⟨y, rfl⟩,
  Q_inv_fun := λ y, ⟨y, rfl⟩ }

example {α : Type} (x : α) : (fffoo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps apply to_dequiv_apply to_further_decorated_equiv_apply to_dequiv]
def fffoo2 (α : Type) : one_more α α := fffoo α

/- test the case where a projection takes additional arguments. -/
variables {ι : Type*} [decidable_eq ι] (A : ι → Type*)

class something [has_add ι] [Π i, add_comm_monoid (A i)] :=
(mul {i} : A i →+ A i)

def something.simps.apply [has_add ι] [Π i, add_comm_monoid (A i)] [something A] {i : ι} (x : A i) :
  A i :=
something.mul ι x

initialize_simps_projections something (mul_to_fun → apply, -mul)

class something2 [has_add ι] :=
(mul {i j} : A i ≃ (A j ≃ A (i + j)))

def something2.simps.mul [has_add ι] [something2 A] {i j : ι}
  (x : A i) (y : A j) : A (i + j) :=
something2.mul x y

initialize_simps_projections? something2 (mul → mul', mul_to_fun_to_fun → mul, -mul')


set_option trace.simps.verbose true
set_option trace.simps.debug true
set_option trace.app_builder true

attribute [ext] equiv

@[simps]
def thing (h : bool ≃ (bool ≃ bool)) : something2 (λ x : ℕ, bool) :=
{ mul := λ i j, { to_fun := λ b, { to_fun := h b,
  inv_fun := (h b).symm,
  left_inv := (h b).left_inv,
  right_inv := (h b).right_inv },
  inv_fun := h.symm,
  left_inv := by { convert h.left_inv, ext x; refl },
  right_inv := by { convert h.right_inv, ext x; refl } } }

-- λ {i j : ℕ} (x : (λ (x : ℕ), bool) i) (y : (λ (x : ℕ), bool) j),
--   ⇑(⇑something2.mul x) y = (⇑(⇑h b) ᾰ : bool)

--         > ⇑((fffoo α).symm) x = (x : α)
end comp_projs
