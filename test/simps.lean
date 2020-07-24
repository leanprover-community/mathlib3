import tactic.simps

-- set_option trace.simps.verbose true
-- set_option trace.app_builder true

open function tactic expr


structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

local infix ` ≃ `:25 := equiv

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
def bar2 : ℕ × ℤ := prod.map (λ x, x + 2) (λ y, y - 3) (3, 4) -- value is not a constructor
noncomputable def bar3 {α} : α ≃ α :=
classical.choice ⟨foo.rfl⟩

run_cmd do
  success_if_fail_with_msg (simps_tac `foo.bar1)
    "Invalid `simps` attribute. Target is not a structure",
  success_if_fail_with_msg (simps_tac `foo.bar2)
    "Invalid `simps` attribute. The body is not a constructor application:
prod.map (λ (x : ℕ), x + 2) (λ (y : ℤ), y - 3) (3, 4)
Possible solution: add option {rhs_md := semireducible}.",
  success_if_fail_with_msg (simps_tac `foo.bar3)
    "Invalid `simps` attribute. The body is not a constructor application:
classical.choice bar3._proof_1
Possible solution: add option {rhs_md := semireducible}.",
  e ← get_env,
  let nm := `foo.bar1,
  d ← e.get nm,
  let lhs : expr := const d.to_name (d.univ_params.map level.param),
  simps_add_projections e nm "" d.type lhs d.value [] d.univ_params ff {} []


/- test `rhs_md` option -/
def rfl2 {α} : α ≃ α := foo.rfl

run_cmd success_if_fail (simps_tac `foo.rfl2)
attribute [simps {rhs_md := semireducible}] foo.rfl2

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

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[simps]
-- def very_partially_applied_term : very_partially_applied_str := ⟨@my_prod.mk ℕ⟩
def very_partially_applied_term : very_partially_applied_str := ⟨λ x y z, my_prod.mk y z⟩

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
@[simps] def specify5 : ℕ × ℕ × ℕ := (1, prod.map (λ x, x) (λ y, y) (2, 3))
end specify

run_cmd do
  e ← get_env,
  e.get `specify.specify1_fst, e.get `specify.specify2_snd,
  e.get `specify.specify3_snd_fst, e.get `specify.specify4_snd_snd, e.get `specify.specify4_snd,
  e.get `specify.specify5_fst, e.get `specify.specify5_snd,
  guard $ 12 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `specify then 1 else 0),
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["fst_fst"])
    "Invalid simp-lemma specify.specify1_fst_fst. Projection fst doesn't exist, because target is not a structure.",
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["foo_fst"])
    "Invalid simp-lemma specify.specify1_foo_fst. Projection foo doesn't exist.",
  success_if_fail_with_msg (simps_tac `specify.specify1 {} ["snd_bar"])
    "Invalid simp-lemma specify.specify1_snd_bar. Projection bar doesn't exist.",
  success_if_fail_with_msg (simps_tac `specify.specify5 {} ["snd_snd"])
    "Invalid simp-lemma specify.specify5_snd_snd. The given definition is not a constructor application:
prod.map (λ (x : ℕ), x) (λ (y : ℕ), y) (2, 3)
Possible solution: add option {rhs_md := semireducible}."


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

/- Tests with universe levels -/
universe variables v u
class has_hom (obj : Type u) : Type (max u (v+1)) :=
(hom : obj → obj → Type v)

infixr ` ⟶ `:10 := has_hom.hom -- type as \h

section prio
set_option default_priority 100
class category_struct (obj : Type u) extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))
end prio

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
@[simps] def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps {simp_rhs := tt}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

end manual_coercion

namespace failty_manual_coercion
variables {α β γ : Sort*}

structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)

local infix ` ≃ `:25 := failty_manual_coercion.equiv

/-- See Note [custom simps projection] -/
noncomputable def equiv.simps.inv_fun (e : α ≃ β) : β → α := classical.choice ⟨e.inv_fun⟩

run_cmd do e ← get_env, success_if_fail (simps_get_raw_projections e `faulty_manual_coercion.equiv)

end failty_manual_coercion

namespace manual_initialize
/- defining a manual coercion. This should be made more easily. -/

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

/- fail if you add an attribute with a parameter. -/
run_cmd success_if_fail $ simps_tac `foo.rfl { attrs := [`higher_order] }
