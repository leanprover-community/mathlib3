/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/

import tactic.interactive
import tactic.finish
import tactic.ext
import tactic.lift
import tactic.apply
import tactic.reassoc_axiom
import tactic.tfae
import tactic.elide
import tactic.ring_exp
import tactic.clear
import tactic.simp_rw

example (m n p q : nat) (h : m + n = p) : true :=
begin
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h,
    guard_hyp h' : m + n = x,
    guard_hyp h : x = p,
    guard_target m + n = q,
    admit },
  have : m + n = q,
  { generalize_hyp h' : m + n = x at h ⊢,
    guard_hyp h' : m + n = x,
    guard_hyp h : x = p,
    guard_target x = q,
    admit },
  trivial
end

example (α : Sort*) (L₁ L₂ L₃ : list α)
  (H : L₁ ++ L₂ = L₃) : true :=
begin
  have : L₁ ++ L₂ = L₂,
  { generalize_hyp h : L₁ ++ L₂ = L at H,
    induction L with hd tl ih,
    case list.nil
    { tactic.cleanup,
      change list.nil = L₃ at H,
      admit },
    case list.cons
    { change list.cons hd tl = L₃ at H,
      admit } },
  trivial
end

example (x y : ℕ) (p q : Prop) (h : x = y) (h' : p ↔ q) : true :=
begin
  symmetry' at h,
  guard_hyp' h : y = x,
  guard_hyp' h' : p ↔ q,
  symmetry' at *,
  guard_hyp' h : x = y,
  guard_hyp' h' : q ↔ p,
  trivial
end

section h_generalize

variables {α β γ φ ψ : Type} (f : α → α → α → φ → γ)
          (x y : α) (a b : β) (z : φ)
          (h₀ : β = α) (h₁ : β = α) (h₂ : φ = β)
          (hx : x == a) (hy : y == b) (hz : z == a)
include f x y z a b hx hy hz

example : f x y x z = f (eq.rec_on h₀ a) (cast h₀ b) (eq.mpr h₁.symm a) (eq.mpr h₂ a) :=
begin
  guard_hyp_nums 16,
  h_generalize hp : a == p with hh,
  guard_hyp_nums 19,
  guard_hyp' hh : β = α,
  guard_target f x y x z = f p (cast h₀ b) p (eq.mpr h₂ a),
  h_generalize hq : _ == q,
  guard_hyp_nums 21,
  guard_target f x y x z = f p q p (eq.mpr h₂ a),
  h_generalize _ : _ == r,
  guard_hyp_nums 23,
  guard_target f x y x z = f p q p r,
  casesm* [_ == _, _ = _], refl
end

end h_generalize

section h_generalize

variables {α β γ φ ψ : Type} (f : list α → list α → γ)
          (x : list α) (a : list β) (z : φ)
          (h₀ : β = α) (h₁ : list β = list α)
          (hx : x == a)
include f x z a hx h₀ h₁

example : true :=
begin
  have : f x x = f (eq.rec_on h₀ a) (cast h₁ a),
  { guard_hyp_nums 11,
    h_generalize : a == p with _,
    guard_hyp_nums 13,
    guard_hyp' h : β = α,
    guard_target f x x = f p (cast h₁ a),
    h_generalize! : a == q ,
    guard_hyp_nums 13,
    guard_target ∀ q, f x x = f p q,
    casesm* [_ == _, _ = _],
    success_if_fail { refl },
    admit },
  trivial
end

end h_generalize

section tfae

example (p q r s : Prop)
  (h₀ : p ↔ q)
  (h₁ : q ↔ r)
  (h₂ : r ↔ s) :
  p ↔ s :=
begin
  scc,
end

example (p' p q r r' s s' : Prop)
  (h₀ : p' → p)
  (h₀ : p → q)
  (h₁ : q → r)
  (h₁ : r' → r)
  (h₂ : r ↔ s)
  (h₂ : s → p)
  (h₂ : s → s') :
  p ↔ s :=
begin
  scc,
end

example (p' p q r r' s s' : Prop)
  (h₀ : p' → p)
  (h₀ : p → q)
  (h₁ : q → r)
  (h₁ : r' → r)
  (h₂ : r ↔ s)
  (h₂ : s → p)
  (h₂ : s → s') :
  p ↔ s :=
begin
  scc',
  assumption
end

example : tfae [true, ∀ n : ℕ, 0 ≤ n * n, true, true] := begin
  tfae_have : 3 → 1, { intro h, constructor },
  tfae_have : 2 → 3, { intro h, constructor },
  tfae_have : 2 ← 1, { intros h n, apply nat.zero_le },
  tfae_have : 4 ↔ 2, { tauto },
  tfae_finish,
end

example : tfae [] := begin
  tfae_finish,
end

variables P Q R : Prop

example (pq : P → Q) (qr : Q → R) (rp : R → P) : tfae [P, Q, R] :=
begin
  tfae_finish
end

example (pq : P ↔ Q) (qr : Q ↔ R) : tfae [P, Q, R] :=
begin
  tfae_finish -- the success or failure of this tactic is nondeterministic!
end

example (p : unit → Prop) : tfae [p (), p ()] :=
begin
  tfae_have : 1 ↔ 2, from iff.rfl,
  tfae_finish
end

end tfae

section clear_aux_decl

example (n m : ℕ) (h₁ : n = m) (h₂ : ∃ a : ℕ, a = n ∧ a = m) : 2 * m = 2 * n :=
let ⟨a, ha⟩ := h₂ in
begin
  clear_aux_decl, -- subst will fail without this line
  subst h₁
end

example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl, -- finish produces an error without this line
  finish
end

end clear_aux_decl

section swap

example {α₁ α₂ α₃ : Type} : true :=
by {have : α₁, have : α₂, have : α₃, swap, swap,
    rotate, rotate, rotate, rotate 2, rotate 2, triv, recover}

end swap

private meta def get_exception_message (t : lean.parser unit) : lean.parser string
| s := match t s with
       | result.success a s' := result.success "No exception" s
       | result.exception none pos s' := result.success "Exception no msg" s
       | result.exception (some msg) pos s' := result.success (msg ()).to_string s
       end

@[user_command] meta def test_parser1_fail_cmd
(_ : interactive.parse (lean.parser.tk "test_parser1")) : lean.parser unit :=
do
  let msg := "oh, no!",
  let t : lean.parser unit := tactic.fail msg,
  s ← get_exception_message t,
  if s = msg then tactic.skip
  else interaction_monad.fail "Message was corrupted while being passed through `lean.parser.of_tactic`"
.

-- Due to `lean.parser.of_tactic'` priority, the following *should not* fail with
-- a VM check error, and instead catch the error gracefully and just
-- run and succeed silently.
test_parser1

section category_theory
open category_theory
variables {C : Type} [category.{1} C]

example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  rw [h',reassoc_of h],
end

end category_theory

section is_eta_expansion
/- test the is_eta_expansion tactic -/
open function tactic
structure my_equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix ` my≃ `:25 := my_equiv

protected def my_rfl {α} : α my≃ α :=
⟨id, λ x, x, λ x, rfl, λ x, rfl⟩

def eta_expansion_test : ℕ × ℕ := ((1,0).1,(1,0).2)
run_cmd do e ← get_env, x ← e.get `eta_expansion_test,
  let v := (x.value.get_app_args).drop 2,
  let nms := [`prod.fst, `prod.snd],
  guard $ expr.is_eta_expansion_test (nms.zip v) = some `((1, 0))

def eta_expansion_test2 : ℕ my≃ ℕ :=
⟨my_rfl.to_fun, my_rfl.inv_fun, λ x, rfl, λ x, rfl⟩

run_cmd do e ← get_env, x ← e.get `eta_expansion_test2,
  let v := (x.value.get_app_args).drop 2,
  projs ← e.structure_fields_full `my_equiv,
  b ← expr.is_eta_expansion_aux x.value (projs.zip v),
  guard $ b = some `(@my_rfl ℕ)

run_cmd do e ← get_env, x1 ← e.get `eta_expansion_test, x2 ← e.get `eta_expansion_test2,
  b1 ← expr.is_eta_expansion x1.value,
  b2 ← expr.is_eta_expansion x2.value,
  guard $ b1 = some `((1, 0)) ∧ b2 = some `(@my_rfl ℕ)

structure my_str (n : ℕ) := (x y : ℕ)

def dummy : my_str 3 := ⟨1, 1⟩
def wrong_param : my_str 2 := ⟨dummy.1, dummy.2⟩
def right_param : my_str 3 := ⟨dummy.1, dummy.2⟩

run_cmd do e ← get_env,
  x ← e.get `wrong_param, o ← x.value.is_eta_expansion,
  guard o.is_none,
  x ← e.get `right_param, o ← x.value.is_eta_expansion,
  guard $ o = some `(dummy)


end is_eta_expansion

section elide

variables {x y z w : ℕ}
variables (h  : x + y + z ≤ w)
          (h' : x ≤ y + z + w)
include h h'

example : x + y + z ≤ w :=
begin
  elide 0 at h,
  elide 2 at h',
  guard_hyp h : @hidden _ (x + y + z ≤ w),
  guard_hyp h' : x ≤ @has_add.add (@hidden Type nat) (@hidden (has_add nat) nat.has_add)
                                   (@hidden ℕ (y + z)) (@hidden ℕ w),
  unelide at h,
  unelide at h',
  guard_hyp h' : x ≤ y + z + w,
  exact h, -- there was a universe problem in `elide`. `exact h` lets the kernel check
           -- the consistency of the universes
end

end elide

section struct_eq

@[ext]
structure foo (α : Type*) :=
(x y : ℕ)
(z : {z // z < x})
(k : α)
(h : x < y)

example {α : Type*} : Π (x y : foo α), x.x = y.x → x.y = y.y → x.z == y.z → x.k = y.k → x = y :=
foo.ext

example {α : Type*} : Π (x y : foo α), x = y ↔ x.x = y.x ∧ x.y = y.y ∧ x.z == y.z ∧ x.k = y.k :=
foo.ext_iff

example {α} (x y : foo α) (h : x = y) : y = x :=
begin
  ext,
  { guard_target' y.x = x.x, rw h },
  { guard_target' y.y = x.y, rw h },
  { guard_target' y.z == x.z, rw h },
  { guard_target' y.k = x.k, rw h },
end

end struct_eq

section ring_exp
  example (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) = (a^2 + 2 * a * b + b^2) * (a + b)^n := by ring_exp
end ring_exp

section clear'

example (a : ℕ) (b : fin a) : unit :=
begin
  success_if_fail { clear a b }, -- fails since `b` depends on `a`
  success_if_fail { clear' a },  -- fails since `b` depends on `a`
  clear' a b,
  guard_hyp_nums 0,
  exact ()
end

example (a : ℕ) : fin a → unit :=
begin
  success_if_fail { clear' a },          -- fails since the target depends on `a`
  success_if_fail { clear_dependent a }, -- ditto
  exact λ _, ()
end

example (a : unit) : unit :=
begin
  -- Check we fail with an error (but don't segfault) if hypotheses are repeated.
  success_if_fail { clear' a a },
  success_if_fail { clear_dependent a a },
  exact ()
end

example (a a a : unit) : unit :=
begin
  -- If there are multiple hypotheses with the same name,
  -- `clear'`/`clear_dependent` currently clears only the last.
  clear' a,
  clear_dependent a,
  guard_hyp_nums 1,
  exact ()
end

end clear'

section clear_dependent

example (a : ℕ) (b : fin a) : unit :=
begin
  success_if_fail { clear' a }, -- fails since `b` depends on `a`
  clear_dependent a,
  guard_hyp_nums 0,
  exact ()
end

end clear_dependent

section simp_rw
  example {α β : Type} {f : α → β} {t : set β} :
    (∀ s, f '' s ⊆ t) = ∀ s : set α, ∀ x ∈ s, x ∈ f ⁻¹' t :=
  by simp_rw [set.image_subset_iff, set.subset_def]
end simp_rw

section local_definitions
/- Some tactics about local definitions.
  Testing revert_deps, revert_after, generalize', clear_value. -/
open tactic
example {A : ℕ → Type} {n : ℕ} : let k := n + 3, l := k + n, f : A k → A k := id in
  ∀(x : A k) (y : A (n + k)) (z : A n) (h : k = n + n), unit :=
begin
  intros, guard_target unit,
  do { e ← get_local `k, e1 ← tactic.local_def_value e, e2 ← to_expr ```(n + 3), guard $ e1 = e2 },
  do { e ← get_local `n, success_if_fail_with_msg (tactic.local_def_value e)
    "Variable n is not a local definition." },
  do { success_if_fail_with_msg (tactic.local_def_value `(1 + 2))
    "No such hypothesis 1 + 2." },
  revert_deps k, tactic.intron 5, guard_target unit,
  revert_after n, tactic.intron 7, guard_target unit,
  do {
    e ← get_local `k,
    tactic.revert_reverse_dependencies_of_hyp e,
    l ← local_context,
    guard $ e ∈ l,
    intros },
  exact unit.star
end

example {A : ℕ → Type} {n : ℕ} : let k := n + 3, l := k + n, f : A k → A (n+3) := id in
  ∀(x : A k) (y : A (n + k)) (z : A n) (h : k = n + n), unit :=
begin
  intros,
  success_if_fail_with_msg {generalize : n + k = x}
    "generalize tactic failed, failed to find expression in the target",
  generalize' : n + k = x,
  generalize' h : n + k = y,
  exact unit.star
end

example {A : ℕ → Type} {n : ℕ} : let k := n + 3, l := k + n, f : A k → A (n+3) := id in
  ∀(x : A k) (y : A (n + k)) (z : A n) (h : k = n + n), unit :=
begin
  intros,
  tactic.to_expr ```(n + n) >>= λ e, tactic.generalize' e `xxx,
  success_if_fail_with_msg {clear_value n}
    "Cannot clear the body of n. It is not a local definition.",
  success_if_fail_with_msg {clear_value k}
    "Cannot clear the body of k. The resulting goal is not type correct.",
  clear_value k f,
  get_local `k, -- test that `k` is not renamed.
  exact unit.star
end

example {A : ℕ → Type} {n : ℕ} : let k := n + 3, l := k + n, f : A k → A k := id in
  ∀(x : A k) (y : A (n + k)) (z : A n) (h : k = n + n), unit :=
begin
  intros,
  clear_value k f,
  exact unit.star
end

/-- test `clear_value` and the preservation of naming -/
example : ∀ x y : ℤ, let z := x + y in x = z - y → x = y - z → true :=
begin
  introv h h,
  guard_hyp x : ℤ,
  guard_hyp y : ℤ,
  guard_hyp z : ℤ := x + y,
  guard_hyp h : x = y - z,
  suffices : true, -- test the type of the second assumption named `h`
  { clear h,
    guard_hyp h : x = z - y,
    assumption },
  do { to_expr ```(z) >>= is_local_def },
  clear_value z,
  guard_hyp z : ℤ,
  success_if_fail { do { to_expr ```(z) >>= is_local_def } },
  guard_hyp h : x = y - z,
  suffices : true,
  { clear h,
    guard_hyp h : x = z - y,
    assumption },
  trivial
end

/- Test whether generalize' always uses the exact name stated by the user, even if that name already
  exists. -/
example (n : Type) (k : ℕ) : k = 5 → unit :=
begin
  generalize' : 5 = n,
  guard_target (k = n → unit),
  intro, constructor
end

/- Test that `generalize'` works correctly with argument `h`, when the expression occurs in the
  target -/
example (n : Type) (k : ℕ) : k = 5 → unit :=
begin
  generalize' h : 5 = n,
  guard_target (k = n → unit),
  intro, constructor
end

end local_definitions

section set_attribute

open tactic

@[user_attribute] meta def my_user_attribute : user_attribute unit bool :=
{ name := `my_attr,
  descr := "",
  parser := return ff }

run_cmd do nm ← get_user_attribute_name `library_note, guard $ nm = `library_note_attr
run_cmd do nm ← get_user_attribute_name `higher_order, guard $ nm = `tactic.higher_order_attr
run_cmd do success_if_fail $ get_user_attribute_name `zxy.xzy

run_cmd set_attribute `norm `prod.map tt
run_cmd set_attribute `my_attr `prod.map
run_cmd set_attribute `to_additive `has_mul
run_cmd success_if_fail $ set_attribute `higher_order `prod.map tt
run_cmd success_if_fail $ set_attribute `norm `xyz.zxy
run_cmd success_if_fail $ set_attribute `zxy.xyz `prod.map

end set_attribute
