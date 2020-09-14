
import data.finmap
import data.multiset.sort
import tactic.find_unused
import testing.slim_check.sampleable
import testing.slim_check.testable

universes u v w

namespace slim_check

/-- Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`with_default f y` encodes `x ↦ f x` when `x ∈ f` and `x ↦ y`
otherwise.
 -/
inductive total_function (α : Type u) (β : Type v) : Type (max u v)
| with_default : list (Σ _ : α, β) → β → total_function

instance total_function.inhabited {α β} [inhabited β] : inhabited (total_function α β) :=
⟨ total_function.with_default ∅ (default _) ⟩

namespace total_function

/-- Apply a total function to an argument. -/
def apply {α β : Type*} [decidable_eq α] : total_function α β → α → β
| (total_function.with_default m y) x := (m.lookup x).get_or_else y

/--
Implementation of `has_repr (total_function α β)`.

Creates a string for a given `finmap` and output, `x₀ ↦ y₀, .. xₙ ↦ yₙ`
for each of the entries. The brackets are provided by the calling function.
-/
def repr_aux {α : Type u} [has_repr α] {β : Type v} [has_repr β] (m : list (Σ _ : α, β)) : string :=
string.join $ list.qsort (λ x y, x < y) (m.map $ λ x, sformat!"{repr $ sigma.fst x} ↦ {repr $ sigma.snd x}, ")

/--
Produce a string for a given `total_function`.

For `with_default f y`, produce `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, _ ↦ y]`.

For `map_to_self f`, produce `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, x ↦ x]`.
-/
protected def repr {α : Type u} [has_repr α] {β : Type v} [has_repr β] : total_function α β → string
| (total_function.with_default m y) := sformat!"[{repr_aux m}_ ↦ {has_repr.repr y}]"

instance (α : Type u) (β : Type v) [has_repr α] [has_repr β] : has_repr (total_function α β) :=
⟨ total_function.repr ⟩

/-- Convert a product type to a Σ-type. -/
@[simp]
def prod.to_sigma {α β} : α × β → Σ _ : α, β
| ⟨x,y⟩ := ⟨x,y⟩

/-- Convert a product type to a Σ-type. -/
@[simp]
def sigma.to_prod {α β} : (Σ _ : α, β) → α × β
| ⟨x,y⟩ := ⟨x,y⟩

/-- Create a `finmap` from a list of pairs. -/
def list.to_finmap' {α β} [decidable_eq α] (xs : list (α × β)) : list (Σ _ : α, β) :=
xs.map prod.to_sigma

@[simp]
lemma prod.fst_to_sigma {α β} (x : α × β) : (prod.to_sigma x).fst = x.fst :=
by cases x; refl

instance ulift.has_repr {α} [has_repr α] : has_repr (ulift α) :=
⟨ λ ⟨x⟩, repr x ⟩

section

variables {α : Type u} {β : Type v} [sampleable α] [sampleable β]

def total.sizeof : total_function α β → ℕ
| ⟨m, x⟩ := 1 + @sizeof _ sampleable.wf m + sizeof x

@[priority 2000]
instance : has_sizeof (total_function α β) :=
⟨ total.sizeof ⟩

variables [decidable_eq α]

lemma sizeof_kerase {α β} [decidable_eq α] [has_sizeof (Σ _ : α, β)] (x : α) (xs : list (Σ _ : α, β)) :
  sizeof (list.kerase x xs) ≤ sizeof xs :=
begin
  unfold_wf,
  induction xs with y ys,
  { simp },
  { by_cases x = y.1; simp [*, list.sizeof] },
end

lemma sizeof_erase_dupkeys {α β} [decidable_eq α] [has_sizeof (Σ _ : α, β)] (xs : list (Σ _ : α, β)) :
  sizeof (list.erase_dupkeys xs) ≤ sizeof xs :=
begin
  unfold_wf,
  induction xs with x xs,
  { simp [list.erase_dupkeys] },
  { simp [list.erase_dupkeys_cons, list.sizeof],
    transitivity, apply sizeof_kerase,
    assumption }
end

protected def shrink : shrink_fn (total_function α β)
| ⟨m, x⟩ := (sampleable.shrink (m, x)).map $ λ ⟨⟨m', x'⟩, h⟩, ⟨⟨list.erase_dupkeys m', x'⟩,
            lt_of_le_of_lt (by unfold_wf; refine @sizeof_erase_dupkeys _ _ _ (@sampleable.wf _ _) _) h ⟩

variables
 [has_repr α] [has_repr β]

instance pi.sampleable_ext : sampleable_ext (α → β) :=
{ proxy_repr := total_function α β,
  interp := total_function.apply,
  sample := do {
    xs ← (sampleable.sample (list (α × β)) : gen ((list (α × β)))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{(max u v)} β)),
    pure $ total_function.with_default (list.to_finmap' xs) x },
  shrink := total_function.shrink }

end

section sampleable_ext
open sampleable_ext

@[priority 2000]
instance pi_pred.sampleable_ext {α : Type u} [sampleable_ext (α → bool)] : sampleable_ext.{u+1} (α → Prop) :=
{ proxy_repr := proxy_repr (α → bool),
  interp := λ m x, interp (α → bool) m x,
  sample := sample (α → bool),
  shrink := shrink }

@[priority 2000]
instance pi_uncurry.sampleable_ext {α : Type u} {β : Type v} {γ : Sort w} [sampleable_ext (α × β → γ)] : sampleable_ext.{(imax (u+1) (v+1) w)} (α → β → γ) :=
{ proxy_repr := proxy_repr (α × β → γ),
  interp := λ m x y, interp (α × β → γ) m (x, y),
  sample := sample (α × β → γ),
  shrink := shrink }

end sampleable_ext

end total_function

/--
Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`map_to_self f` encodes `x ↦ f x` when `x ∈ f` and `x ↦ x`,
i.e. `x` to itself, otherwise.
-/
inductive injective_function (α : Type u) : Type u
| map_to_self : list (Σ _ : α, α) → injective_function

namespace injective_function

/-- Apply a total function to an argument. -/
def apply {α : Type u} [decidable_eq α] : injective_function α → α → α
| (injective_function.map_to_self m) x := (m.lookup x).get_or_else x

protected def repr {α : Type u} [has_repr α] : injective_function α → string
| (injective_function.map_to_self m) := sformat!"[{total_function.repr_aux m}x ↦ x]"

instance (α : Type u) [has_repr α] : has_repr (injective_function α) :=
⟨ injective_function.repr ⟩

open total_function (prod.to_sigma sigma.to_prod)

/-- Interpret a list of pairs as a total function, defaulting to
the identity function when no entries are found for a given function -/
def list.apply_id {α : Type u} [decidable_eq α] (xs : list (α × α)) (x : α) : α :=
((xs.map prod.to_sigma).lookup x).get_or_else x

@[simp]
lemma list.apply_id_cons {α : Type u} [decidable_eq α] (xs : list (α × α)) (x y z : α) :
  list.apply_id ((y, z) :: xs) x = if y = x then z else list.apply_id xs x :=
by simp [list.apply_id, list.lookup]; split_ifs; refl

open function list prod
open nat

lemma nth_injective {α : Type u} {xs : list α} (i j : ℕ) (a : α)
  (h : nodup xs)
  (hi : xs.nth i = some a)
  (hj : xs.nth j = some a) : i = j :=
begin
  induction xs with x xs generalizing i j,
  { cases hj },
  { wlog : i ≤ j,
    cases h with _ _ h₀ h₁,
    cases j,
    { cases case, refl },
    cases i,
    { specialize h₀ a _,
      { injection hi, contradiction },
      { rw mem_iff_nth, exact ⟨_, hj⟩ } },
    { congr, apply xs_ih; assumption, } }
end

lemma foo {α : Type u} [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs.length = ys.length) (x y : α) (i : ℕ)
  (h₂ : xs.nth i = some x) :
  ys.nth i = some y ↔ list.apply_id.{u} (xs.zip ys) x = y :=
begin
  induction xs generalizing ys i,
  { cases h₂ },
  { cases i,
    injection h₂; subst h_1,
    cases ys,
    { cases h₁ },
    { simp [list.apply_id], },
    cases ys,
    { cases h₁ },
    { cases h₀,
      simp at h₂ ⊢, rw if_neg,
      apply xs_ih; solve_by_elim [succ.inj],
      apply h₀_a_1,
      apply nth_mem h₂ } }
end

lemma bar {α : Type u} {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs ~ ys) (i j : ℕ) :
  xs.nth i = xs.nth j ↔ ys.nth i = ys.nth j :=
begin
  revert xs ys,
  suffices : ∀ {xs ys : list α}, xs.nodup → xs ~ ys → (xs.nth i = xs.nth j → ys.nth i = ys.nth j),
  { intros,
    have h₂ : ys.nodup := h₁.nodup_iff.1 h₀,
    have h₃ := h₁.symm,
    split; apply this; assumption, },
  introv h₀ h₁ h₂,
  by_cases j < xs.length,
  { congr, rw nth_le_nth h at h₂,
    apply nth_injective _ _ _ h₀ h₂,
    rw nth_le_nth },
  { have h' : ¬j < ys.length, { rwa ← h₁.length_eq },
    rw nth_len_le (le_of_not_gt h) at h₂,
    rw nth_len_le (le_of_not_gt h'),
    rw nth_eq_none_iff at h₂ ⊢,
    rwa ← h₁.length_eq, }
end

lemma foo_bar {α : Type u} [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs ~ ys)
  (x : α) :
  x ∈ xs ↔ list.apply_id.{u} (xs.zip ys) x ∈ ys :=
begin
  simp [list.apply_id],
  cases h₃ : (lookup x (map prod.to_sigma (xs.zip ys))),
  { dsimp [option.get_or_else],
    rw h₁.mem_iff },
  { have h₂ : ys.nodup := h₁.nodup_iff.1 h₀,
    replace h₁ : xs.length = ys.length := h₁.length_eq,
    dsimp,
    induction xs with x' xs generalizing ys,
    { contradiction },
    { cases ys with y ys, cases h₃,
      dsimp [lookup] at h₃, split_ifs at h₃,
      { subst x', subst val, simp },
      { cases h₀ with _ _ h₀ h₅,
        cases h₂ with _ _ h₂ h₄,
        have h₆ := nat.succ.inj h₁,
        specialize @xs_ih h₅ ys h₃ h₄ h₆,
        simp [ne.symm h, xs_ih],
        suffices : val ∈ ys, tauto!,
        erw [← option.mem_def, mem_lookup_iff] at h₃,
        simp at h₃,
        rcases h₃ with ⟨a, b, h₃, h₄, h₅⟩,
        subst a, subst b,
        apply (mem_zip h₃).2,
        simp [nodupkeys, keys, (∘), map_fst_zip],
        rwa map_fst_zip _ _ (le_of_eq h₆) } } }
end

lemma bar_foo {α : Type u} [decidable_eq α] {xs ys : list α} (x : α) :
  x ∉ xs → list.apply_id.{u} (xs.zip ys) x = x :=
begin
  intro h,
  dsimp [list.apply_id],
  rw lookup_eq_none.2, refl,
  simp [keys],
  intros y hy,
  exact h (mem_zip hy).1,
end

lemma apply_id_injective {α : Type u} [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs) (h₁ : xs ~ ys) :
  injective.{u+1 u+1}
    (list.apply_id (xs.zip ys))
:=
begin
  intros x y h,
  by_cases hx : x ∈ xs;
    by_cases hy : y ∈ xs,
  { rw mem_iff_nth at hx hy,
    cases hx with i hx,
    cases hy with j hy,
    suffices : some x = some y,
    { injection this },
    have h₂ := h₁.length_eq,
    rw [← foo h₀ h₂ _ _ _ hx] at h,
    rw [← hx, ← hy, bar h₀ h₁, h],
    symmetry,
    rw foo; assumption, },
  { rw foo_bar h₀ h₁ at hx hy,
    rw h at hx,
    contradiction, },
  { rw foo_bar h₀ h₁ at hx hy,
    rw h at hx,
    contradiction, },
  { rwa [bar_foo, bar_foo] at h; assumption },
end

open total_function (list.to_finmap')

lemma interp_injective {α : Type u} [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs) (h₁ : xs ~ ys) :
  injective.{u+1 u+1}
    (apply (injective_function.map_to_self (list.to_finmap'.{u u} $ xs.zip ys))) :=
begin
  simp [list.to_finmap'],
  intros x y h,
  dsimp [apply] at h,
  replace h : list.apply_id.{u} (xs.zip ys) x = list.apply_id (xs.zip ys) y := h,
  refine (apply_id_injective h₀ h₁ h),
end

open sampleable

instance pi_injective.sampleable_ext : sampleable_ext { f : ℤ → ℤ // function.injective f } :=
{ proxy_repr := { f : injective_function ℤ // function.injective (apply f) },
  interp := subtype.map apply $ λ x h, h,
  sample := gen.sized $ λ sz, do {
    let xs' := int.range (-(2*sz+2)) (2*sz + 2),
    ys ← gen.permutation_of xs',
    let r : injective_function ℤ := injective_function.map_to_self (list.to_finmap' (xs'.zip ys.1)),
    have Hinj : injective (λ (r : ℕ), -(2*sz + 2 : ℤ) + ↑r), from λ x y h, int.coe_nat_inj (add_right_injective _ h),
    pure ⟨r, interp_injective (list.nodup_map Hinj (nodup_range _)) ys.2⟩ },
  shrink := λ _, lazy_list.nil }

end injective_function

open function

instance injective.testable {α β} (f : α → β)
  [I : testable (named_binder "x" $ ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ f x = f y → x = y)] :
  testable (injective f) := I

instance monotone.testable {α β} [preorder α] [preorder β] (f : α → β)
  [I : testable (named_binder "x" $ ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ x ≤ y → f x ≤ f y)] :
  testable (monotone f) := I

end slim_check
