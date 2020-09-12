
import data.finmap
import data.multiset.sort
import tactic.find_unused
import testing.slim_check.sampleable
import testing.slim_check.testable

universes u v w

namespace slim_check

/-- Data structure specifying a total function
using a partial function (`finmap`) and a default value
used when the input is not in the domain of the partial function.

`with_default f y` encodes `x ↦ f x` when `x ∈ f` and `x ↦ y`
otherwise.

`map_to_self f` encodes `x ↦ f x` when `x ∈ f` and `x ↦ x`,
i.e. `x` to itself, otherwise.
 -/
inductive total_function (α : Type u) : Type u → Type (u+1)
| with_default {β} : finmap (λ _ : α, β) → β → total_function β
| map_to_self : finmap (λ _ : α, α) → total_function α

instance total_function.inhabited {α β} [inhabited β] : inhabited (total_function α β) :=
⟨ total_function.with_default ∅ (default _) ⟩

namespace total_function

/-- Apply a total function to an argument. -/
def apply {α : Type u} [decidable_eq α] : Π {β : Type u}, total_function α β → α → β
| β (total_function.with_default m y) x := (m.lookup x).get_or_else y
| β (total_function.map_to_self m) x := (m.lookup x).get_or_else x

/--
Implementation of `has_repr (total_function α β)`.

Creates a string for a given `finmap` and output, `x₀ ↦ y₀, .. xₙ ↦ yₙ`
for each of the entries. The brackets are provided by the calling function.
-/
def repr_aux {α : Type u} [has_repr α] {β : Type u} [has_repr β] (m : finmap (λ _ : α, β)) : string :=
string.join $ multiset.sort (≤) (m.entries.map $ λ x, sformat!"{repr $ sigma.fst x} ↦ {repr $ sigma.snd x}, ")

/--
Produce a string for a given `total_function`.

For `with_default f y`, produce `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, _ ↦ y]`.

For `map_to_self f`, produce `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, x ↦ x]`.
-/
protected def repr {α : Type u} [has_repr α] : Π {β : Type u} [has_repr β], total_function α β → string
| β Iβ (total_function.with_default m y) := sformat!"[{@repr_aux _ _ _ Iβ m}_ ↦ {@has_repr.repr _ Iβ y}]"
| _ _ (total_function.map_to_self m) := sformat!"[{repr_aux m}x ↦ x]"

instance (α : Type u) (β : Type u) [has_repr α] [has_repr β] : has_repr (total_function α β) :=
⟨ total_function.repr ⟩

/-- Convert a product type to a Σ-type. -/
@[simp]
def prod.to_sigma {α β} : α × β → Σ _ : α, β
| ⟨x,y⟩ := ⟨x,y⟩

/-- Create a `finmap` from a list of pairs. -/
def list.to_finmap' {α β} [decidable_eq α] (xs : list (α × β)) : finmap (λ _ : ulift α, ulift β) :=
(xs.map $ prod.to_sigma ∘ prod.map ulift.up ulift.up).to_finmap

@[simp]
lemma prod.fst_to_sigma {α β} (x : α × β) : (prod.to_sigma x).fst = x.fst :=
by cases x; refl

/-- Print out the representation of a function. -/
@[reducible]
protected def proxy_repr (α : Type u) (β : Type v) :=
total_function (ulift.{max u v} α) (ulift.{max v u} β)

/-- Interpret a `total_function` as a pi-typed function. -/
protected def interp (α : Type u) (β : Type v) [decidable_eq α] (m : total_function.proxy_repr α β) (x : α) : β :=
ulift.down $ total_function.apply m (ulift.up x)

instance ulift.has_repr {α} [has_repr α] : has_repr (ulift α) :=
⟨ λ ⟨x⟩, repr x ⟩

instance pi.sampleable_ext {α : Type u} {β : Type v} [has_repr α] [has_repr β] [sampleable α] [decidable_eq α] [sampleable β] : sampleable_ext (α → β) :=
{ proxy_repr := total_function (ulift.{max u v} α) (ulift.{max v u} β),
  interp := total_function.interp α β,
  sample := do {
    ⟨xs⟩ ← (uliftable.up $ sampleable.sample (list (α × β)) : gen (ulift.{(max u v)+1} (list (α × β)))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{(max u v)+1} β)),
    pure $ total_function.with_default (list.to_finmap' xs) ⟨x⟩ },
  shrink := λ _, lazy_list.nil }

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

lemma interp_injective {α : Type u} [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs) (h₁ : xs ~ ys) :
  injective.{u+1 u+1}
    (total_function.interp α α (total_function.map_to_self (list.to_finmap' $ xs.zip ys))) :=
begin
  simp [list.to_finmap'],
  rw [← map_map, ← zip_map],
  generalize hxs : (map ulift.up xs) = xs',
  generalize hys : (map ulift.up ys) = ys',
  intros x y h,
  dsimp [total_function.interp, apply] at h,
  replace h : list.apply_id.{u} (xs'.zip ys') ⟨x⟩ = list.apply_id (xs'.zip ys') ⟨y⟩,
  { dsimp [list.apply_id],
    simp at h, ext, exact h, },
  refine congr_arg ulift.down (apply_id_injective _ _ h),
  { subst xs', solve_by_elim [nodup_map, ulift.up.inj], },
  { rw [← hxs, ← hys], solve_by_elim [perm.map] }
end

open sampleable

instance pi_injective.sampleable_ext : sampleable_ext { f : ℤ → ℤ // function.injective f } :=
{ proxy_repr := { f : total_function (ulift ℤ) (ulift ℤ) // function.injective (total_function.interp ℤ ℤ f) },
  interp := subtype.map (total_function.interp ℤ ℤ) $ λ x h, h,
  sample := gen.sized $ λ sz, do {
    let xs' := int.range (-(2*sz+2)) (2*sz + 2)  in
    uliftable.adapt_up.{1} gen.{0} gen.{1}
      (gen.permutation_of xs') $ λ ys,
    let r : total_function (ulift.{0} ℤ) (ulift.{0} ℤ) := total_function.map_to_self (list.to_finmap' (xs'.zip ys.1)) in
    have Hinj : injective (λ (r : ℕ), -(2*sz + 2 : ℤ) + ↑r), from λ x y h, int.coe_nat_inj (add_right_injective _ h),
    pure ⟨r, interp_injective (list.nodup_map Hinj (nodup_range _)) ys.2⟩ },
  shrink := λ _, lazy_list.nil }

end total_function

open function

instance injective.testable {α β} (f : α → β)
  [I : testable (named_binder "x" $ ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ f x = f y → x = y)] :
  testable (injective f) := I

instance monotone.testable {α β} [preorder α] [preorder β] (f : α → β)
  [I : testable (named_binder "x" $ ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ x ≤ y → f x ≤ f y)] :
  testable (monotone f) := I

end slim_check
