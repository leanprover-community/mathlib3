
import data.nat.basic
import data.stream
import data.pfun
import data.erased
import order.basic
import order.bounded_lattice
import tactic.wlog

section nat_up

def nat.up (p : ℕ → Prop) : Type := { i : ℕ // (∀ j < i, ¬ p j) }

variable {p : ℕ → Prop}

def nat.up_lt (p) : nat.up p → nat.up p → Prop := λ x y, x.1 > y.1

instance : has_lt (nat.up p) :=
{ lt := λ x y, x.1 > y.1 }

def nat.up_wf : Exists p → well_founded (nat.up_lt p)
| ⟨x,h⟩ :=
have h : (<) = measure (λ y : nat.up p, x - y.val),
  by { ext, dsimp [measure,inv_image],
       rw nat.sub_lt_sub_left_iff, refl,
       by_contradiction h', revert h,
       apply x_1.property _ (lt_of_not_ge h'), },
cast (congr_arg _ h.symm) (measure_wf _)

def nat.up.zero : nat.up p := ⟨ 0, λ j h, false.elim (nat.not_lt_zero _ h) ⟩

def nat.up.succ (x : nat.up p) (h : ¬ p x.val) : nat.up p :=
⟨x.val.succ, by { intros j h', rw nat.lt_succ_iff_lt_or_eq at h',
                  cases h', apply x.property _ h', subst j, apply h } ⟩

end nat_up

section find

variables {p : ℕ → Prop} [decidable_pred p] (h : Exists p)

def find_aux : nat.up p → nat.up p :=
well_founded.fix (nat.up_wf h) $ λ x f,
if h : p x.val then x
  else f (x.succ h) $ nat.lt_succ_self _

def find : ℕ := (find_aux h nat.up.zero).val

lemma p_find : p (find h) :=
let P := (λ x : nat.up p, p (find_aux h x).val) in
suffices ∀ x, P x, from this _,
assume x,
well_founded.induction (nat.up_wf h) _ $ λ y ih,
by { dsimp [P], rw [find_aux,well_founded.fix_eq],
     by_cases h' : (p (y.val)); simp *,
     apply ih, apply nat.lt_succ_self, }

lemma find_least_solution (i : ℕ) (h' : i < find h) : ¬ p i :=
subtype.property (find_aux h nat.up.zero) _ h'

end find

namespace roption
open nat lattice

variables {α : Type*} {β : Type*} (f f₀ f₁ : (α → roption β) → α → roption β)


def roption.inf (x y : roption β) : roption β :=
⟨ ∃ h h', x.get h = y.get h' , λ h, x.get h.fst ⟩

instance : semilattice_inf_bot (roption β) :=
{ le := λ x y, ∀ i, i ∈ x → i ∈ y,
  le_refl := λ x y, id,
  le_trans := λ x y z f g i, g _ ∘ f _,
  le_antisymm := λ x y f g, roption.ext $ λ z, ⟨f _, g _⟩,
  bot := none,
  inf := roption.inf,
  le_inf := by { introv h₀ h₁ x h₂, replace h₀ := h₀ _ h₂, replace h₁ := h₁ _ h₂,
                 refine ⟨ ⟨h₀.fst,h₁.fst,_⟩, h₀.snd⟩, rw [h₀.snd,h₁.snd] },
  inf_le_left  := by { introv x h₀, existsi h₀.fst.fst, exact h₀.snd },
  inf_le_right := by { introv x h₀, existsi h₀.fst.snd.fst, rw ← h₀.fst.snd.snd, exact h₀.snd },
  bot_le := by { introv x, rintro ⟨⟨_⟩,_⟩, } }

def approx : stream $ α → roption β
| 0 := ⊥
| (succ i) := f (approx i)

local attribute [instance, priority 0] classical.prop_decidable

def fix_aux {p : ℕ → Prop} (i : nat.up p) (g : Π j : nat.up p, j < i → α → roption β) : α → roption β :=
f $ λ x,
assert (¬p (i.val)) $ λ h,
g (i.succ h) (nat.lt_succ_self _) x

def fix (x : α) : roption β :=
assert (∃ i, (approx f i x).dom) $ λ h,
well_founded.fix (nat.up_wf h) (fix_aux f) nat.up.zero x

def mono := ∀ ⦃a⦄ ⦃x y : α → roption β⦄, x a ≤ y a → f x a ≤ f y a

variables {f} (h : mono f)
include h

lemma approx_mono' {i : ℕ} : approx f i ≤ approx f (succ i) :=
begin
  induction i, apply @bot_le _ _ _,
  intro, apply h, apply i_ih
end

lemma approx_mono {i j : ℕ} (hij : i ≤ j) : approx f i ≤ approx f j :=
begin
  induction j, cases hij, apply @le_refl _ _ _,
  cases hij, apply @le_refl _ _ _,
  apply @le_trans _ _ _ (approx f j_n) _ (j_ih hij_a),
  apply approx_mono' h
end

lemma fix_def {x : α} (h' : ∃ i, (approx f i x).dom) :
  fix f x = approx f (succ $ find h') x :=
begin
  let p := λ (i : ℕ), (approx f i x).dom,
  have : p (find h') := p_find h',
  generalize hk : find h' = k,
  replace hk : find h' = k + (@up.zero p).val := hk,
  rw hk at this,
  revert hk,
  dsimp [fix], rw assert_pos h', revert this,
  generalize : up.zero = z, intros,
  suffices : ∀ x', well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x' = approx f (succ k) x',
    from this _,
  induction k generalizing z; intro,
  { rw [approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1, rw assert_neg, refl,
    rw nat.zero_add at this,
    simp *, exact this },
  { rw [approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1,
    have hh : ¬(approx f (z.val) x).dom,
    { apply find_least_solution h' z.val,
      rw [hk,nat.succ_add,← nat.add_succ],
      apply nat.lt_of_succ_le,
      apply nat.le_add_left },
    rw succ_add_eq_succ_add at this hk,
    rw [assert_pos hh, k_ih (up.succ z hh) this hk] }
end

lemma fix_def' {x : α} (h' : ¬ ∃ i, (approx f i x).dom) :
  fix f x = none :=
by dsimp [fix]; rw assert_neg h'

lemma mem_fix (x : α) (b : β) : b ∈ fix f x ↔ ∃ i, b ∈ approx f i x :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i x).dom,
  { simp [fix_def h h₀],
    split; intro hh, exact ⟨_,hh⟩,
    have h₁ := p_find h₀,
    rw [dom_iff_mem] at h₁,
    cases h₁ with y h₁,
    replace h₁ := approx_mono' h _ _ h₁,
    suffices : y = b, subst this, exact h₁,
    cases hh with i hh,
    revert h₁, generalize : (succ (find h₀)) = j, intro,
    wlog : i ≤ j := le_total i j using [i j b y,j i y b],
    replace hh := approx_mono h case _ _ hh,
    apply roption.mem_unique h₁ hh },
  { simp [fix_def' h h₀],
    simp [dom_iff_mem] at h₀,
    intro, apply h₀ }
end

lemma max_fix (i : ℕ) : approx f i ≤ fix f :=
assume a b hh,
by rw [mem_fix h]; exact ⟨_, hh⟩

lemma min_fix (a : α) : ∃ i, fix f a ≤ approx f i a :=
begin
  by_cases hh : ∃ i b, b ∈ approx f i a,
  { rcases hh with ⟨i,b,hb⟩, existsi i,
    intros b' h',
    have hb' := max_fix h i a _ hb,
    have hh := roption.mem_unique h' hb',
    subst hh, exact hb },
  { simp at hh, existsi 0,
    intros b' h', simp [mem_fix h] at h',
    cases h' with i h',
    cases hh _ _ h' }
end

lemma fix_interior  : fix f ≤ f (fix f) :=
begin
  intros a b,
  simp [mem_fix h],
  intro i, revert a b,
  change approx f i ≤ f (fix f),
  transitivity' f (approx f i),
  { apply approx_mono' h },
  { intro, apply h, apply max_fix h }
end

lemma fix_closure  : f (fix f) ≤ fix f :=
begin
  intro a,
  cases min_fix h a with i hi,
  transitivity' f (approx f i) a,
  { apply h hi },
  { apply max_fix h i.succ }
end

lemma fix_strongest {X : α → roption β} (h' : f X ≤ X) : fix f ≤ X :=
begin
  intro a,
  cases min_fix h a with i hh,
  transitivity', apply hh, clear hh,
  induction i, apply @bot_le _ _ _,
  transitivity' (f X a),
  { apply h i_ih },
  { apply h' }
end

lemma fix_eq : fix f = f (fix f) :=
le_antisymm (fix_interior h) (fix_closure h)

end roption

namespace roption.examples
open function

def div_intl (div : ℕ → ℕ → roption ℕ) : ℕ → ℕ → roption ℕ
| x y :=
if y ≤ x ∧ y > 0
  then div (x - y) y
  else pure x

def div : ℕ → ℕ → roption ℕ :=
curry $ roption.fix $ λ f, uncurry (div_intl $ curry f)

-- TODO(Simon): write `div` equation, prove monotonicity

inductive tree (α : Type*)
| nil {} : tree | node (x : α) : tree → tree → tree

open tree

def tree_map_intl {α β} (f : α → β) (tree_map : tree α → roption (tree β)) : tree α → roption (tree β)
| nil := pure nil
| (node x t₀ t₁) :=
do tt₀ ← tree_map t₀,
   tt₁ ← tree_map t₁,
   pure $ node (f x) tt₀ tt₁

def tree_map {α β} (f : α → β) : tree α → roption (tree β) :=
roption.fix $ tree_map_intl f

-- TODO(Simon): write `tree_map` equations, prove monotonicity
end roption.examples
