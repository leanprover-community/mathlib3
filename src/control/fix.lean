

import data.nat.up
import data.stream.basic
import logic.basic
import order.basic
import order.bounded_lattice
import order.omega_complete_partial_order
import tactic.apply

universes u v

open_locale classical
variables {α : Type*} {β : α → Type*}

/-- `has_fix α` gives us a way to calculate the fixed point
of function of type `α → α`. -/
class has_fix (α : Type*) :=
(fix : (α → α) → α)

open omega_complete_partial_order

/--  -/
class lawful_fix (α : Type*) [has_fix α] [omega_complete_partial_order α] :=
(fix_eq : ∀ {f : α → α}, continuous' f → has_fix.fix f = f (has_fix.fix f))

namespace roption

variables (f : (Π a, roption $ β a) → (Π a, roption $ β a))

open roption nat nat.up

/-- series of successive, finite approximation of the fixed point of `f` -/
def fix.approx : stream $ Π a, roption $ β a
| 0 := ⊥
| (nat.succ i) := f (fix.approx i)

/-- loop body for finding the fixed point of `f` -/
def fix_aux {p : ℕ → Prop} (i : nat.up p) (g : Π j : nat.up p, j < i → Π a, roption $ β a) : Π a, roption $ β a :=
f $ λ x : α,
assert (¬p (i.val)) $ λ h : ¬ p (i.val),
g (i.succ h) (nat.lt_succ_self _) x

/-- fixed point of `f` -/
protected def fix (x : α) : roption $ β x :=
roption.assert (∃ i, (fix.approx f i x).dom) $ λ h,
well_founded.fix.{1} (nat.up.wf h) (fix_aux f) nat.up.zero x

protected lemma fix_def {x : α} (h' : ∃ i, (fix.approx f i x).dom) :
  roption.fix f x = fix.approx f (nat.succ $ nat.find h') x :=
begin
  let p := λ (i : ℕ), (fix.approx f i x).dom,
  have : p (nat.find h') := nat.find_spec h',
  generalize hk : nat.find h' = k,
  replace hk : nat.find h' = k + (@up.zero p).val := hk,
  rw hk at this,
  revert hk,
  dsimp [roption.fix], rw assert_pos h', revert this,
  generalize : up.zero = z, intros,
  suffices : ∀ x', well_founded.fix (fix._proof_1 f x h') (fix_aux f) z x' = fix.approx f (succ k) x',
    from this _,
  induction k generalizing z; intro,
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1, rw assert_neg, refl,
    rw nat.zero_add at this,
    simp *, exact this },
  { rw [fix.approx,well_founded.fix_eq,fix_aux],
    congr, ext : 1,
    have hh : ¬(fix.approx f (z.val) x).dom,
    { apply nat.find_min h',
      rw [hk,nat.succ_add,← nat.add_succ],
      apply nat.lt_of_succ_le,
      apply nat.le_add_left },
    rw succ_add_eq_succ_add at this hk,
    rw [assert_pos hh, k_ih (up.succ z hh) this hk] }
end

lemma fix_def' {x : α} (h' : ¬ ∃ i, (fix.approx f i x).dom) :
  roption.fix f x = none :=
by dsimp [roption.fix]; rw assert_neg h'

namespace fix

variables {f} (hf : monotone f)

include hf

lemma approx_mono' {i : ℕ} : fix.approx f i ≤ fix.approx f (succ i) :=
begin
  induction i, dsimp [approx], apply @bot_le _ _ (f ⊥),
  intro, apply hf, apply i_ih
end

lemma approx_mono {i j : ℕ} (hij : i ≤ j) : approx f i ≤ approx f j :=
begin
  induction j, cases hij, refine @le_refl _ _ _,
  cases hij, apply @le_refl _ _ _,
  apply @le_trans _ _ _ (approx f j_n) _ (j_ih hij_a),
  apply approx_mono' hf
end

lemma mem_fix (a : α) (b : β a) : b ∈ roption.fix f a ↔ ∃ i, b ∈ approx f i a :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i a).dom,
  { simp [roption.fix_def f h₀],
    split; intro hh, exact ⟨_,hh⟩,
    have h₁ := nat.find_spec h₀,
    rw [dom_iff_mem] at h₁,
    cases h₁ with y h₁,
    replace h₁ := approx_mono' hf _ _ h₁,
    suffices : y = b, subst this, exact h₁,
    cases hh with i hh,
    revert h₁, generalize : (succ (nat.find h₀)) = j, intro,
    wlog : i ≤ j := le_total i j using [i j b y,j i y b],
    replace hh := approx_mono hf case _ _ hh,
    apply roption.mem_unique h₁ hh },
  { simp [fix_def' f h₀],
    simp [dom_iff_mem] at h₀,
    intro, apply h₀ }
end

lemma max_fix (i : ℕ) : approx f i ≤ roption.fix f :=
assume a b hh,
by { rw [mem_fix hf], exact ⟨_,hh⟩ }

lemma min_fix (x : α) : ∃ i, roption.fix f x ≤ approx f i x :=
begin
  by_cases hh : ∃ i b, b ∈ approx f i x,
  { rcases hh with ⟨i,b,hb⟩, existsi i,
    intros b' h',
    have hb' := max_fix hf i _ _ hb,
    have hh := roption.mem_unique h' hb',
    subst hh, exact hb },
  { simp at hh, existsi 0,
    intros b' h', simp [mem_fix hf] at h',
    cases h' with i h',
    cases hh _ _ h' }
end

/-- series of approximations of `fix f` as a `chain` -/
noncomputable def approx_chain : chain (Π a, roption $ β a) :=
begin
  refine ⟨ approx f, _ ⟩,
  apply approx_mono, exact hf
end

lemma le_f_of_mem_approx {x} (hx : x ∈ approx_chain hf) : x ≤ f x :=
begin
  revert hx, simp [approx_chain,stream.mem_def],
  intros i hx, subst x,
  apply approx_mono' hf
end

lemma f_mem_approx_chain {x} (hx : x ∈ approx_chain hf) : f x ∈ approx_chain hf :=
begin
  revert hx, simp [approx_chain,stream.mem_def],
  intros i hx, subst hx, exact ⟨i.succ,rfl⟩
end

lemma approx_mem_approx_chain {i} : approx f i ∈ approx_chain hf :=
stream.mem_of_nth_eq rfl

end fix

open fix

variables {α f}
variables (hf : monotone f)

open omega_complete_partial_order

include hf

open roption (hiding ωSup) nat
open nat.up omega_complete_partial_order

lemma fix_eq_ωSup : roption.fix f = ωSup (approx_chain hf) :=
begin
  apply le_antisymm,
  { intro x, cases min_fix hf x with i hx,
    transitivity' approx f i.succ x,
    { transitivity', apply hx, apply approx_mono' hf },
    apply le_ωSup _ _ _, dsimp [approx],
    rw chain.mem_map_iff,
    refine ⟨approx f i.succ,_,rfl⟩,
    apply approx_mem_approx_chain },
  { apply ωSup_le _ _ _,
    simp [mem_map_iff,approx_chain,stream.mem_def],
    intros y x, revert y, simp, apply max_fix hf },
end

@[main_declaration]
lemma fix_le {X : Π a, roption $ β a} (hX : f X ≤ X) : roption.fix f ≤ X :=
begin
  rw fix_eq_ωSup hf,
  apply ωSup_le _ _ _,
  simp [approx_chain,stream.mem_def,stream.nth],
  intros y i, revert y, simp,
  induction i, dsimp [fix.approx], apply' bot_le,
  transitivity' f X, apply hf i_ih,
  apply hX
end

variables {hf} (hc : continuous f hf)
include hc

lemma fix_eq : roption.fix f = f (roption.fix f) :=
begin
  rw [fix_eq_ωSup hf,hc],
  apply le_antisymm,
  { apply ωSup_le_ωSup_of_le _,
    intros x hx, existsi [f x,chain.mem_map _ hf _ hx],
    apply le_f_of_mem_approx _ hx },
  { apply ωSup_le_ωSup_of_le _,
    intros x hx, rw chain.mem_map_iff at hx,
    rcases hx with ⟨y,h₀,h₁⟩, refine ⟨x,_,le_refl _⟩,
    rw ← h₁, apply f_mem_approx_chain _ h₀ }
end

end roption

namespace roption

/-- Convert a function from and to `α` to a function from and to `unit → α` -/
def to_unit (f : α → α) (x : unit → α) (u : unit) : α := f (x u)

instance : has_fix (roption α) :=
⟨ λ f, roption.fix (to_unit f) () ⟩

lemma to_unit_mono (f : roption α → roption α) (hm : monotone f) : monotone (to_unit f) :=
λ x y, assume h : x ≤ y,
show to_unit f x ≤ to_unit f y,
  from λ u, hm $ h u

lemma to_unit_cont (f : roption α → roption α) : Π hc : continuous' f, continuous (to_unit f) (to_unit_mono f hc.fst)
| ⟨hm,hc⟩ := by { intro c, ext : 1, dsimp [to_unit,omega_complete_partial_order.ωSup], erw [hc _,chain.map_comp], refl }

@[main_declaration]
noncomputable instance : lawful_fix (roption α) :=
⟨ λ f hc, by { dsimp [has_fix.fix],
              conv { to_lhs, rw [roption.fix_eq (to_unit_cont f hc)] }, refl } ⟩

end roption

namespace pi

instance roption.has_fix {β} : has_fix (α → roption β) :=
⟨ roption.fix ⟩

noncomputable instance {β} : lawful_fix (α → roption β) :=
⟨ λ f hc, by { dsimp [has_fix.fix], conv { to_lhs, rw [roption.fix_eq hc.snd], } } ⟩

variables {γ : Π a : α, β a → Type*}

section monotone

variables (α β γ)

lemma monotone_curry [∀ x y, preorder $ γ x y] : monotone $ @curry α β γ :=
λ x y h a b, h ⟨a,b⟩

lemma monotone_uncurry [∀ x y, preorder $ γ x y] : monotone $ @uncurry α β γ :=
λ x y h a, h a.1 a.2

variables [∀ x y, omega_complete_partial_order $ γ x y]
open chain
lemma continuous_curry : continuous curry (monotone_curry α β γ) :=
λ c, by { ext x y, dsimp [curry,ωSup], rw [map_comp,map_comp], refl }
lemma continuous_uncurry : continuous uncurry $ monotone_uncurry α β γ :=
λ c, by { ext x y, dsimp [uncurry,ωSup], rw [map_comp,map_comp], refl }

end monotone

open has_fix

instance [has_fix $ Π x : sigma β, γ x.1 x.2] : has_fix (Π x (y : β x), γ x y) :=
⟨ λ f, curry (fix $ uncurry ∘ f ∘ curry) ⟩

variables [∀ x y, omega_complete_partial_order $ γ x y]

section curry

variables f : (Π x (y : β x), γ x y) → (Π x (y : β x), γ x y)
variables {f} (hm : monotone f)
include hm

lemma uncurry_mono : monotone $ uncurry ∘ f ∘ curry :=
monotone.comp (monotone_uncurry α β γ)
              (monotone.comp hm (monotone_curry α β γ))

variables {hm} (hc : continuous f hm)
include hc

lemma uncurry_cont : continuous (uncurry ∘ f ∘ curry) (uncurry_mono hm) :=
continuous_comp (f ∘ curry) _ uncurry _
  (continuous_comp curry _ f _ (continuous_curry _ _ _) hc)
  (continuous_uncurry _ _ _)

end curry

instance pi.lawful_fix' [has_fix $ Π x : sigma β, γ x.1 x.2] [lawful_fix $ Π x : sigma β, γ x.1 x.2] : lawful_fix (Π x y, γ x y) :=
⟨ λ f hc, by {
  dsimp [fix], conv { to_lhs, rw [lawful_fix.fix_eq ⟨_, uncurry_cont hc.snd⟩] }, refl, } ⟩

end pi
