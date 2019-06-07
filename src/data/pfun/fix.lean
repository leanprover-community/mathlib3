import order.bounded_lattice
import order.complete_partial_order
import data.nat.up
import logic.basic
import data.stream.basic
import order.basic
import order.bounded_lattice

universes u v

local attribute [instance, priority 0] classical.prop_decidable
variables {α : Type*}

namespace fix

open lattice (has_bot order_bot) roption
open nat nat.up lattice.has_bot lattice.order_bot (bot_le)
open complete_partial_order (Sup)

variables {β : Type*} (f : (α → roption β) → (α → roption β))

def succ' (i : α → ℕ) (x : α) : ℕ := (i x).succ

def approx : stream $ α → roption β
| 0 := ⊥
| (nat.succ i) := f (approx i)

def fix_aux {p : ℕ → Prop} (i : nat.up p) (g : Π j : nat.up p, j < i → α → roption β) : α → roption β :=
f $ λ x : α,
assert (¬p (i.val)) $ λ h : ¬ p (i.val),
g (i.succ h) (nat.lt_succ_self _) x

def fix (x : α) : roption β :=
assert (∃ i, (approx f i x).dom) $ λ h,
well_founded.fix.{1} (nat.up.wf h) (fix_aux f) nat.up.zero x

lemma fix_def {x : α} (h' : ∃ i, (approx f i x).dom) :
  fix f x = approx f (nat.succ $ nat.up.find h') x :=
begin
  let p := λ (i : ℕ), (approx f i x).dom,
  have : p (up.find h') := up.p_find h',
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

variables {f} (hf : monotone f)

include hf

lemma approx_mono' {i : ℕ} : approx f i ≤ approx f (succ i) :=
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

lemma mem_fix (a : α) (b : β) : b ∈ fix f a ↔ ∃ i, b ∈ approx f i a :=
begin
  by_cases h₀ : ∃ (i : ℕ), (approx f i a).dom,
  { simp [fix_def f h₀],
    split; intro hh, exact ⟨_,hh⟩,
    have h₁ := p_find h₀,
    rw [dom_iff_mem] at h₁,
    cases h₁ with y h₁,
    replace h₁ := approx_mono' hf _ _ h₁,
    suffices : y = b, subst this, exact h₁,
    cases hh with i hh,
    revert h₁, generalize : (succ (find h₀)) = j, intro,
    wlog : i ≤ j := le_total i j using [i j b y,j i y b],
    replace hh := approx_mono hf case _ _ hh,
    apply roption.mem_unique h₁ hh },
  { simp [fix_def' f h₀],
    simp [dom_iff_mem] at h₀,
    intro, apply h₀ }
end

lemma max_fix (i : ℕ) : approx f i ≤ fix f :=
assume a b hh,
by { rw [mem_fix hf], exact ⟨_,hh⟩ }

lemma min_fix (x : α) : ∃ i, fix f x ≤ approx f i x :=
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

lemma approx_eq {i j : ℕ} {a : α} (hi : (approx f i a).dom) (hj : (approx f j a).dom) :
  approx f i a = approx f j a :=
begin
  simp [dom_iff_mem] at hi hj,
  cases hi with b hi, cases hj with b' hj,
  have : b' = b,
  { wlog hij : i ≤ j := le_total i j using [i j b b',j i b' b],
    apply mem_unique hj, apply approx_mono hf hij _ _ hi, },
  subst b',
  ext y, split; intro hy,
  rename hi hh, rename hj hi, rename hh hj,
  all_goals
  { have := mem_unique hy hj, subst this,
    exact hi }
end

noncomputable def approx_chain : chain (α → roption β) :=
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

namespace pi

open fix

variables {α} {β : Type*}
open lattice (order_bot) complete_partial_order

variables {f : (α → roption β) → α → roption β} (hf : monotone f)

include hf

open roption (hiding Sup) nat
open nat.up complete_partial_order

lemma fix_eq_Sup : fix f = Sup (approx_chain hf) :=
begin
  apply le_antisymm,
  { intro x, cases min_fix hf x with i hx,
    transitivity' approx f i.succ x,
    { transitivity', apply hx, apply approx_mono' hf },
    apply le_Sup _ _ _, dsimp [approx],
    rw chain.mem_map_iff,
    refine ⟨approx f i.succ,_,rfl⟩,
    apply approx_mem_approx_chain },
  { apply Sup_le _ _ _,
    simp [mem_map_iff,approx_chain,stream.mem_def],
    intros y x, revert y, simp, apply max_fix hf },
end

lemma fix_le {X : α → roption β} (hX : f X ≤ X) : fix f ≤ X :=
begin
  rw fix_eq_Sup hf,
  apply Sup_le _ _ _,
  simp [approx_chain,stream.mem_def,stream.nth],
  intros y i, revert y, simp,
  induction i, apply bot_le _,
  transitivity' f X, apply hf i_ih,
  apply hX
end

variables {hf} (hc : continuous f hf)
include hc

lemma fix_eq : fix f = f (fix f) :=
begin
  rw [fix_eq_Sup hf,hc],
  apply le_antisymm,
  { apply Sup_le_Sup_of_le _,
    intros x hx, existsi [f x,chain.mem_map _ hf _ hx],
    apply le_f_of_mem_approx _ hx },
  { apply Sup_le_Sup_of_le _,
    intros x hx, rw chain.mem_map_iff at hx,
    rcases hx with ⟨y,h₀,h₁⟩, refine ⟨x,_,le_refl _⟩,
    rw ← h₁, apply f_mem_approx_chain _ h₀ }
end

end pi

class has_fix (α : Type*) :=
(fix : (α → α) → α)

open has_fix complete_partial_order

class lawful_fix (α : Type*) [has_fix α] [complete_partial_order α] :=
(fix_eq : ∀ {f : α → α}, continuous' f → fix f = f (fix f))

namespace roption

def to_unit (f : α → α) (x : unit → α) (_ : unit) : α := f (x ())

instance : has_fix (roption α) :=
⟨ λ f, fix.fix (to_unit f) () ⟩

def to_unit_mono (f : roption α → roption α) (hm : monotone f) : monotone (to_unit f) :=
λ x y h a, hm $ by exact h ()

def to_unit_cont (f : roption α → roption α) : Π hc : continuous' f, continuous (to_unit f) (to_unit_mono f hc.fst)
| ⟨hm,hc⟩ := by { intro c, ext : 1, dsimp [to_unit,complete_partial_order.Sup], erw [hc _,chain.map_comp], refl }

noncomputable instance : lawful_fix (roption α) :=
⟨ λ f hc, by { dsimp [fix],
              conv { to_lhs, rw [pi.fix_eq (to_unit_cont f hc)] }, refl } ⟩

end roption

namespace pi

instance roption.has_fix {β} : has_fix (α → roption β) :=
⟨ fix.fix ⟩

noncomputable instance {β} : lawful_fix (α → roption β) :=
⟨ λ f hc, by { dsimp [fix], conv { to_lhs, rw [fix_eq hc.snd], } } ⟩

variables {β : α → Type*} {γ : Π a : α, β a → Type*}

def curry (f : Π x : sigma β, γ x.1 x.2) (x : α) (y : β x) : γ x y :=
f ⟨x,y⟩

def uncurry (f : Π x (y : β x), γ x y) (x : sigma β) : γ x.1 x.2 :=
f x.1 x.2

section monotone

variables (α β γ)

lemma monotone_curry [∀ x y, preorder $ γ x y] : monotone $ @curry α β γ :=
λ x y h a b, h ⟨a,b⟩

lemma monotone_uncurry [∀ x y, preorder $ γ x y] : monotone $ @uncurry α β γ :=
λ x y h a, h a.1 a.2

variables [∀ x y, complete_partial_order $ γ x y]
open chain
lemma continuous_curry : continuous curry (monotone_curry α β γ) :=
λ c, by { ext x y, dsimp [curry,Sup], rw [map_comp,map_comp], refl }
lemma continuous_uncurry : continuous uncurry $ monotone_uncurry α β γ :=
λ c, by { ext x y, dsimp [uncurry,Sup], rw [map_comp,map_comp], refl }

end monotone

instance [has_fix $ Π x : sigma β, γ x.1 x.2] : has_fix (Π x (y : β x), γ x y) :=
⟨ λ f, curry (fix $ uncurry ∘ f ∘ curry) ⟩

variables [∀ x y, complete_partial_order $ γ x y]

section curry

variables f : (Π x (y : β x), γ x y) → (Π x (y : β x), γ x y)
variables {f} (hm : monotone f)
include hm

lemma uncurry_mono : monotone $ uncurry ∘ f ∘ curry :=
monotone_comp (monotone_comp (monotone_curry α β γ) hm)
              (monotone_uncurry α β γ)

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
