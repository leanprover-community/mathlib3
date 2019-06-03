import order.bounded_lattice
import order.chain_complete_partial_order
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
open chain_complete_partial_order (Sup)

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

end fix

namespace roption
open fix chain_complete_partial_order

variables {β : Type u} (f : (α → roption β) → α → roption β)

def approx₀ (i : α → ℕ) (x : α) : roption β :=
approx f (i x) x

variables {f} (hf : monotone f)
include hf

lemma min_fix₀ : ∃ i, fix f ≤ approx₀ f i :=
suffices ∀ a, ∃ i, fix f a ≤ approx f i a, from classical.skolem.mp this,
assume a,  min_fix hf _

end roption

namespace pi

open fix

variables {α} {β : Type*}
open lattice (order_bot) chain_complete_partial_order

-- instance : order_bot (α → roption β) :=
-- lattice.pi.order_bot

variables {f : (α → roption β) → α → roption β} (hf : monotone f)

include hf
set_option pp.implicit true

local attribute [priority 0]
  partial_order.to_preorder
  chain_complete_partial_order.to_partial_order
  roption.chain_complete_partial_order
  -- pi.chain_complete_partial_order

def approx_chain : chain (α → roption β) :=
begin
  refine ⟨ { x | x ∈ approx f }, _ ⟩,
  simp [stream.mem_def], intros x i hx y j hy,
  wlog h : i ≤ j := le_total i j using [i j x y,j i y x],
  left, subst x, subst y,
  apply approx_mono _ h,
  introv _ h x, apply hf h,
end

local attribute [instance] roption.chain_complete_partial_order

noncomputable def approx₁ (i : α → ℕ) : α → roption β :=
begin
  intro a,
  refine Sup ⟨ { y : roption β | ∃ a' : α, y ≤ approx f (i a') a }, _ ⟩,
  simp,
  intros y₀ x₀ hy₀ y₁ x₁ hy₁,
  wlog h : i x₀ ≤ i x₁ := le_total (i x₀) (i x₁)
    using [x₀ x₁ y₀ y₁,x₁ x₀ y₁ y₀],
  have h' := approx_mono hf h,
  apply roption.le_total_of_le_of_le (approx f (i x₁) a),
  { apply le_trans hy₀ (h' a) },
  { apply hy₁ },
end

noncomputable def approx₂ (i : α → ℕ) : α → roption β :=
begin
  refine Sup ⟨ { y : α → roption β | ∃ a' : α, y = approx f (i a') }, _ ⟩,
  simp,
  intros y₀ x₀ hy₀ y₁ x₁ hy₁,
  wlog h : i x₀ ≤ i x₁ := le_total (i x₀) (i x₁)
    using [x₀ x₁ y₀ y₁,x₁ x₀ y₁ y₀],
  subst y₀, subst y₁,
  left, apply approx_mono hf h,
end

lemma max_fix₁ (i : α → ℕ) : approx₁ hf i ≤ fix f :=
assume a b,
by { simp [approx₁], revert b, change _ ≤ (_ : roption β), apply Sup_le _ (fix f a) _,
     simp, intros y x hy, apply le_trans hy, apply max_fix hf }

lemma max_fix₂ (i : α → ℕ) : approx₂ hf i ≤ fix f :=
by { simp [approx₂], apply Sup_le _ (fix f) _,
     simp, intros y x hy, subst y, apply max_fix hf }

open roption (hiding Sup) nat

lemma approx_le_approx₁ (i) : approx₀ f i ≤ approx₁ hf i :=
begin
  intro a,
  rcases eq_none_or_eq_some (approx₀ f i a) with h | ⟨b,h⟩,
  { rw h, change ⊥ ≤ _, refine lattice.order_bot.bot_le _ },
  apply le_Sup _ _ _, simp [approx₀],
  exact ⟨_,le_refl _⟩
end

lemma min_fix₁ : ∃ i, fix f ≤ approx₁ hf i :=
begin
  suffices : ∃ (i : α → ℕ), fix f ≤ approx₀ f i,
  { revert this, apply exists_imp_exists, intros i h,
    transitivity', apply h, clear h, intro a,
    rcases eq_none_or_eq_some (approx₀ f i a) with h | ⟨b,h⟩,
    { rw h, change ⊥ ≤ _, refine lattice.order_bot.bot_le _ },
    apply le_Sup _ _ _, simp [approx₀],
    exact ⟨_,le_refl _⟩ },
  apply min_fix₀ hf
end

lemma approx₁_le_approx₂ (i) : approx₁ hf i ≤ approx₂ hf i :=
begin
  intro a,
  apply Sup_le_Sup_of_le _,
  apply le_chain_map, simp,
  intros b a hb,
  existsi [approx f (i a),hb],
  exact ⟨_,rfl⟩,
end

lemma min_fix₂ : ∃ i, fix f ≤ approx₂ hf i :=
begin
  cases min_fix₁ hf with i h, existsi i,
  transitivity', apply h, apply approx₁_le_approx₂,
end

open nat.up

protected lemma fix_spec : fix f = Sup (approx_chain hf) :=
begin
  ext : 1, dsimp [chain_complete_partial_order.Sup],
  let c := (@chain.map _ _ _ _ (approx_chain hf) (λ (f : α → roption β), f x) _),
  change _ = roption.Sup c,
  by_cases hh : ∃ a, roption.some a ∈ c,
  { cases hh with a ha, rw Sup_eq_some ha,
    simp [c,stream.mem_def,approx_chain] at ha,
    rcases ha with ⟨i,⟨j,ha⟩,ha'⟩, replace ha := ha.symm,
    simp [stream.nth] at ha,
    have : ∃ i, (approx f i x).dom,
    { simp [dom_iff_mem], simp [eq_some_iff] at ha',
      existsi [j,a], rw ha, exact ha', },
    rw fix_def f this, have hh := p_find this, rw dom_iff_mem at hh,
    replace ha' := eq.trans (congr_fun ha x) ha',
    rw ← ha', rw [eq_some_iff] at ha',
    have h' : (approx f (find this) x).dom := p_find this,
    replace h' : (approx f (succ $ find this) x).dom := _,
    apply approx_eq hf h' ha'.fst,
    revert h', rw [dom_iff_mem,dom_iff_mem],
    apply exists_imp_exists, apply approx_mono' hf },
  { rw Sup_eq_none hh,
    cases min_fix hf x, rw eq_none_iff,
    intros a ha, replace h := h _ ha,
    simp at hh, apply hh a,
    rw ← eq_some_iff at h,
    dsimp [c], rw ← h, apply mem_chain.map,
    exact ⟨w,rfl⟩, },
end

lemma bot_eq_Sup_empty : ⊥ = (Sup ∅ : α → roption β) :=
begin
  apply le_antisymm, refine lattice.bot_le,
  apply Sup_le _ _ _, intros, cases H
end

variables {hf} (hc : continuous f hf)
include hc

lemma f_approx₂ (i : α → ℕ) : f (approx₂ hf i) ≤ approx₂ hf (succ' i) :=
begin
  rw [approx₂,approx₂,hc _],
  apply Sup_le_Sup_of_le _,
  apply chain_map_le, simp [succ',approx],
  introv hx, rw hx, exact ⟨_,rfl⟩,
end

lemma fix_eq_lfp : fix f = lfp f hf :=
begin
  apply le_antisymm,
  { apply le_Sup _ _ _,
    rw pi.fix_spec hf, constructor,
    intros x hx, simp [approx_chain,stream.mem_def] at hx,
    cases hx with i hx, subst x, dsimp [stream.nth],
    induction i; simp [approx],
    { rw bot_eq_Sup_empty hf, constructor,
      rintro _ ⟨ ⟩ },
    { constructor, apply i_ih } },
  { apply @lfp_induction _ _ _ _ (λ p, p ≤ fix f) _ _; dsimp,
    { intros x hx,
      cases min_fix₂ hf with i hi,
      transitivity' f (approx₂ hf i),
      { apply hf, apply le_trans hx hi },
      { apply le_trans (f_approx₂ hc _) (max_fix₂ _ _) } },
    { intros c hc, dsimp [chain_complete_partial_order.Sup],
      apply Sup_le _ _ hc } }
end

end pi

class has_fix (α : Type*) :=
(fix : (α → α) → α)

open has_fix chain_complete_partial_order

class lawful_fix (α : Type*) [has_fix α] [chain_complete_partial_order α] :=
(fix_eq : ∀ {f : α → α} {hm : monotone f}, continuous f hm → fix f = f (fix f))

namespace roption

def to_unit (f : α → α) (x : unit → α) (_ : unit) : α := f (x ())

instance : has_fix (roption α) :=
⟨ λ f, fix.fix (to_unit f) () ⟩

local attribute [instance] roption.chain_complete_partial_order

def to_unit_mono (f : roption α → roption α) (hm : monotone f) : monotone (to_unit f) :=
λ x y h a, hm $ by exact h ()

def to_unit_cont (f : roption α → roption α) {hm : monotone f} (hc : continuous f hm) : continuous (to_unit f) (to_unit_mono f hm) :=
λ c, by { ext : 1, dsimp [to_unit,chain_complete_partial_order.Sup], erw [hc _,map_comp,map_comp], refl }

noncomputable instance : lawful_fix (roption α) :=
⟨ λ f hm hc, by { dsimp [fix], rw [pi.fix_eq_lfp (to_unit_cont f hc)],
                 conv { to_lhs, rw lfp_eq _ (to_unit_mono f hm), }, refl } ⟩

end roption

namespace pi

instance roption.has_fix {β} : has_fix (α → roption β) :=
⟨ fix.fix ⟩

local attribute [instance] roption.chain_complete_partial_order

noncomputable instance {β} : lawful_fix (α → roption β) :=
⟨ λ f hm hc, by { dsimp [fix], rw [fix_eq_lfp hc,← lfp_eq f hm] } ⟩

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

variables [∀ x y, chain_complete_partial_order $ γ x y]

lemma continuous_curry : continuous curry (monotone_curry α β γ) :=
λ c, by { ext x y, dsimp [curry,Sup], rw [map_comp,map_comp], refl }
lemma continuous_uncurry : continuous uncurry $ monotone_uncurry α β γ :=
λ c, by { ext x y, dsimp [uncurry,Sup], rw [map_comp,map_comp], refl }

end monotone

instance [has_fix $ Π x : sigma β, γ x.1 x.2] : has_fix (Π x (y : β x), γ x y) :=
⟨ λ f, curry (fix $ uncurry ∘ f ∘ curry) ⟩

variables [∀ x y, chain_complete_partial_order $ γ x y]

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
⟨ λ f hm hc, by {
  dsimp [fix], conv { to_lhs, rw [lawful_fix.fix_eq (uncurry_cont hc)] }, refl, } ⟩

end pi
