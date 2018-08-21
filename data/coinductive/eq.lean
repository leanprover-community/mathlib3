
import .basic .ext

universes u₀ u₁ u₂
variables {ι : Type u₁}
variables {α : ι → Type u₀}
variables {β : Π i, α i → Type u₂}
variables {γ : Π i (a : α i), β i a → ι}

namespace cofix
open coinduction
open coinduction.approx
open coinduction.subtree
variables {β}

local prefix `♯`:0 := cast (by simp [*] <|> cc <|> solve_by_elim)

local attribute [instance, priority 0] classical.prop_decidable

lemma ext {i} (x y : cofix γ i)
  (H : ∀ {j} (ps : path β) {x' y' : α j},
             (select ps x x') →
             (select ps y y') →
                         x' = y')
: x = y :=
begin
  cases x, cases y,
  congr, funext i,
  induction i with i,
  { cases x_approx 0, cases y_approx 0, refl },
  { apply ext_aux, apply_assumption,
    rw i_ih, apply_assumption,
    introv h₀ h₁ H',
    simp [select_eq_select] at H,
    -- cases H',
    subst i,
    apply H ps; assumption, }
end

section bisim
  variable (R : Π {i j : ι}, cofix γ i → cofix γ j → Prop)
  local infix ~ := R

  def is_bisimulation :=
      ∀ {i j} {s₁ : cofix γ i} {s₂ : cofix γ j},
        s₁ ~ s₂ →
        i = j →
        head s₁ == head s₂ ∧
        (∀ i j : _, i == j → children s₁ i ~ children s₂ j)

  theorem nth_of_bisim (bisim : is_bisimulation @R) :
     ∀ {i₀ i₁ j₀ j₁} (s₁ : cofix γ i₀) (s₂ : cofix γ i₁)
       (x₁ : cofix γ j₀) (x₂ : cofix γ j₁) (ps : path β),
       subtree ps s₁ x₁ →
       subtree ps s₂ x₂ →
       s₁ ~ s₂ →
         i₀ = i₁ →
         head x₁ == head x₂ ∧
         ∀ i j, i == j →
                children x₁ i ~ children x₂ j :=
  begin
    introv H₀ H₁ Hr Hij,
    -- revert s₁ s₂,
    have h₁ := (bisim Hr Hij).1,
    have h₂ := (bisim Hr Hij).2,
    induction ps generalizing i₀ i₁ s₁ s₂,
    { cases H₀, cases H₁,
      split, subst_all, assumption,
      assumption },
    { cases H₀, cases H₁,
      subst s₁, subst s₂,
      simp at h₂,
      have Hr' := (h₂ H₀_x _ rfl) ,
      have := (bisim Hr' rfl).1,
      apply ps_ih _ _ H₀_a_2 H₁_a_2 Hr' rfl this,
      intros,
      apply (bisim Hr' rfl).2,
      assumption },
  end

  theorem eq_of_bisim (bisim : is_bisimulation @R) :
    ∀ {i} {s₁ s₂ : cofix γ i}, s₁ ~ s₂ → s₁ = s₂ :=
  begin
    introv Hr, apply ext,
    introv Hs₁ Hs₂,
    cases exists_subtree _ _ _ Hs₁ with ch_x hx,
    cases exists_subtree _ _ _ Hs₂ with ch_y hy ,
    have H := (nth_of_bisim @R @bisim _ _ _ _ ps hx hy Hr rfl).1,
    simp at H, assumption,
  end
end bisim

section coinduction

variables γ β

inductive rel_head : Type (max u₀ u₁ u₂)
 | intro {i : ι} (x : α i) (ch₀ ch₁ : Π b : β i x, cofix γ (γ i x b)) : rel_head

def rel_branch : rel_head β γ → Type*
 | (rel_head.intro x _ _) := β _ x

structure sim_rel : Type (max u₀ u₁ u₂) :=
  (rel : Π {i j}, cofix γ i → cofix γ j → Prop)
  -- (head_rel : α → α → Prop)
  (refl : ∀ i, reflexive $ @rel i i)
  -- (head_refl : reflexive head_rel)
  -- (head_eq : ∀ x y, rel x y → head_rel (head x) (head y))
  (backwards : ∀ i x
    (ch₀ : Π b : β i x, cofix γ (γ _ _ b))
    (ch₁ : Π b : β _ x, cofix γ (γ _ _ b)),
    (∀ i, rel (ch₀ i) (ch₁ i)) →
    rel (cofix.mk x ch₀) (cofix.mk x ch₁))

instance : has_coe_to_fun (sim_rel β γ) :=
{ F := λ r, Π {i j}, cofix γ i → cofix γ j → Prop
, coe := λ r {i j}, @sim_rel.rel _ _ _ _ r i j }

def R {i j} (s₁ : cofix γ i) (s₂ : cofix γ j) :=
   head s₁ == head s₂ ∧
            ∀ (FR : sim_rel β γ),
              FR s₁ s₂ →
            ∀ i j, i == j →
                FR (children s₁ i) (children s₂ j)

open ulift
lemma R_is_bisimulation : is_bisimulation (@R _ _ β γ ) :=
begin
  simp [is_bisimulation,R],
  introv H_head H_coind, intro,
  split, assumption,
  introv Hij,
  split,
  { apply H_coind { rel := λ i j x y, head x == head y, .. };
     simp [reflexive] <|> assumption, intros, trivial, },
  { intros,
    let FR' : sim_rel β γ,
    { clear_except FR,
      refine
      { rel := λ i j x y,
        FR x y ↔
        head x == head y ∧
        ∀ i j, i == j → FR (children x i) (children y j), .. },
      { simp [reflexive], -- intros, existsi FR.refl x,
        intros, split ; intros ; try { subst j } ; apply FR.refl },
      {
        introv Hsim, -- Hfr Hij,
        split ; intro h', dsimp, simp,
        { introv _, subst j, rw Hsim, split, admit, admit },
        -- specialize Hsim _ _ Hij,
        admit } },
    admit }
    -- apply H_coind FR' ; try { assumption },
    -- -- { simp [FR',reflexive], intros, subst i_2, solve_by_elim, },
    -- { unfold_coes, simp [FR'], intros, apply H_coind ; assumption, }, },
end

variables {β}

#check R_is_bisimulation β γ

lemma coinduction {i} (s₁ s₂ : cofix γ i)
  (hh : head s₁ = head s₂)
  (ht : ∀ (FR : Π {i j}, cofix γ i → cofix γ j → Prop),
          (∀ i, reflexive (@FR i i)) →
          FR s₁ s₂ →
          ∀ i j, i == j →
                 FR (children s₁ i) (children s₂ j))
: s₁ = s₂ :=
eq_of_bisim
  (@R _ _ β γ) (@R_is_bisimulation _ _ β γ)
  (and.intro (heq_of_eq hh) $
   begin
     intros, specialize ht @FR,
     apply ht FR.refl; assumption,
   end)

end coinduction

#check @cofix.corec
#check γ
def iterate {i} (x : α i) (f : Π (j : ι) (y : α j), Π (a : β j y), α (γ j y a)) : cofix γ i :=
cofix.corec γ (λ j y, ⟨ y, f _ y ⟩ ) x

universes u' v'

def map {ι'}
  {α' : ι' → Type u'} {β' : Π i, α' i → Type v'}
  {γ' : Π (i : ι') (a : α' i), β' i a → ι'}
  (h : ι' → ι)
  (f : Π i, α (h i) → α' i)
  (g : Π i x, β' i (f _ x) → β (h i) x)
  (H : Π i (t : cofix γ (h i)) a, cofix γ (γ (h i) (head t) (g i (head t) a)) → (cofix γ ∘ h) (γ' i (f i (head t)) a))
  {i} (x : cofix γ (h i)) : cofix γ' i :=
-- cofix.corec (λ j t, ⟨ head t, _ ⟩ : Π i, cofix γ' i → Σ y : α' i, Π a : β' i y, cofix γ (γ (h i) _ (g _ _ a))) x
@cofix.corec ι' α' β' γ' (cofix γ ∘ h) (λ i t, ⟨ f _ (head t), λ a, H _ _ _ (children t (g _ _ a)) ⟩) i x

-- def map'
--   -- {α' : ι' → Type u'} {β' : Π i, α' i → Type v'}
--   (h : ι → ι)
--   (f : Π i, α (h i) → α i)
--   (g : Π i x, β i (f _ x) → β (h i) x)
--   {i} (x : cofix γ $ h i) : cofix γ i :=
-- @cofix.corec ι α β γ (cofix γ ∘ h) (λ i t, ⟨ f _ $ head t, λ a,children t _⟩) _ x

#check @cofix.corec

def corec_on {i} {X : ι → Type*} (x₀ : X i) (f : Π i, X i → (Σ (y : α i), Π b : β i y, X (γ i y b))) : cofix γ i :=
cofix.corec _ f x₀

-- set_option pp.implicit true

theorem corec_eq  {X : ι → Type*} (f : Π i, X i → (Σ (y : α i), β i y → X (γ i y _))) {i} (x₀ : X i)
: cofix.corec γ f x₀ = cofix.mk (f _ x₀).1 (λ  i, cofix.corec γ f ((f _ x₀).2 i)) :=
begin
  cases Hf : f _ x₀, simp,
  apply coinduction,
  { simp [*], },
  { admit }
--   { intros, rw [children_mk,children_corec],
--     generalize Hi : cast _ i_1 = k,
--     have : k == j, cc, clear Hi a_2 ,
--     revert j k, rw Hf,
--     dsimp, intros, subst this,
--     suffices : (cofix.corec γ f ((sigma.mk fst snd).snd k)) = (cofix.corec γ f (snd k)),
--     { simp [this],
--       generalize h : snd k = d, dsimp,
--       h_generalize h : d == j, clear_except h,
--       -- revert j,
--       have : (head (cofix.corec γ f x₀)) = fst, admit,
--       subst fst, subst j,
-- generalize hh : (head (cofix.corec γ f x₀)) = z,
--       rw head_corec,
--       change FR (cofix.corec γ f (d)) (cofix.corec γ f d),
--       apply a,
--       revert k,
--       rw [head_corec],  },
--     congr, cc, }
end

theorem corec_eq' {X : ι → Type*}
  (f : Π i, X i → α i)
  (g : Π i (x : X i), β i (f i x) → X (γ i _ _)) {i} (x₀ : X i)
: cofix.corec γ (λ i x, ⟨f i x,g i x ⟩) x₀ =
  cofix.mk (f i x₀) (λ j, cofix.corec γ (λ i x, ⟨f i x,g i x⟩) (g _ _ _)) :=
corec_eq _ x₀

end cofix
