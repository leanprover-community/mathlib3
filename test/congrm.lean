import tactic.congrm

variables {X : Type*} [has_add X] [has_mul X] (a b c d : X) (f : X → X)

example (H : a = b) : f a + f a = f b + f b :=
by congrm f _ + f _; exact H

example {g : X → X} (H : a = b) (H' : c + f a = c + f d) (H'' : f d = f b) :
  f (g a) * (f d + (c + f a)) = f (g b) * (f b + (c + f d)) :=
begin
  congrm f (g _) * (_ + _),
  { exact H },
  { exact H'' },
  { exact H' },
end

example (H' : c + (f a) = c + (f d)) (H'' : f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm f (f _) * (_ + _),
  { exact H'' },
  { exact H' },
end

example (H' : c + (f a) = c + (f d)) (H'' : f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm f (f _) * (_ + _),
  { exact H'' },
  { exact H' },
end

example {p q} [decidable p] [decidable q] (h : p ↔ q) :
  ite p 0 1 = ite q 0 1 :=
begin
  congrm ite _ 0 1,
  exact h,
end

example {a b : ℕ} (h : a = b) : (λ y : ℕ, ∀ z, a + a = z) = (λ x, ∀ z, b + a = z) :=
begin
  congrm λ x, ∀ w, _ + a = w,
  exact h,
end

example (h : 5 = 3) : (⟨5 + 1, dec_trivial⟩ : fin 10) = ⟨3 + 1, dec_trivial⟩ :=
begin
  congrm ⟨_ + 1, _⟩,
  exact h,
end

example : true ∧ false ↔ (true ∧ true) ∧ false :=
begin
  congrm _ ∧ _,
  exact (true_and true).symm,
end

variables {A : Type*} (w : A)

def j₁ : A → A | _ := w
def j₂ : A → A → A | _ _ := w
def w : A := w

example (H : a = b) (H' : c + (f a) = c + (f d)) (H'' : f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f b) * (f b + (c + f d)) :=
begin
  congrm_1 j₂ (j₁ (j₁ _)) (j₂ _ _),
  { exact H },
  { exact H'' },
  { exact H' },
end

example (H : a = b) (H' : c + (f a) = c + (f d)) (H'' : f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm_1 j₂ (j₁ (j₁ w)) (j₂ _ _),
  { exact H'' },
  { exact H' },
end

example (H : a = b) (H' : c + (f a) = c + (f d)) (H'' : d = b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm_1 j₂ (j₁ (j₁ w)) (j₂ (j₁ _) _),
  { exact H'' },
  { exact H' },
end

example (h1 : 5 = 3) (h2 : 7 = 1) : nat.succ 5 + nat.pred 7 = nat.pred 3 * nat.succ 1 :=
begin
  congrm_1 j₂ (j₁ _) (j₁ _);
 -- the main goal becomes `3.succ + 1.pred = 3.pred * 1.succ` and `refl` closes it!
  exact h1 <|> exact h2,
end
