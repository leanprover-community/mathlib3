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

example {f g : ℕ → ℕ → ℕ} (h : f = g) : (λ i j, f i j) = (λ i j, g i j) :=
begin
  congrm λ i j, _,
  guard_target f i j = g i j,
  rw h,
end

example : true ∧ false ↔ (true ∧ true) ∧ false :=
begin
  congrm _₂ _ _,
  exact (true_and true).symm,
end

example {g : X → X} (H : a = b) (H' : c + f a = c + f d) (H'' : f d = f b) :
  f (g a) * (f d + (c + f a)) = f (g b) * (f b + (c + f d)) :=
begin
  congrm _₂ (f (_₁ _)) (_₂ _ _),
  { exact H },
  { exact H'' },
  { exact H' },
end

example {A B C D E : Type*} [has_add A] [has_mul C] {a1 a2 a3 : A} (b1 b2 : B) {c1 c2 c3 : C}
  (d1 d2 : D) (r : A → B → C → D → E)
  (a23 : a2 = a3) (b12 : b1 = b2) (c23 : c2 = c3) (d12 : d1 = d2) :
  r (a1 + a2) b1 (c1 * c2) d1 = r (a1 + a3) b2 (c1 * c3) d2 :=
by congrm _₄ (_₂ _ _) _ (_₂ _ _) _; assumption

example {A B C D : Type*} [has_add A] [has_mul C] {a1 a2 a3 : A} (b1 b2 : B) {c1 c2 c3 : C}
  (r : A → B → C → D)
  (a23 : a2 = a3) (b12 : b1 = b2) (c23 : c2 = c3) :
  r (a1 + a2) b1 (c1 * c2) = r (a1 + a3) b2 (c1 * c3) :=
by congrm _₃ (_₂ _ _) _ (_₂ _ _); assumption

example {A : Type*} (s : A → ℕ) {a1 a3 : ℕ} {a4 a5 : A} (a45 : a4 = a5) :
  (a1 + (s a4)) * a3 = (a1 + (s a5)) * a3 :=
begin
  congrm _₂ (_ + (_₁ _)) _,
  exact a45,
end

example {A B C : Type*} [has_add A] [has_mul B] {a1 a2 a3 : A} (b1 b2 b3 : B)
  (r : A → B → C) (a23 : a2 = a3) (b13 : b1 = b3) :
  r (a1 + a2) (b1 * b2) = r (a1 + a3) (b3 * b2) :=
by congrm _₂ (_₂ _ _) (_₂ _ _); assumption

example {A B C : Type*} (r : A → B) (s : B → C) (a b : A) (ab : a = b) :
  s (r a) = s (r b) :=
begin
  congrm _₁ (_₁ _),
  exact ab,
end

open tactic

example {A : Type} [has_add A] (a b c d e f : A) (r : A → A → A → A) (s : A → A)
  (bd : b = d) (af : a = f) (bc : b = c) (ae : a = e) :
  r b (a + s b) a = r d (f + s c) e :=
begin
  congrm _₃ _ (_ + (_₁ _)) _,
  exact bd,
  exact af,
  exact bc,
  exact ae,
end

example {A : Type} [has_add A] (a b c d : A) (r : A → A → A) (s : A → A) (bd : b = d) (bc : b = c) :
  r b (a + s b) = r d (a + s c) :=
begin
  congrm _₂ _ (_₂ _ (s _)),  exact bd, exact bc,
/-  any one of these alternatives to the line above proves the goal
  congrm _₂ _ (_₂ _ (_₁ _)), exact bd, exact bc,
  congrm _₂ _ (_ + (_₁ _)),  exact bd, exact bc,
  congrm _₂ _ (_ + (s _)),   exact bd, exact bc,
  congrm r _ (_₂ _ (s _)),   exact bd, exact bc,
  congrm r _ (_₂ _ (_₁ _)),  exact bd, exact bc,
  congrm r _ (_ + (s _)),    exact bd, exact bc,
  congrm r _ (_ + (_₁ _)),   exact bd, exact bc,
-/
end

example {W X Y Z : Type*} (w w' : W) (y y' : Y) (r : X → Y → Z) (s : W → X)
  (hw : w = w') (hy : y = y') :
  r (s w) y = r (s w') y' :=
by congrm _₂ (_₁ _) _; assumption

example {W X Y : Type*} (w w' : W) (y y' : Y) (r : X → Y → ℕ) (s : W → X)
  (hw : w = w') (hy : y = y') :
  (2 + 2) + r (s w) y = 2 * 2 + r (s w') y' :=
by congrm _₂ (_₂ _ _) (_₂ (_₁ _) _); assumption

example (h1 : 5 = 1) (h2 : 7 = 3) : nat.succ 5 + nat.pred 7 = nat.pred 3 * nat.succ 1 :=
begin
  congrm _₂ (_₁ _) (_₁ _);
 -- the main goal becomes `3.succ + 1.pred = 3.pred * 1.succ` and `refl` closes it!
  exact h1 <|> exact h2,
end

example {a b c d e f g h : ℕ} (ae : a = e) (bf : b = f) (cg : c = g)  (dh : d = h) :
  (a + b) * (c - d.succ) = (e + f) * (g - h.succ) :=
by congrm _₂ (_₂ _ _) (_₂ _ (_₁ _)); assumption
