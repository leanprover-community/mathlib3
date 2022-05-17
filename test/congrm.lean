import tactic.congrm

variables {A X : Type*} (w : A) [has_add X] [has_mul X] (a b c d : X) (f : X → X)

def j₁ : A → A | _ := w
def j₂ : A → A → A | _ _ := w
def w : A := w

example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f b) * (f b + (c + f d)) :=
begin
  congrm_1 j₂ (j₁ (j₁ _)) (j₂ _ _),
  { exact H trivial },
  { exact H'' trivial },
  { exact H' trivial },
end

example (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm_1 j₂ (j₁ (j₁ w)) (j₂ _ _),
  { exact H'' trivial },
  { exact H' trivial },
end
