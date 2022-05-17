import tactic.congrm

variables {X : Type*} [has_add X] [has_mul X] (a b c d : X) (f : X → X)

def j₁ : unit → unit | _ := unit.star
def j₂ : unit → unit → unit | _ _ := unit.star
def w : unit := unit.star

example {A : Type*} (j₂ : A → A → A) (j₁ : A → A)
  (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f b) * (f b + (c + f d)) :=
begin
  congrm j₂ (j₁ (j₁ _)) (j₂ _ _),
  { exact H trivial },
  { exact H'' trivial },
  { exact H' trivial },
end

example {A : Type*} (j₂ : A → A → A) (j₁ : A → A) (w : A)
  (H : true → a = b) (H' : true → c + (f a) = c + (f d)) (H'' : true → f d = f b) :
  f (f a) * (f d + (c + f a)) = f (f a) * (f b + (c + f d)) :=
begin
  congrm j₂ (j₁ (j₁ w)) (j₂ _ _),
  { exact H'' trivial },
  { exact H' trivial },
end
