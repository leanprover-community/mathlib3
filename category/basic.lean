/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends the theory on functors, applicatives and monads.
-/

universes u v w x y
variables {α β γ : Type u}

notation a ` $< `:1 f:1 := f a

section functor
variables {f : Type u → Type v} [functor f] [is_lawful_functor f]

run_cmd mk_simp_attr `functor_norm

@[functor_norm] theorem map_map (m : α → β) (g : β → γ) (x : f α) :
  g <$> (m <$> x) = (g ∘ m) <$> x :=
(comp_map _ _ _).symm

@[simp] theorem id_map' (x : f α) : (λa, a) <$> x = x := id_map _

end functor

section applicative
variables {f : Type u → Type v} [applicative f]

def mmap₂
  {α₁ α₂ φ : Type u}
  (g : α₁ → α₂ → f φ) :
  Π (ma₁ : list α₁) (ma₂: list α₂), f (list φ)
| (x :: xs) (y :: ys) := (::) <$> g x y <*> mmap₂ xs ys
| _ _ := pure []

def mmap₂'  (g : α → β → f γ) : list α → list β → f punit
| (x :: xs) (y :: ys) := g x y *> mmap₂' xs ys
| [] _ := pure punit.star
| _ [] := pure punit.star

variables [is_lawful_applicative f]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[simp] theorem pure_id'_seq (x : f α) : pure (λx, x) <*> x = x :=
pure_id_seq x

variables  [is_lawful_applicative f]

attribute [functor_norm] seq_assoc pure_seq_eq_map

@[functor_norm] theorem seq_map_assoc (x : f (α → β)) (g : γ → α) (y : f γ) :
  (x <*> (g <$> y)) = (λ(m:α→β), m ∘ g) <$> x <*> y :=
begin
  simp [(pure_seq_eq_map _ _).symm],
  simp [seq_assoc, (comp_map _ _ _).symm, (∘)],
  simp [pure_seq_eq_map]
end

@[functor_norm] theorem map_seq (g : β → γ) (x : f (α → β)) (y : f α) :
  (g <$> (x <*> y)) = ((∘) g) <$> x <*> y :=
by simp [(pure_seq_eq_map _ _).symm]; simp [seq_assoc]

end applicative

-- TODO: setup `functor_norm` for `monad` laws
section monad
variables {m : Type u → Type v} [monad m] [is_lawful_monad m]

lemma map_bind (x : m α) {g : α → m β} {f : β → γ} : f <$> (x >>= g) = (x >>= λa, f <$> g a) :=
by rw [← bind_pure_comp_eq_map,bind_assoc]; simp [bind_pure_comp_eq_map]

lemma seq_bind_eq (x : m α) {g : β → m γ} {f : α → β} : (f <$> x) >>= g = (x >>= g ∘ f) :=
show bind (f <$> x) g = bind x (g ∘ f),
by rw [← bind_pure_comp_eq_map, bind_assoc]; simp [pure_bind]

lemma seq_eq_bind_map {x : m α} {f : m (α → β)} : f <*> x = (f >>= (<$> x)) :=
(bind_map_eq_seq m f x).symm

end monad

section alternative
variables {f : Type → Type v} [alternative f]

@[simp] theorem guard_true {h : decidable true} :
  @guard f _ true h = pure () := by simp [guard]

@[simp] theorem guard_false {h : decidable false} :
  @guard f _ false h = failure := by simp [guard]

end alternative

class is_comm_applicative (m : Type* → Type*) [applicative m] extends is_lawful_applicative m : Prop :=
(commutative_prod : ∀{α β} (a : m α) (b : m β), prod.mk <$> a <*> b = (λb a, (a, b)) <$> b <*> a)

lemma is_comm_applicative.commutative_map
  {m : Type* → Type*} [applicative m] [is_comm_applicative m]
  {α β γ} (a : m α) (b : m β) {f : α → β → γ} :
  f <$> a <*> b = flip f <$> b <*> a :=
calc f <$> a <*> b = (λp:α×β, f p.1 p.2) <$> (prod.mk <$> a <*> b) :
    by simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
  ... = (λb a, f a b) <$> b <*> a :
    by rw [is_comm_applicative.commutative_prod];
        simp [seq_map_assoc, map_seq, seq_assoc, seq_pure, map_map]
