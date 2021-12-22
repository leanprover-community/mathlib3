import tactic

#print applicative

universes u v u' v'

open function



-- class applicative'' (f : Type u → Type v) extends functor f, has_pure f, has_seq f, has_seq_left f, has_seq_right f :=
-- (map       := λ _ _ x y, pure x <*> y)
-- (seq_left  := λ α β a b, (const β <$> a) <*> b)
-- (seq_right := λ α β a b, (const α id <$> a) <*> b)

-- variables (f : Type u → Type v) [functor f] [has_pure f] [has_seq f] [has_seq_left f] [has_seq_right f]

-- variables (α β : Type u) {a : f α} { b : f β}
-- #check const β
-- #check (const β <$> a)
-- include a b
-- example : true := begin
--   set x := ((const α id <$> a : f (β → β)) <*> b),
-- end


class is_monadic (α : out_param Type*) (fα : Type*) : Prop

instance {α : Type*} : is_monadic α (list α) := is_monadic.mk

class functor' {α β : out_param Type*} (fα fβ : Type*) [is_monadic α fα] [is_monadic β fβ] :=
(map : (α → β) → fα → fβ)
(map_const : β → fα → fβ := map ∘ function.const α)

instance {α β : Type*} : functor' (list α) (list β) :=
{ map := list.map }

infixr ` <$> `:100 := functor'.map
infixr ` <$ `:100  := functor'.map_const

@[reducible] def functor'.map_const_rev {α β : out_param Type*} (fα fβ : Type*)
  [is_monadic α fα] [is_monadic β fβ]
  [functor' fα fβ] : fα → β → fβ :=
λ a b, b <$ a
infixr ` $> `:100  := functor'.map_const_rev


class has_pure' {α : out_param Type*} (fα : Type*) [is_monadic α fα] :=
(pure : α → fα)

export has_pure' (pure)

class has_seq' {α β : out_param Type*} (fαβ : out_param Type*)
  (fα fβ : Type*) [is_monadic α fα] [is_monadic β fβ]
  [is_monadic (α → β) fαβ] :=
(seq  : fαβ → fα → fβ)

infixl ` <*> `:60 := has_seq'.seq

class has_seq_left' {α β : out_param Type*} (fα fβ : Type*) [is_monadic α fα] [is_monadic β fβ] :=
(seq_left : fβ → fα → fβ)

infixl ` <* `:60  := has_seq_left'.seq_left

class has_seq_right' {α β : out_param Type*} (fα fβ : Type*) [is_monadic α fα] [is_monadic β fβ] :=
(seq_right : fα → fβ → fβ)

infixl ` *> `:60  := has_seq_right'.seq_right

#print applicative.mk

class applicative' {α β : out_param Type*} (fαβ fββ : out_param Type*) (fα fβ : Type*) [is_monadic α fα] [is_monadic β fβ]
  [is_monadic (α → β) fαβ] [is_monadic (β → β) fββ]
  extends
  functor' fα fβ, has_pure' fαβ, has_seq' fαβ fα fβ, has_seq_left' fα fβ,
    has_seq_right' fα fβ :=
[to_functor₂ : functor' fβ fαβ]
[to_functor₃ : functor' fα fββ]
[to_has_seq₂ : has_seq' fββ fβ fβ]
(map       := λ x y, (pure x : fαβ) <*> y)
(seq_left  := λ b a, (const α <$> b : fαβ) <*> a)
(seq_right := λ a b, (const α id <$> a : fββ) <*> b)

instance {α β : Type*} : has_seq' (list (α → β)) (list α) (list β) :=
{ seq := λ f a, f.bind (λ g, a.map g) }

instance {α β : Type*} : applicative' (list (α → β)) (list (β → β)) (list α) (list β) :=
{ map := list.map,
  pure := list.ret }
