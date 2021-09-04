/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

The writer monad transformer for passing immutable state.
-/
import control.monad.basic
import algebra.group.basic

universes u v w u₀ u₁ v₀ v₁

structure writer_t (ω : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
(run : m (α × ω))

@[reducible] def writer (ω : Type u) := writer_t ω id

attribute [pp_using_anonymous_constructor] writer_t

namespace writer_t
section
  variable  {ω : Type u}
  variable  {m : Type u → Type v}
  variable  [monad m]
  variables {α β : Type u}
  open function

  @[ext]
  protected lemma ext (x x' : writer_t ω m α)
    (h : x.run = x'.run) :
    x = x' := by cases x; cases x'; congr; apply h

  @[inline] protected def tell (w : ω) : writer_t ω m punit :=
  ⟨pure (punit.star, w)⟩

  @[inline] protected def listen : writer_t ω m α → writer_t ω m (α × ω)
  | ⟨ cmd ⟩ := ⟨ (λ x : α × ω, ((x.1,x.2),x.2)) <$> cmd ⟩

  @[inline] protected def pass : writer_t ω m (α × (ω → ω)) → writer_t ω m α
  | ⟨ cmd ⟩ := ⟨ uncurry (uncurry $ λ x (f : ω → ω) w, (x,f w)) <$> cmd ⟩

  @[inline] protected def pure [has_one ω] (a : α) : writer_t ω m α :=
  ⟨ pure (a,1) ⟩

  @[inline] protected def bind [has_mul ω] (x : writer_t ω m α) (f : α → writer_t ω m β) :
    writer_t ω m β :=
  ⟨ do x  ← x.run,
       x' ← (f x.1).run,
       pure (x'.1,x.2 * x'.2) ⟩

  instance [has_one ω] [has_mul ω] : monad (writer_t ω m) :=
  { pure := λ α, writer_t.pure, bind := λ α β, writer_t.bind }

  instance [monoid ω] [is_lawful_monad m] : is_lawful_monad (writer_t ω m) :=
  { id_map := by { intros, cases x, simp [(<$>),writer_t.bind,writer_t.pure] },
    pure_bind := by { intros, simp [has_pure.pure,writer_t.pure,(>>=),writer_t.bind], ext; refl },
    bind_assoc := by { intros, simp [(>>=),writer_t.bind,mul_assoc] with functor_norm } }

  @[inline] protected def lift [has_one ω] (a : m α) : writer_t ω m α :=
  ⟨ flip prod.mk 1 <$> a ⟩

  instance (m) [monad m] [has_one ω] : has_monad_lift m (writer_t ω m) :=
  ⟨ λ α, writer_t.lift  ⟩

  @[inline] protected def monad_map {m m'} [monad m] [monad m'] {α} (f : Π {α}, m α → m' α) :
    writer_t ω m α → writer_t ω m' α :=
  λ x, ⟨ f x.run ⟩

  instance (m m') [monad m] [monad m'] : monad_functor m m' (writer_t ω m) (writer_t ω m') :=
  ⟨@writer_t.monad_map ω m m' _ _⟩

  @[inline] protected def adapt {ω' : Type u} {α : Type u} (f : ω → ω') :
    writer_t ω m α → writer_t ω' m α :=
  λ x, ⟨prod.map id f <$> x.run⟩

  instance (ε) [has_one ω] [monad m] [monad_except ε m] : monad_except ε (writer_t ω m) :=
  { throw := λ α, writer_t.lift ∘ throw,
    catch := λ α x c, ⟨catch x.run (λ e, (c e).run)⟩ }
end
end writer_t


/--
An implementation of [MonadReader](
https://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Reader-Class.html#t:MonadReader).
It does not contain `local` because this function cannot be lifted using `monad_lift`.
Instead, the `monad_reader_adapter` class provides the more general `adapt_reader` function.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader (ρ : out_param (Type u)) (n : Type u → Type u) :=
(lift {α : Type u} : (∀ {m : Type u → Type u} [monad m], reader_t ρ m α) → n α)
```
-/
class monad_writer (ω : out_param (Type u)) (m : Type u → Type v) :=
(tell (w : ω) : m punit)
(listen {α} : m α → m (α × ω))
(pass {α : Type u} : m (α × (ω → ω)) → m α)

export monad_writer

instance {ω : Type u} {m : Type u → Type v} [monad m] : monad_writer ω (writer_t ω m) :=
{ tell := writer_t.tell,
  listen := λ α, writer_t.listen,
  pass := λ α, writer_t.pass }

instance {ω ρ : Type u} {m : Type u → Type v} [monad m] [monad_writer ω m] :
  monad_writer ω (reader_t ρ m) :=
{ tell := λ x, monad_lift (tell x : m punit),
  listen := λ α ⟨ cmd ⟩, ⟨ λ r, listen (cmd r) ⟩,
  pass := λ α ⟨ cmd ⟩, ⟨ λ r, pass (cmd r) ⟩ }

def swap_right {α β γ} : (α × β) × γ → (α × γ) × β
| ⟨⟨x,y⟩,z⟩ := ((x,z),y)

instance {ω σ : Type u} {m : Type u → Type v} [monad m] [monad_writer ω m] :
  monad_writer ω (state_t σ m) :=
{ tell := λ x, monad_lift (tell x : m punit),
  listen := λ α ⟨ cmd ⟩, ⟨ λ r, swap_right <$> listen (cmd r) ⟩,
  pass := λ α ⟨ cmd ⟩, ⟨ λ r, pass (swap_right <$> cmd r) ⟩ }
open function

def except_t.pass_aux {ε α ω} : except ε (α × (ω → ω)) → except ε α × (ω → ω)
| (except.error a) := (except.error a,id)
| (except.ok (x,y)) := (except.ok x,y)

instance {ω ε : Type u} {m : Type u → Type v} [monad m] [monad_writer ω m] :
  monad_writer ω (except_t ε m) :=
{ tell := λ x, monad_lift (tell x : m punit),
  listen := λ α ⟨ cmd ⟩, ⟨ uncurry (λ x y, flip prod.mk y <$> x) <$> listen cmd ⟩,
  pass := λ α ⟨ cmd ⟩, ⟨ pass (except_t.pass_aux <$> cmd) ⟩ }

def option_t.pass_aux {α ω} : option (α × (ω → ω)) → option α × (ω → ω)
| none := (none ,id)
| (some (x,y)) := (some x,y)

instance {ω : Type u} {m : Type u → Type v} [monad m] [monad_writer ω m] :
  monad_writer ω (option_t m) :=
{ tell := λ x, monad_lift (tell x : m punit),
  listen := λ α ⟨ cmd ⟩, ⟨ uncurry (λ x y, flip prod.mk y <$> x) <$> listen cmd ⟩,
  pass := λ α ⟨ cmd ⟩, ⟨ pass (option_t.pass_aux <$> cmd) ⟩ }

/-- Adapt a monad stack, changing the type of its top-most environment.

This class is comparable to
[Control.Lens.Magnify](https://hackage.haskell.org/package/lens-4.15.4/docs/Control-Lens-Zoom.html#t:Magnify),
but does not use lenses (why would it), and is derived automatically for any transformer
implementing `monad_functor`.

Note: This class can be seen as a simplification of the more "principled" definition
```
class monad_reader_functor (ρ ρ' : out_param (Type u)) (n n' : Type u → Type u) :=
(map {α : Type u} :
  (∀ {m : Type u → Type u} [monad m], reader_t ρ m α → reader_t ρ' m α) → n α → n' α)
```
-/
class monad_writer_adapter (ω ω' : out_param (Type u)) (m m' : Type u → Type v) :=
(adapt_writer {α : Type u} : (ω → ω') → m α → m' α)
export monad_writer_adapter (adapt_writer)

section
variables {ω ω' : Type u} {m m' : Type u → Type v}

/-- Transitivity.

This instance generates the type-class problem with a metavariable argument (which is why this
is marked as `[nolint dangerous_instance]`).
Currently that is not a problem, as there are almost no instances of `monad_functor` or
`monad_writer_adapter`.

see Note [lower instance priority] -/
@[nolint dangerous_instance, priority 100]
instance monad_writer_adapter_trans {n n' : Type u → Type v} [monad_writer_adapter ω ω' m m']
  [monad_functor m m' n n'] : monad_writer_adapter ω ω' n n' :=
⟨λ α f, monad_map (λ α, (adapt_writer f : m α → m' α))⟩

instance [monad m] : monad_writer_adapter ω ω' (writer_t ω m) (writer_t ω' m) :=
⟨λ α, writer_t.adapt⟩
end

instance (ω : Type u) (m out) [monad_run out m] : monad_run (λ α, out (α × ω)) (writer_t ω m) :=
⟨λ α x, run $ x.run ⟩

/-- reduce the equivalence between two writer monads to the equivalence between
their underlying monad -/
def writer_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ ω₁ : Type u₀} {α₂ ω₂ : Type u₁} (F : (m₁ (α₁ × ω₁)) ≃ (m₂ (α₂ × ω₂))) :
  writer_t ω₁ m₁ α₁ ≃ writer_t ω₂ m₂ α₂ :=
{ to_fun := λ ⟨f⟩, ⟨F f⟩,
  inv_fun := λ ⟨f⟩, ⟨F.symm f⟩,
  left_inv := λ ⟨f⟩, congr_arg writer_t.mk $ F.left_inv _,
  right_inv := λ ⟨f⟩, congr_arg writer_t.mk $ F.right_inv _ }
