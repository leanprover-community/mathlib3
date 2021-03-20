/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Monad encapsulating continuation passing programming style, similar to
Haskell's `Cont`, `ContT` and `MonadCont`:
<http://hackage.haskell.org/package/mtl-2.2.2/docs/Control-Monad-Cont.html>
-/
import control.monad.writer

universes u v w u₀ u₁ v₀ v₁

structure monad_cont.label (α : Type w) (m : Type u → Type v) (β : Type u) :=
(apply : α → m β)

def monad_cont.goto {α β} {m : Type u → Type v} (f : monad_cont.label α m β) (x : α) := f.apply x

class monad_cont (m : Type u → Type v) :=
(call_cc : Π {α β}, ((monad_cont.label α m β) → m α) → m α)

open monad_cont

class is_lawful_monad_cont (m : Type u → Type v) [monad m] [monad_cont m]
extends is_lawful_monad m :=
(call_cc_bind_right {α ω γ} (cmd : m α) (next : (label ω m γ) → α → m ω) :
  call_cc (λ f, cmd >>= next f) = cmd >>= λ x, call_cc (λ f, next f x))
(call_cc_bind_left {α} (β) (x : α) (dead : label α m β → β → m α) :
  call_cc (λ f : label α m β, goto f x >>= dead f) = pure x)
(call_cc_dummy {α β} (dummy : m α) :
  call_cc (λ f : label α m β, dummy) = dummy)

export is_lawful_monad_cont

def cont_t (r : Type u) (m : Type u → Type v) (α : Type w) := (α → m r) → m r

@[reducible] def cont (r : Type u) (α : Type w) := cont_t r id α

namespace cont_t

export monad_cont (label goto)

variables {r : Type u} {m : Type u → Type v} {α β γ ω : Type w}

def run : cont_t r m α → (α → m r) → m r := id

def map (f : m r → m r) (x : cont_t r m α) : cont_t r m α := f ∘ x

lemma run_cont_t_map_cont_t (f : m r → m r) (x : cont_t r m α) :
  run (map f x) = f ∘ run x := rfl

def with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) : cont_t r m β :=
λ g, x $ f g

lemma run_with_cont_t (f : (β → m r) → α → m r) (x : cont_t r m α) :
  run (with_cont_t f x) = run x ∘ f := rfl

@[ext]
protected lemma ext {x y : cont_t r m α}
  (h : ∀ f, x.run f = y.run f) :
  x = y := by { ext; apply h }

instance : monad (cont_t r m) :=
{ pure := λ α x f, f x,
  bind := λ α β x f g, x $ λ i, f i g }

instance : is_lawful_monad (cont_t r m) :=
{ id_map := by { intros, refl },
  pure_bind := by { intros, ext, refl },
  bind_assoc := by { intros, ext, refl } }

def monad_lift [monad m] {α} : m α → cont_t r m α :=
λ x f, x >>= f

instance [monad m] : has_monad_lift m (cont_t r m) :=
{ monad_lift := λ α, cont_t.monad_lift }

lemma monad_lift_bind [monad m] [is_lawful_monad m] {α β} (x : m α) (f : α → m β) :
  (monad_lift (x >>= f) : cont_t r m β) = monad_lift x >>= monad_lift ∘ f :=
begin
  ext,
  simp only [monad_lift,has_monad_lift.monad_lift,(∘),(>>=),bind_assoc,id.def,run,cont_t.monad_lift]
end

instance : monad_cont (cont_t r m) :=
{ call_cc := λ α β f g, f ⟨λ x h, g x⟩ g }

instance : is_lawful_monad_cont (cont_t r m) :=
{ call_cc_bind_right := by intros; ext; refl,
  call_cc_bind_left := by intros; ext; refl,
  call_cc_dummy := by intros; ext; refl }

instance (ε) [monad_except ε m] : monad_except ε (cont_t r m) :=
{ throw := λ x e f, throw e,
  catch := λ α act h f, catch (act f) (λ e, h e f) }

instance : monad_run (λ α, (α → m r) → ulift.{u v} (m r)) (cont_t.{u v u} r m) :=
{ run := λ α f x, ⟨ f x ⟩ }

end cont_t

variables {m : Type u → Type v} [monad m]

def except_t.mk_label {α β ε} : label (except.{u u} ε α) m β → label α (except_t ε m) β
| ⟨ f ⟩ := ⟨ λ a, monad_lift $ f (except.ok a) ⟩

lemma except_t.goto_mk_label {α β ε : Type*} (x : label (except.{u u} ε α) m β) (i : α) :
  goto (except_t.mk_label x) i = ⟨ except.ok <$> goto x (except.ok i) ⟩ := by cases x; refl

def except_t.call_cc
  {ε} [monad_cont m] {α β : Type*} (f : label α (except_t ε m) β → except_t ε m α) :
  except_t ε m α :=
except_t.mk (call_cc $ λ x : label _ m β, except_t.run $ f (except_t.mk_label x) : m (except ε α))

instance {ε} [monad_cont m] : monad_cont (except_t ε m) :=
{ call_cc := λ α β, except_t.call_cc }

instance {ε} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (except_t ε m) :=
{ call_cc_bind_right := by { intros, simp [call_cc,except_t.call_cc,call_cc_bind_right], ext, dsimp,
    congr' with ⟨ ⟩; simp [except_t.bind_cont,@call_cc_dummy m _], },
  call_cc_bind_left  := by { intros,
    simp [call_cc,except_t.call_cc,call_cc_bind_right,except_t.goto_mk_label,map_eq_bind_pure_comp,
      bind_assoc,@call_cc_bind_left m _], ext, refl },
  call_cc_dummy := by { intros, simp [call_cc,except_t.call_cc,@call_cc_dummy m _], ext, refl }, }

def option_t.mk_label {α β} : label (option.{u} α) m β → label α (option_t m) β
| ⟨ f ⟩ := ⟨ λ a, monad_lift $ f (some a) ⟩

lemma option_t.goto_mk_label {α β : Type*} (x : label (option.{u} α) m β) (i : α) :
  goto (option_t.mk_label x) i = ⟨ some <$> goto x (some i) ⟩ := by cases x; refl

def option_t.call_cc [monad_cont m] {α β : Type*} (f : label α (option_t m) β → option_t m α) :
  option_t m α :=
option_t.mk (call_cc $ λ x : label _ m β, option_t.run $ f (option_t.mk_label x) : m (option α))

instance [monad_cont m] : monad_cont (option_t m) :=
{ call_cc := λ α β, option_t.call_cc }

instance [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (option_t m) :=
{ call_cc_bind_right := by { intros, simp [call_cc,option_t.call_cc,call_cc_bind_right], ext, dsimp,
    congr' with ⟨ ⟩; simp [option_t.bind_cont,@call_cc_dummy m _], },
  call_cc_bind_left  := by { intros, simp [call_cc,option_t.call_cc,call_cc_bind_right,
    option_t.goto_mk_label,map_eq_bind_pure_comp,bind_assoc,@call_cc_bind_left m _], ext, refl },
  call_cc_dummy := by { intros, simp [call_cc,option_t.call_cc,@call_cc_dummy m _], ext, refl }, }

def writer_t.mk_label {α β ω} [has_one ω] : label (α × ω) m β → label α (writer_t ω m) β
| ⟨ f ⟩ := ⟨ λ a, monad_lift $ f (a,1) ⟩

lemma writer_t.goto_mk_label {α β ω : Type*} [has_one ω] (x : label (α × ω) m β) (i : α) :
  goto (writer_t.mk_label x) i = monad_lift (goto x (i,1)) := by cases x; refl

def writer_t.call_cc [monad_cont m] {α β ω : Type*} [has_one ω]
  (f : label α (writer_t ω m) β → writer_t ω m α) : writer_t ω m α :=
⟨ call_cc (writer_t.run ∘ f ∘ writer_t.mk_label : label (α × ω) m β → m (α × ω)) ⟩

instance (ω) [monad m] [has_one ω] [monad_cont m] : monad_cont (writer_t ω m) :=
{ call_cc := λ α β, writer_t.call_cc }

def state_t.mk_label {α β σ : Type u} : label (α × σ) m (β × σ) → label α (state_t σ m) β
| ⟨ f ⟩ := ⟨ λ a, ⟨ λ s, f (a,s) ⟩ ⟩

lemma state_t.goto_mk_label {α β σ : Type u} (x : label (α × σ) m (β × σ)) (i : α) :
  goto (state_t.mk_label x) i = ⟨ λ s, (goto x (i,s)) ⟩ := by cases x; refl

def state_t.call_cc {σ}  [monad_cont m] {α β : Type*}
  (f : label α (state_t σ m) β → state_t σ m α) : state_t σ m α :=
⟨ λ r, call_cc (λ f', (f $ state_t.mk_label f').run r) ⟩

instance {σ} [monad_cont m] : monad_cont (state_t σ m) :=
{ call_cc := λ α β, state_t.call_cc }

instance {σ} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (state_t σ m) :=
{ call_cc_bind_right := by { intros,
    simp [call_cc,state_t.call_cc,call_cc_bind_right,(>>=),state_t.bind], ext, dsimp,
    congr' with ⟨x₀,x₁⟩, refl },
  call_cc_bind_left  := by { intros, simp [call_cc,state_t.call_cc,call_cc_bind_left,(>>=),
    state_t.bind,state_t.goto_mk_label], ext, refl },
  call_cc_dummy := by { intros, simp [call_cc,state_t.call_cc,call_cc_bind_right,(>>=),
    state_t.bind,@call_cc_dummy m _], ext, refl }, }

def reader_t.mk_label {α β} (ρ) : label α m β → label α (reader_t ρ m) β
| ⟨ f ⟩ := ⟨ monad_lift ∘ f ⟩

lemma reader_t.goto_mk_label {α ρ β} (x : label α m β) (i : α) :
  goto (reader_t.mk_label ρ x) i = monad_lift (goto x i) := by cases x; refl

def reader_t.call_cc {ε}  [monad_cont m] {α β : Type*}
  (f : label α (reader_t ε m) β → reader_t ε m α) : reader_t ε m α :=
⟨ λ r, call_cc (λ f', (f $ reader_t.mk_label _ f').run r) ⟩

instance {ρ} [monad_cont m] : monad_cont (reader_t ρ m) :=
{ call_cc := λ α β, reader_t.call_cc }

instance {ρ} [monad_cont m] [is_lawful_monad_cont m] : is_lawful_monad_cont (reader_t ρ m) :=
{ call_cc_bind_right :=
    by { intros, simp [call_cc,reader_t.call_cc,call_cc_bind_right], ext, refl },
  call_cc_bind_left  := by { intros, simp [call_cc,reader_t.call_cc,call_cc_bind_left,
    reader_t.goto_mk_label], ext, refl },
  call_cc_dummy := by { intros, simp [call_cc,reader_t.call_cc,@call_cc_dummy m _], ext, refl } }

/-- reduce the equivalence between two continuation passing monads to the equivalence between
their underlying monad -/
def cont_t.equiv {m₁ : Type u₀ → Type v₀} {m₂ : Type u₁ → Type v₁}
  {α₁ r₁ : Type u₀} {α₂ r₂ : Type u₁} (F : m₁ r₁ ≃ m₂ r₂) (G : α₁ ≃ α₂) :
  cont_t r₁ m₁ α₁ ≃ cont_t r₂ m₂ α₂ :=
{ to_fun := λ f r, F $ f $ λ x, F.symm $ r $ G x,
  inv_fun := λ f r, F.symm $ f $ λ x, F $ r $ G.symm x,
  left_inv := λ f, by funext r; simp,
  right_inv := λ f, by funext r; simp }
