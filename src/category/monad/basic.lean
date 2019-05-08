
import tactic.interactive

attribute [extensionality] reader_t.ext state_t.ext except_t.ext option_t.ext
attribute [functor_norm]   bind_assoc pure_bind bind_pure
universes u v

lemma map_eq_bind_pure_comp (m : Type u → Type v) [monad m] [is_lawful_monad m] {α β : Type u} (f : α → β) (x : m α) :
  f <$> x = x >>= pure ∘ f := by rw bind_pure_comp_eq_map
