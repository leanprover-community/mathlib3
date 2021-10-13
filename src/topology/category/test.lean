import topology.homotopy.basic

universes u v w

variables {X : Type u} {Y : Type v} {Z : Type w}
variables [topological_space X] [topological_space Y] [topological_space Z]

example {f₀ f₁ : C(X, Y)} {g₀ g₁ : C(Y, Z)} (F : f₀.homotopy f₁) (G : g₀.homotopy g₁) :
  continuous_map.homotopy (g₀.comp f₀) (g₁.comp f₁) :=
{ to_fun := λ x, G (x.1, F x),
  continuous_to_fun := by continuity,
  to_fun_zero := by simp,
  to_fun_one := by simp }
