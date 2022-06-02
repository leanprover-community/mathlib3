import representation_theory.invariants

universes v u

variables {k : Type u} [comm_semiring k] {G : Type u} [group G] {M : Type u}
  [add_comm_group M] [module k M] (ρ : representation k G M)

def one_cocycles : submodule k (G → M) :=
{ carrier := { f | ∀ g h, f (g * h) = ρ g (f h) + f g },
  add_mem' := λ a b ha hb g h, by {simp only [pi.add_apply, ha g, hb g, (ρ g).map_add], abel},
  zero_mem' := λ g h, by simp,
  smul_mem' := λ r f hf g h, by simp [hf g] }

instance : has_coe_to_fun (one_cocycles ρ) (λ _, G → M) := ⟨λ f, (f : G → M)⟩

variables {ρ}

lemma mem_one_cocycles (f : G → M) :
  f ∈ one_cocycles ρ ↔ ∀ g h : G, f (g * h) = ρ g (f h) + f g := iff.rfl

lemma one_cocycles_map_mul (f : one_cocycles ρ) (g h : G) : f (g * h) = ρ g (f h) + f g := f.2 g h

lemma one_cocycles_map_one (f : one_cocycles ρ) : f 1 = 0 :=
by have := one_cocycles_map_mul f 1 1; simp * at *

lemma one_cocycles_map_inv (f : one_cocycles ρ) (g : G) :
  ρ g (f g⁻¹) = -f g :=
by rw [←add_eq_zero_iff_eq_neg, ←one_cocycles_map_one f, ←mul_inv_self g, one_cocycles_map_mul]

variables (ρ)

def one_coboundaries : submodule k (G → M) :=
{ carrier := { f | ∃ (m : M), ∀ g : G, f g = ρ g m - m },
  zero_mem' := ⟨0, λ g, by simp⟩,
  add_mem' := λ x y ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n, λ g,
  begin
    dsimp,
    rw [hm g, hn g, map_add],
    abel,
  end⟩,
  smul_mem' := λ r x ⟨m, hm⟩, ⟨r • m, λ g, by simp [hm g, smul_sub]⟩ }

instance : has_coe_to_fun (one_coboundaries ρ) (λ _, G → M) := ⟨λ f, (f : G → M)⟩

variables {ρ}

lemma mem_one_coboundaries (f : G → M) :
  f ∈ one_coboundaries ρ ↔ ∃ (m : M), ∀ g : G, f g = ρ g m - m := iff.rfl

lemma one_coboundaries_le_one_cocycles :
  one_coboundaries ρ ≤ one_cocycles ρ :=
λ x ⟨m, hm⟩ g h, by simp [hm, map_mul]

variables (ρ)
