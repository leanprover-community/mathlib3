import .defs

section imprimitive_explicit

variables (A : Type*) (B : Type*) (L : Type*) (M : Type*) [group A] [group B] [mul_action A L]

def imprimitive_smul (h : mul_action B M) : has_smul (B ≀[L] A) (M × L) :=
{ smul := (λ g x, ⟨g.left (g.right • x.2) • x.1, g.right • x.2⟩)}

def imprimitive_smul_def (h : mul_action B M) (g : (B ≀[L] A))(m : M) (l : L) :
  (imprimitive_smul A B L M h).smul g (m,l) = (g.left (g.right • l) • m, g.right • l) := rfl

def imprimitive (h : mul_action B M) : mul_action (B ≀[L] A) (M × L) :=
{
  to_has_smul := imprimitive_smul A B L M h,
  one_smul := begin
    rintros ⟨m, l⟩,
    rw imprimitive_smul_def,
    simp,
  end,
  mul_smul := begin
    rintros g h ⟨m, l⟩,
    repeat {rw imprimitive_smul_def},
    simp [mul_smul],
  end,
}

end imprimitive_explicit

section imprimitive_typeclass
variables (A : Type*) (B : Type*) (L : Type*) (M : Type*) [group A] [group B] [mul_action A L] [mul_action B M ] --TODO inhabited M, L follows from the faithful action, not sure if I want to make this explicit

--TODO: move this above
instance imprimitive_mul_action : mul_action (B ≀[L] A) (M × L) :=
begin
  apply imprimitive,
  apply_instance,
end

end imprimitive_typeclass

section imprimitive_faithful

variables (A : Type*) (B : Type*) (L : Type*) (M : Type*) [group A] [group B] [mul_action A L] [mul_action B M ] [has_faithful_smul A L] [has_faithful_smul B M] [inhabited M] [inhabited L]
--TODO inhabited M, L follows from the faithful action, not sure if I want to make this explicit

@[simp]
def imprimitive_smul_def' (g : (B ≀[L] A))(m : M) (l : L) :
  g • (m,l) = (g.left (g.right • l) • m, g.right • l) := rfl


instance imprimitive_faithful : has_faithful_smul (B ≀[L] A) (M × L) :=
begin
  split,
  rintros ⟨f1, a1⟩ ⟨f2, a2⟩ h,
  have eqmr : ∀ l : L, a1 • l = a2 • l, by begin
    intros l,
    have m : M := default,
    specialize h ⟨m, l⟩,
    simp at h,
    cc,
  end,
  have eqa : a1 = a2, {
    apply eq_of_smul_eq_smul eqmr,
  },
  ext l,
  {
    simp,
    have eql : ∀ m : M, f1 l • m = f2 l • m, by begin
      intro m,
      specialize h ⟨m, a1⁻¹ • l⟩,
      simp [eqa] at h,
      exact h,
    end,
    apply eq_of_smul_eq_smul eql,
  },
  {
    exact eqa,
  }

end

end imprimitive_faithful
