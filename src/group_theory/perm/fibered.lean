import group_theory.perm.basic
import group_theory.subgroup.basic

/-!
-/

variables {α β γ : Type*} {f : α → β}


namespace equiv

namespace perm

def fiberwise (f : α → β) : subgroup (equiv.perm α) :=
{ carrier := {e : equiv.perm α | ∀ x, f (e x) = f x},
  mul_mem' := λ e₁ e₂ h₁ h₂ x, (h₁ _).trans (h₂ _),
  one_mem' := λ x, rfl,
  inv_mem' := λ e h, e.surjective.forall.2 $ λ x, by rw [e.inv_apply_self, ← h x] }

@[simp] lemma mem_fiberwise {e : equiv.perm α} : e ∈ fiberwise f ↔ ∀ x, f (e x) = f x := iff.rfl

@[simp] lemma fiberwise_const (c : β) : fiberwise (λ x : α, c) = ⊤ := by { ext e, simp }

lemma fiberwise_injective (hf : function.injective f) : fiberwise f = ⊥ :=
by { ext e, simp [hf.eq_iff, fun_like.ext_iff] }

lemma fiberwise_prod_mk (f : α → β) (g : α → γ) :
  fiberwise (λ x, (f x, g x)) = fiberwise f ⊓ fiberwise g :=
by { ext e, simp only [mem_fiberwise, subgroup.mem_inf, prod.mk.inj_iff, forall_and_distrib] }

lemma fiberwise_equiv_pi_aux {f : α → β} (e : Π y, equiv.perm {x // f x = y}) (x : α) :
  ((e (f $ e (f x) ⟨x, rfl⟩)).symm ⟨e (f x) ⟨x, rfl⟩, rfl⟩ : α) = x :=
begin
  suffices : ∀ y z (hy : f x = y) (hz : f (e y ⟨x, hy⟩) = z),
    ((e z).symm ⟨e y ⟨x, hy⟩, hz⟩ : α) = x, from this _ _ rfl rfl,
  intros y z hy hz,
  obtain rfl : y = z := (e y ⟨x, hy⟩).coe_prop.out.symm.trans hz,
  simp only [(e y).symm_apply_apply, subtype.coe_eta, subtype.coe_mk]
end

def fiberwise_equiv_pi (f : α → β) : fiberwise f ≃* Π y : β, equiv.perm {x : α // f x = y} :=
{ to_fun := λ e y, (e : equiv.perm α).subtype_perm $ λ x, by rw [e.coe_prop],
  inv_fun := λ e, ⟨⟨λ x, e (f x) ⟨x, rfl⟩, λ x, (e (f x)).symm ⟨x, rfl⟩,
    fiberwise_equiv_pi_aux _, fiberwise_equiv_pi_aux (λ x, (e x).symm)⟩, λ x, (e (f x) ⟨x, rfl⟩).2⟩,
  left_inv := λ e, subtype.ext $ ext $ λ x, rfl,
  right_inv := λ e, funext $ λ y, ext $
    begin
      rintro ⟨x, rfl⟩,
      simp only [subtype.coe_mk, coe_fn_mk, subtype_perm_apply, subtype.coe_eta],
    end,
  map_mul' := λ e₁ e₂, funext $ λ y, ext $ λ x, by simp only [subgroup.coe_mul, equiv.perm.coe_mul,
    (∘), subtype.coe_mk, subtype_perm_apply, pi.mul_apply] }

end perm

end equiv
