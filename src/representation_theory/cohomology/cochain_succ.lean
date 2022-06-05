/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import group_theory.group_action.basic
import data.fin_simplicial_complex
import group_theory.free_abelian_group
import algebra.big_operators.finsupp
import algebra.monoid_algebra.basic
import representation_theory.cohomology.lemmas
import representation_theory.cohomology.std_resn

/-!
# Group cohomology

We describe an explicit model for the group cohomology groups `Hⁿ(G,M)`,
as certain homogeneous cocycles over coboundaries.

-/

namespace add_comm_group
-- a sensible add_comm_group constructor

universe uA

variables (A : Type uA) [has_add A] [has_zero A] [has_neg A]

class add_comm_group_aux  : Prop :=
(add_assoc : ∀ (a b c : A), (a + b) + c = a + (b + c))
(zero_add : ∀ (a : A), 0 + a = a)
(add_left_neg : ∀ (a : A), -a + a = 0)
(add_comm : ∀ (a b : A), a + b = b + a)

open add_comm_group_aux

instance add_comm_group_aux.to_add_comm_group [add_comm_group_aux A] : add_comm_group A :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_zero := λ a, (add_comm_group_aux.add_comm 0 a) ▸ (zero_add a),
  ..‹add_comm_group_aux A›}

end add_comm_group

namespace group_cohomology

universes uG uM uA

variables (G : Type uG) [group G] (M : Type uM) [add_comm_group M]
  [distrib_mul_action G M] (n : ℕ)

-- need the homogeneous cochains, cocycles and coboundaries
/-- `cochain-succ G M n.succ` is homogeneous `n`-cochains, namely functions
$$c:G^{n+1}\to M$$ which are homogeneous in the sense that for s in G, we have
$$c((s*g_i)_i)=s\bub c((g_i)_i)$$.
-/
@[ext] structure cochain_succ :=
(to_fun : (fin n → G) → M)
-- to_fin is G-linear
(smul_apply' : ∀ (s : G) (g : fin n → G), s • to_fun g = to_fun (λ i, s * g i))

namespace cochain_succ

variables {G M n}
instance : has_coe_to_fun (cochain_succ G M n) (λ _, (fin n → G) → M) :=
{ coe := to_fun }

@[simp] lemma coe_eval (c : (fin n → G) → M)
  (hc : ∀ (s : G) (g : fin n → G), s • c g = c (λ i, s * g i)) (g : fin n → G) :
  (⟨c, hc⟩ : cochain_succ G M n) g = c g := rfl

@[simp] lemma to_fun_eval (c : cochain_succ G M n) (g : fin n → G) : c.to_fun g = c g := rfl

@[ext] theorem ext' (c₁ c₂ : cochain_succ G M n) (h : ∀ g : fin n → G, c₁ g = c₂ g) : c₁ = c₂ :=
ext c₁ c₂ $ funext h

theorem ext_iff' (c₁ c₂ : cochain_succ G M n) : c₁ = c₂ ↔ ∀ g : fin n → G, c₁ g = c₂ g :=
⟨λ h x, h ▸ rfl, ext' _ _⟩

variables (G M n)

def zero : cochain_succ G M n :=
{ to_fun := 0,
  smul_apply' := λ s g, smul_zero s }

instance : has_zero (cochain_succ G M n) := ⟨zero G M n⟩

@[simp] lemma zero_apply (g : fin n → G) : (0 : cochain_succ G M n) g = 0 := rfl

variables {G M n}

@[simp]
lemma smul_apply (c : cochain_succ G M n) (s : G) (g : fin n → G) : s • c g = c (λ i, s * g i) :=
c.smul_apply' s g

def neg (c₁ : cochain_succ G M n): cochain_succ G M n :=
{ to_fun := λ g, -c₁ g,
  smul_apply' := λ s g, by {rw ← smul_apply, apply smul_neg }, }

instance : has_neg (cochain_succ G M n) := ⟨neg⟩

@[simp] lemma neg_apply (c : cochain_succ G M n) (g : fin n → G) :
  (-c : cochain_succ G M n) g = -(c g) := rfl

def add (c₁ c₂ : cochain_succ G M n) : cochain_succ G M n :=
{ to_fun := λ g, c₁ g + c₂ g,
  smul_apply' := by {intros, simp * at *}, }

instance : has_add (cochain_succ G M n) := ⟨add⟩

@[simp] lemma add_apply (c₁ c₂ : cochain_succ G M n) (g : fin n → G) : (c₁ + c₂) g = c₁ g + c₂ g :=
rfl

instance : add_comm_group.add_comm_group_aux (cochain_succ G M n) :=
{ add_assoc := by { intros, ext, simp [add_assoc] },
  zero_add := by {intros, ext, simp },
  add_left_neg := by { intros, ext, simp },
  add_comm := by {intros, ext, simp [add_comm] },
}

@[simp] lemma sub_apply (c₁ c₂ : cochain_succ G M n) (g : fin n → G) :
  (c₁ - c₂) g = c₁ g - c₂ g :=
begin
  simp [sub_eq_add_neg],
end

@[simp] lemma int_smul_apply (c : cochain_succ G M n) (z : ℤ) (g : fin n → G) :
  (z • c) g = z • (c g) :=
begin
  apply int.induction_on z,
  { simp },
  { intros i this, simpa [add_zsmul] },
  { intros i this, rw [int.pred_smul, int.pred_smul, sub_apply, this] },
end

def d {i j : ℕ} (hj : j = i + 1) : cochain_succ G M i →+ cochain_succ G M j :=
{ to_fun := λ c,
  { to_fun := λ g, (finset.range j).sum (λ p, (-1 : ℤ)^p • c $ λ t, g (fin.delta hj p t)),
    smul_apply' := λ s g, begin
      simp only [finset.smul_sum, int_smul_apply, ← c.smul_apply, distrib_mul_action.smul_zsmul],
    end },
  map_zero' := begin ext, simp end,
  map_add' := λ x y, by {ext, simp [finset.sum_add_distrib]} }

lemma d_eval {i j : ℕ} (hj : j = i + 1) (c : cochain_succ G M i) (g : fin j → G) :
  d hj c g = (finset.range j).sum (λ p, (-1 : ℤ)^p • c $ λ t, g $ fin.delta hj p t) := rfl
variables {i j : ℕ} (hj : j = i + 1) (c : cochain_succ G M i) (g : fin j → G)
#exit
theorem total_d_eq_d :
  finsupp.total (fin i → G) M ℤ c (group_ring.d G hj (group_ring.of _ g)) = d hj c g :=
begin
  rw [d_eval, group_ring.d_of],
  simp only [int_smul_apply, finsupp.total_single, linear_map.map_sum],
end

theorem d_squared_eq_zero {i j k : ℕ} (hj : j = i + 1) (hk : k = j + 1) (c : cochain_succ G M i) :
  d hk (d hj c) = 0 :=
begin
  ext g,
  suffices : d hk (d hj c) g = finsupp.total (fin i → G) M ℤ c (group_ring.d G hj
    (group_ring.d G hk (group_ring.of _ g))),
  by rwa [group_ring.d_squared, map_zero] at this,
  simp only [←total_d_eq_d, group_ring.d_of, linear_map.map_sum, group_ring.d_single,
    finsupp.total_single, mul_comm, mul_smul, finset.smul_sum],
 end

end cochain_succ

-- I claim that I just resolved `ℤ` (+ trivial `G`-action) by finite free `ℤ[G]`-modules.

end group_cohomology

namespace add_comm_group

variables (M : Type*) [add_comm_monoid M]

instance : semiring (M →+ M) :=
{ mul := add_monoid_hom.comp,
  mul_assoc := λ _ _ _, (add_monoid_hom.comp_assoc _ _ _).symm,
  one := add_monoid_hom.id _,
  one_mul := add_monoid_hom.id_comp,
  mul_one := add_monoid_hom.comp_id,
  zero_mul := add_monoid_hom.zero_comp,
  mul_zero := add_monoid_hom.comp_zero,
  left_distrib := add_monoid_hom.comp_add,
  right_distrib := add_monoid_hom.add_comp,
  ..add_monoid_hom.add_comm_monoid }

variables (A : Type*) [add_comm_group A]

instance : ring (A →+ A) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. add_comm_group.add_monoid_hom.semiring A
}

end add_comm_group

namespace finsupp

@[simp] lemma emb_domain_refl {α M : Type*} [has_zero M] (f : α →₀ M) :
  emb_domain (function.embedding.refl α) f = f :=
begin
  ext a,
  exact emb_domain_apply (function.embedding.refl α) f a,
end

def emb_domain_comp {α β γ M : Type*} [has_zero M] (i : α ↪ β) (j : β ↪ γ) (f : α →₀ M) :
  emb_domain (i.trans j) f = emb_domain j (emb_domain i f) :=
begin
  ext c,
  by_cases ha : ∃ a : α, j (i a) = c,
  { rcases ha with ⟨a, rfl⟩,
    rw emb_domain_apply,
    rw emb_domain_apply,
    exact emb_domain_apply (i.trans j) f _ },
  { convert eq.refl (0 : M),
    { rw emb_domain_notin_range,
      exact ha },
    { by_cases h : ∃ b : β, j b = c, -- really?
      { rcases h with ⟨b, rfl⟩,
        rw emb_domain_apply,
        rw emb_domain_notin_range,
        rintro ⟨a, rfl⟩,
        exact ha ⟨a, rfl⟩ },
      { rw finsupp.emb_domain_notin_range,
      exact h } } },
end
noncomputable def equiv_congr {α β M : Type*} [has_zero M] (e : α ≃ β) : (β →₀ M) ≃ (α →₀ M) :=
{ to_fun := λ l, finsupp.emb_domain e.symm.to_embedding l,
  inv_fun := λ l, finsupp.emb_domain e.to_embedding l,
  left_inv := λ f, by { ext, simp [← finsupp.emb_domain_comp] },
  right_inv := λ f, by {ext, simp [← finsupp.emb_domain_comp] } }

theorem equiv_congr_apply {α β M : Type*} [has_zero M] (e : α ≃ β) (g : β →₀ M) (a : α) :
  equiv_congr e g a = g (e a)  :=
begin
  convert emb_domain_apply _ _ _,
  simp,
end

theorem equiv_congr_apply' {α β M : Type*} [has_zero M] (e : α ≃ β) (g : β →₀ M) (b : β) :
  equiv_congr e g (e.symm b) = g b :=
emb_domain_apply _ _ _

def equiv_fun {X Y : Sort*} (A : Sort*) (e : X ≃ Y) : (A → X) ≃ (A → Y) :=
{ to_fun := λ f a, e (f a),
  inv_fun := λ g b, e.symm (g b),
  left_inv := λ h, by simp,
  right_inv := λ h, by simp }


/- I think everything after here wasn't here when I wrote my files - Amelia -/



-- The Lean `(fin i.succ → G) →₀ ℤ` is the Cassels-Froehlich `P i`, for `i : ℕ`.
-- A lot of what they say works for what they would call $P_{-1}$.
-- I'm not even going to bother introducing notation

variables {G : Type*} [group G] (i : ℕ)

noncomputable instance finsupp.distrib_mul_action' :
  distrib_mul_action G ((fin i → G) →₀ ℤ) :=
{ smul := λ s c, finsupp.equiv_congr (equiv_fun (fin i) (equiv.mul_left s⁻¹ : G ≃ G)) c,
  -- it could be equiv.mul_right s, I didn't check carefully
  one_smul := λ b,
  begin
    ext p,
    unfold has_scalar.smul,
    rw equiv_congr_apply,
    apply congr_arg,
    ext t,
    simp,
    convert one_mul _,
  end,
  mul_smul := λ x y b, begin
    ext p,
    unfold has_scalar.smul,
    rw equiv_congr_apply,
    rw equiv_congr_apply,
    rw equiv_congr_apply,
    unfold equiv_fun,
    dsimp,
    apply congr_arg,
    ext t,
    simp [mul_assoc],
  end,
  smul_add := λ s x y, begin
    ext p,
    unfold has_scalar.smul,
    rw equiv_congr_apply,
    rw finsupp.add_apply,
    rw [← equiv_congr_apply, ← equiv_congr_apply],
    refl,
  end,
  smul_zero := λ s, begin
    ext p,
    simp [has_scalar.smul],
    refl,
  end }

noncomputable def add_equiv.of_finsupp_and_equiv
  {S T : Sort*} (e : S ≃ T) : (S →₀ ℤ) ≃+ (T →₀ ℤ) :=
{ to_fun := equiv_map_domain e,
  inv_fun := equiv_map_domain (equiv.symm e),
  left_inv := by {intro φ, ext, simp},--tidy?,
  right_inv := by {intro φ, ext, simp},
  map_add' := by {intros φ₁ φ₂, ext1, simp}}

@[simp] lemma add_equiv.of_finsupp_and_equiv_refl {S : Type*} :
  add_equiv.of_finsupp_and_equiv (equiv.refl S) = add_equiv.refl (S →₀ ℤ) :=
begin
  ext φ s,
  simp,
  refl,
end

@[simp] lemma add_equiv.of_finsupp_and_equiv_trans {S T U : Sort*}
  (e₁ : S ≃ T) (e₂ : T ≃ U) :
  add_equiv.of_finsupp_and_equiv (e₁.trans e₂) =
  (add_equiv.of_finsupp_and_equiv e₁).trans (add_equiv.of_finsupp_and_equiv e₂) :=
begin
  ext φ u,
  simp,
  refl,
end

--noncomputable def add_equiv.of_finsupp_and_add_equiv

def equiv_comap_or_something
  {S T : Sort*} (ι : Sort*) (e : S ≃ T) : (ι → S) ≃ (ι → T) :=
{ to_fun := λ φ i, e (φ i),
  inv_fun := λ ψ i, e.symm (ψ i),
  left_inv := by { intro φ, simp },
  right_inv := by { intro ψ, simp } }

@[simp] lemma equiv_comap_or_something.refl  {ι S : Sort*} :
  equiv_comap_or_something ι (equiv.refl S) = equiv.refl (ι → S) := rfl


@[simp] lemma equiv_comap_or_something.trans
  {ι S T U : Sort*} (e₁ : S ≃ T) (e₂ : T ≃ U):
  equiv_comap_or_something ι (e₁.trans e₂) =
  (equiv_comap_or_something ι e₁).trans (equiv_comap_or_something ι e₂) :=
begin
  ext fS i,
  simp,
  refl,
end

def left_translation_equiv (s : G) : G ≃ G :=
{ to_fun := λ g, s * g,
  inv_fun := λ h, s⁻¹ * h,
  left_inv := by intro g; simp,
  right_inv := by intro h; simp
  }

@[simp] lemma left_translation_equiv_apply (s g : G) : left_translation_equiv s g = s * g := rfl

@[simp] theorem left_translation_equiv.comp (g₁ g₂ : G) :
 left_translation_equiv (g₁ * g₂)
 = (left_translation_equiv g₂).trans (left_translation_equiv g₁) :=
begin
  ext h,
  simp [mul_assoc],
end


@[simp] lemma left_translation_equiv_one : left_translation_equiv (1 : G) = equiv.refl G :=
begin
  ext,
  simp,
end

noncomputable example (R : Type) [comm_ring R] (c : G →* R) : monoid_algebra ℤ G →+* R :=
monoid_algebra.lift ℤ G R c
-- timing out at the moment and I don't use it anywhere
#exit
noncomputable
def group_ring_action :
(monoid_algebra ℤ G) →+* (((fin i → G) →₀ ℤ) →+ ((fin i → G) →₀ ℤ)) :=
{ to_fun :=
begin
  refine monoid_algebra.lift ℤ G (((fin i → G) →₀ ℤ) →+ ((fin i → G) →₀ ℤ))
    (_ : G →* (((fin i → G) →₀ ℤ) →+ ((fin i → G) →₀ ℤ))),
  exact { to_fun := λ g, (add_equiv.of_finsupp_and_equiv
            ((equiv_comap_or_something _
              (left_translation_equiv g)) : (fin i → G) ≃ (fin i → G))).to_add_monoid_hom,
          map_one' := by { ext φ ψ, simp },
          map_mul' := λ g₁ g₂, begin ext φ₁ φ₂, simp end,
  },
end,
  map_one' := begin
    simp,
  end,
  map_mul' := begin
    simp,
  end,
  map_zero' := begin
    simp,
  end,
  map_add' := begin
    simp,
  end }

-- what I want
example (G : Type*) [group G] (A : Type*) [add_comm_group A] :
module (monoid_algebra ℤ G) A ≃ distrib_mul_action G A := sorry


-- this would do I guess
example (G : Sort*) [group G] (A : Sort*) [add_comm_group A] (R : Sort*) [comm_ring R] :
module (monoid_algebra R G) A ≃ module R A × distrib_mul_action G A := sorry

instance group_ring_module : module (monoid_algebra ℤ G) ((fin i → G) →₀ ℤ) :=
begin
  sorry
  -- apply some instances which I want and which I don't know if they're there
end

--{ι : Type*} (b : basis ι R P)

end finsupp
