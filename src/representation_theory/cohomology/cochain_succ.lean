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

namespace group_cohomology

universes v u
example (n : ℕ) : (n + 1) + 1 = n + (1 + 1) := rfl

#check chain_complex
#check int.add_sub_cancel
def homog_cochain {k : Type*} [comm_ring k] {G : Type*} [group G] {V : Type*} [add_comm_group V]
  [module k V] (ρ : representation k G V) (n : ℕ) :
  submodule k ((fin n → G) → V) :=
{ carrier := {f | ∀ (s : G) (g : fin n → G), ρ s (f g) = f (λ i, s * g i)},
  add_mem' := λ a b ha hb s g, by dsimp; rw [(ρ s).map_add, ha s g, hb s g]; refl,
  zero_mem' := λ s g, (ρ s).map_zero,
  smul_mem' := λ c f hf s g, by dsimp; rw [(ρ s).map_smul, hf s g] }

namespace homog_cochain
section

variables {k : Type*} [comm_ring k] {G : Type*} [group G] {V : Type*} [add_comm_group V]
  [module k V] (ρ : representation k G V) (n : ℕ)

variables {ρ n}
instance : has_coe_to_fun (homog_cochain ρ n) (λ _, (fin n → G) → V) := ⟨coe⟩

@[simp] lemma coe_apply (c : (fin n → G) → V)
  (hc : ∀ (s : G) (g : fin n → G), ρ s (c g) = c (λ i, s * g i)) (g : fin n → G) :
  (⟨c, hc⟩ : homog_cochain ρ n) g = c g := rfl

--hm
@[ext] theorem ext' (c₁ c₂ : homog_cochain ρ n) (h : ∀ g : fin n → G, c₁ g = c₂ g) : c₁ = c₂ :=
by ext; exact h _

theorem ext_iff' (c₁ c₂ : homog_cochain ρ n) : c₁ = c₂ ↔ ∀ g : fin n → G, c₁ g = c₂ g :=
⟨λ h x, h ▸ rfl, ext' _ _⟩

@[simps] def d_aux {i j : ℕ} (hj : j = i + 1) (c : homog_cochain ρ i) : homog_cochain ρ j :=
{ val := λ g, (finset.range j).sum (λ p, (-1 : k) ^ p • c $ λ t, g (fin.delta hj p t)),
  property :=
  begin
    intros s g,
    dsimp,
    rw linear_map.map_sum,
    refine finset.sum_congr rfl (λ x hx, _),
    erw [linear_map.map_smul (ρ s) ((-1 : k) ^ x), c.2 s (g ∘ fin.delta hj x)],
    refl,
  end }

variables (ρ)

def d {i j : ℕ} (hj : j = i + 1) : homog_cochain ρ i →ₗ[k] homog_cochain ρ j :=
{ to_fun := d_aux hj,
  map_add' :=
  begin
    intros,
    dsimp [d_aux],
    ext,
    dsimp,
    simp only [smul_add, pi.add_apply, ←finset.sum_add_distrib],
    refl,
  end,
  map_smul' :=
  begin
    intros,
    dsimp [d_aux],
    ext,
    dsimp,
    simp only [←mul_smul, mul_comm _ r],
    simp only [mul_smul],
    erw ←finset.smul_sum,
    congr,
  end }

lemma d_eval {i j : ℕ} (hj : j = i + 1) (c : homog_cochain ρ i) (g : fin j → G) :
  d ρ hj c g = (finset.range j).sum (λ p, (-1 : k)^p • c $ λ t, g $ fin.delta hj p t) := rfl

end
section
variables {k : Type u} [comm_ring k] [nontrivial k] {G : Type u} [group G] {V : Type u}
  [add_comm_group V] [module k V] (ρ : representation k G V) (n : ℕ)

variables {i j : ℕ} (hj : j = i + 1) (c : homog_cochain ρ i) (g : fin j → G)

theorem total_d_eq_d :
  finsupp.total (fin i → G) V k c (Rep.d_hom k G hj (finsupp.single g (1 : k))) = d ρ hj c g :=
begin
  simp only [d_eval, Rep.d_hom_of, Rep.d_aux_eq, linear_map.map_sum, finsupp.total_single],
  refl,
end

theorem d_squared_eq_zero {i j l : ℕ} (hj : j = i + 1) (hl : l = j + 1) (c : homog_cochain ρ i) :
  d ρ hl (d ρ hj c) = 0 :=
begin
  ext g,
  suffices : d ρ hl (d ρ hj c) g = finsupp.total (fin i → G) V k c (Rep.d_hom k G hj
    (Rep.d_hom k G hl (finsupp.single g (1 : k)))),
  by rwa [Rep.d_hom_squared, map_zero] at this,
  rw [←total_d_eq_d, Rep.d_hom_of, finsupp.total_apply, finsupp.total_apply,
    Rep.d_hom, finsupp.lift_apply, finsupp.sum_sum_index],
  { simp only [←total_d_eq_d, Rep.d_hom_of, ←finsupp.total_apply, linear_map.map_smul] },
  { exact (λ a, zero_smul _ _) },
  { exact (λ a r r', add_smul _ _ _) },
end

end
end homog_cochain
#exit
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
