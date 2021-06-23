import representation_theory.basic
import linear_algebra.dimension

open_locale big_operators

section

set_option old_structure_cmd true

/--
A homomorphism between representations is a linear map that commutes with the action by G.
-/
structure repre_hom
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M]
  [repre k G M]
  (M₂ : Type*) [add_comm_monoid M₂] [module k M₂]
  [repre k G M₂]
  extends M →ₗ[k] M₂ :=
(map_smul2' : ∀ (g : G) (x : M), to_fun (g • x) = g • to_fun x)

end

infixr ` →ᵣ `:25 := repre_hom _ _
notation M ` →ᵣ[`:25 k:25 `;`:25 G:25 `] `:0 M₂:0 := repre_hom k G M M₂

/-
Copy defs and lemmas from linear_map and linear_equiv:
https://github.com/leanprover-community/mathlib/blob/461b444d065e1747f1bda60070b4b5d6a3026fb2/src/algebra/module/linear_map.lean
-/

namespace repre_hom

section add_comm_monoid

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]

def of_linear_map (f : M →ₗ[k] M₂) (h : ∀ (g : G) (x : M), f (g • x) = g • f x) : M →ᵣ[k;G] M₂ := ⟨f.1, f.2, f.3, h⟩

instance : has_coe (M →ᵣ[k;G] M₂) (M →ₗ[k] M₂) := ⟨to_linear_map⟩

instance : has_coe_to_fun (M →ᵣ[k;G] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : M → M₂) (h₁ h₂ h₃) :
  ((repre_hom.mk f h₁ h₂ h₃ : M →ᵣ[k;G] M₂) : M → M₂) = f := rfl

/-- Identity map as a `repre_hom` -/
def id : M →ᵣ[k;G] M :=
⟨id, λ _ _, rfl, λ _ _, rfl, λ _ _, rfl⟩

lemma id_apply (x : M) :
  @id k G M _ _ _ _ _ x = x := rfl

@[simp, norm_cast] lemma id_coe : ((repre_hom.id : M →ᵣ[k;G] M) : M → M) = _root_.id := by { ext x, refl }

@[simp] lemma to_fun_eq_coe (f : M →ᵣ[k;G] M₂) : f.to_fun = ⇑f := rfl

theorem coe_injective : function.injective (λ f : M →ᵣ[k;G] M₂, show M → M₂, from f) :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] theorem ext {f g : M →ᵣ[k;G] M₂} (H : ∀ x, f x = g x) : f = g :=
coe_injective $ funext H

protected lemma congr_arg {f : M →ᵣ[k;G] M₂} : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

/-- If two linear maps are equal, they are equal at each point. -/
protected lemma congr_fun {f g : M →ᵣ[k;G] M₂} (h : f = g) (x : M) : f x = g x := h ▸ rfl

theorem ext_iff {f g : M →ᵣ[k;G] M₂} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

@[simp] lemma mk_coe (f : M →ᵣ[k;G] M₂) (h₁ h₂ h₃) :
  (repre_hom.mk f h₁ h₂ h₃ : M →ᵣ[k;G] M₂) = f := ext $ λ _, rfl

@[simp] lemma map_add (f : M →ᵣ[k;G] M₂) (x y : M) : f (x + y) = f x + f y := f.map_add' x y

@[simp] lemma map_smul (f : M →ᵣ[k;G] M₂) (c : k) (x : M) : f (c • x) = c • f x := f.map_smul' c x

@[simp] lemma map_smul2 (f : M →ᵣ[k;G] M₂) (g : G) (x : M) : f (g • x) = g • f x := f.map_smul2' g x

@[simp] lemma map_zero (f : M →ᵣ[k;G] M₂) : f 0 = 0 :=
f.to_linear_map.map_zero

@[simp] lemma map_eq_zero_iff (f : M →ᵣ[k;G] M₂) (h : function.injective f) {x : M} : f x = 0 ↔ x = 0 :=
⟨λ w, by { apply h, simp [w], }, λ w, by { subst w, simp, }⟩

@[simp] lemma to_linear_map_coe (f : M →ᵣ[k;G] M₂) : ⇑f.to_linear_map = f := rfl

@[simp] lemma map_sum (f : M →ᵣ[k;G] M₂) {ι} {t : finset ι} {x : ι → M} :
  f (∑ i in t, x i) = (∑ i in t, f (x i)) :=
by {rw ←to_linear_map_coe, apply f.to_linear_map.map_sum}

section

variables
  {M₃ : Type*} [add_comm_monoid M₃] [module k M₃] [repre k G M₃]
  (f : M₂ →ᵣ[k;G] M₃) (g : M →ᵣ[k;G] M₂)

/-- Composition of two repre_hom is a repre_hom -/
def comp : M →ᵣ[k;G] M₃ := ⟨f ∘ g, by simp, by simp, by simp⟩

lemma comp_apply (x : M) : f.comp g x = f (g x) := rfl

@[simp, norm_cast] lemma coe_comp : (f.comp g : M → M₃) = f ∘ g := rfl

@[simp] theorem comp_id : f.comp id = f :=
repre_hom.ext $ λ x, rfl

@[simp] theorem id_comp : id.comp f = f :=
repre_hom.ext $ λ x, rfl

variables {M₄ : Type*} [add_comm_monoid M₄] [module k M₄] [repre k G M₄]

theorem comp_assoc (e : M₃ →ᵣ[k;G] M₄) : (e.comp f).comp g = e.comp (f.comp g) :=
rfl

/- dom_restrict, etc, and algebraic structure of repre_hom from linear_algebra.basic -/

/-- 0 map as a repre_hom -/
instance : has_zero (M →ᵣ[k;G] M₂) := ⟨of_linear_map 0 (by simp)⟩

instance : inhabited (M →ᵣ[k;G] M₂) := ⟨0⟩

@[simp] lemma zero_apply (x : M) : (0 : M →ᵣ[k;G] M₂) x = 0 := rfl

@[simp] theorem comp_zero : f.comp (0 : M →ᵣ[k;G] M₂) = 0 :=
ext $ assume c, by rw [comp_apply, zero_apply, zero_apply, f.map_zero]

@[simp] theorem zero_comp : (0 : M₂ →ᵣ[k;G] M₃).comp g = 0 :=
rfl

/-- 1 is the identity repre_hom -/
instance : has_one (M →ᵣ[k;G] M) := ⟨repre_hom.id⟩

lemma one_eq_id : (1 : M →ᵣ[k;G] M) = id := rfl

@[simp] lemma one_apply (x : M) : (1 : M →ᵣ[k;G] M) x = x := rfl

lemma coe_one : ⇑(1 : M →ᵣ[k;G] M) = _root_.id := rfl

end

end add_comm_monoid

section add_comm_group

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_group M] [module k M] [repre k G M]
  [add_comm_group M₂] [module k M₂] [repre k G M₂]

@[simp] lemma map_neg (f : M →ᵣ[k;G] M₂) (x : M) : f (- x) = - f x :=
f.to_linear_map.to_add_monoid_hom.map_neg x

@[simp] lemma map_sub (f : M →ᵣ[k;G] M₂) (x y : M) : f (x - y) = f x - f y :=
f.to_linear_map.to_add_monoid_hom.map_sub x y

end add_comm_group

end repre_hom

section

set_option old_structure_cmd true

structure repre_iso
  (k : Type*) [semiring k]
  (G : Type*) [monoid G]
  (M : Type*) [add_comm_monoid M] [module k M]
  [repre k G M]
  (M₂ : Type*) [add_comm_monoid M₂] [module k M₂]
  [repre k G M₂]
  extends M ≃ₗ[k] M₂ :=
(map_smul2' : ∀ (g : G) (x : M), to_fun (g • x) = g • to_fun x)

end

infixr ` ≃ᵣ `:25 := repre_iso _ _
notation M ` ≃ᵣ[`:25 k:25 `;`:25 G:25 `] `:0 M₂:0 := repre_iso k G M M₂

namespace repre_iso

section add_comm_monoid

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]

def of_linear_equiv (f : M ≃ₗ[k] M₂) (h : ∀ (g : G) (x : M), f (g • x) = g • f x) : M ≃ᵣ[k;G] M₂ := ⟨f.1, f.2, f.3, f.4, f.5, f.6, h⟩

instance : has_coe (M ≃ᵣ[k;G] M₂) (M ≃ₗ[k] M₂) := ⟨to_linear_equiv⟩

def to_repre_hom (f : M ≃ᵣ[k;G] M₂) : M →ᵣ[k;G] M₂ := repre_hom.of_linear_map f f.7

instance : has_coe (M ≃ᵣ[k;G] M₂) (M →ᵣ[k;G] M₂) := ⟨to_repre_hom⟩

instance : has_coe_to_fun (M ≃ᵣ[k;G] M₂) := ⟨_, to_fun⟩

@[simp] lemma coe_mk {to_fun inv_fun map_add map_smul left_inv right_inv map_smul2} :
  ⇑(⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv, map_smul2⟩ : M ≃ᵣ[k;G] M₂) = to_fun := rfl

@[simp] lemma coe_mk_to_repre_hom {to_fun inv_fun map_add map_smul left_inv right_inv map_smul2} :
  ((⟨to_fun, map_add, map_smul, inv_fun, left_inv, right_inv, map_smul2⟩ : (M ≃ᵣ[k;G] M₂)) : (M →ᵣ[k;G] M₂)) = ⟨to_fun, map_add, map_smul, map_smul2⟩ := rfl

@[simp] lemma to_linear_equiv_coe (f : M ≃ᵣ[k;G] M₂) : ⇑f.to_linear_equiv = f := rfl

def to_equiv : (M ≃ᵣ[k;G] M₂) → M ≃ M₂ := λ f, ⟨f, f.inv_fun, f.left_inv, f.right_inv⟩

lemma to_equiv_injective : function.injective (to_equiv : (M ≃ᵣ[k;G] M₂) → M ≃ M₂) :=
λ ⟨_, _, _, _, _, _, _⟩ ⟨_, _, _, _, _, _, _⟩ h, repre_iso.mk.inj_eq.mpr (equiv.mk.inj h)

@[simp] lemma to_equiv_inj {e₁ e₂ : M ≃ᵣ[k;G] M₂} : e₁.to_equiv = e₂.to_equiv ↔ e₁ = e₂ :=
to_equiv_injective.eq_iff

lemma to_repre_hom_injective : function.injective (coe : (M ≃ᵣ[k;G] M₂) → (M →ᵣ[k;G] M₂)) :=
λ e₁ e₂ H, to_equiv_injective $ equiv.ext $ repre_hom.congr_fun H

@[simp, norm_cast] lemma to_repre_hom_inj {e₁ e₂ : M ≃ᵣ[k;G] M₂} :
  (e₁ : M →ᵣ[k;G] M₂) = e₂ ↔ e₁ = e₂ :=
to_repre_hom_injective.eq_iff

@[simp] lemma to_repre_hom_eq_coe (f : M ≃ᵣ[k;G] M₂) : f.to_repre_hom = ↑f := rfl

@[simp, norm_cast] theorem coe_coe (e : M ≃ᵣ[k;G] M₂) : ⇑(e : M →ᵣ[k;G] M₂) = e := rfl

@[simp] lemma coe_to_equiv (e : M ≃ᵣ[k;G] M₂) : ⇑e.to_equiv = e := rfl

@[simp] lemma coe_to_repre_hom (e : M ≃ᵣ[k;G] M₂) : ⇑e.to_repre_hom = e := rfl

@[simp] lemma to_fun_eq_coe (e : M ≃ᵣ[k;G] M₂) : e.to_fun = e := rfl

section

variables {e e' : M ≃ᵣ[k;G] M₂}

@[ext] lemma ext (h : ∀ x, e x = e' x) : e = e' :=
to_equiv_injective (equiv.ext h)

protected lemma congr_arg : Π {x x' : M}, x = x' → e x = e x'
| _ _ rfl := rfl

protected lemma congr_fun (h : e = e') (x : M) : e x = e' x := h ▸ rfl

lemma ext_iff : e = e' ↔ ∀ x, e x = e' x :=
⟨λ h x, h ▸ rfl, ext⟩

end

/-- The identity map is a repre_iso. -/
@[refl]
def refl
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M] : M ≃ᵣ[k;G] M :=
{ .. repre_hom.id, .. equiv.refl M }

@[simp] lemma refl_apply (x : M) : refl k G M x = x := rfl

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ᵣ[k;G] M₂) : M₂ ≃ᵣ[k;G] M :=
{ map_smul2' := by
  { intros,
  simp,
  rw ←linear_equiv.symm_apply_apply e.to_linear_equiv (g • e.to_linear_equiv.symm x),
  rw [to_linear_equiv_coe, ←to_fun_eq_coe, e.map_smul2', to_fun_eq_coe, ←to_linear_equiv_coe, linear_equiv.apply_symm_apply] },
.. e.to_linear_equiv.symm }

@[simp] lemma inv_fun_eq_symm (e : M ≃ᵣ[k;G] M₂) : e.inv_fun = e.symm := rfl

variables
  {M₃ : Type*} [add_comm_monoid M₃] [module k M₃] [repre k G M₃]

/-- Linear equivalences are transitive. -/
@[trans]
def trans (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) : M ≃ᵣ[k;G] M₃ :=
{ .. g.to_repre_hom.comp f.to_repre_hom,
  .. f.to_equiv.trans g.to_equiv }

@[simp] theorem trans_apply (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) (c : M) :
  (f.trans g) c = g (f c) := rfl
@[simp] theorem apply_symm_apply (f : M ≃ᵣ[k;G] M₂) (c : M₂) : f (f.symm c) = c := f.6 c
@[simp] theorem symm_apply_apply (f : M ≃ᵣ[k;G] M₂) (b : M) : f.symm (f b) = b := f.5 b
@[simp] lemma symm_trans_apply (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) (c : M₃) : (f.trans g).symm c = f.symm (g.symm c) := rfl

@[simp] lemma trans_refl (f : M ≃ᵣ[k;G] M₂) : f.trans (refl k G M₂) = f := to_equiv_injective f.to_equiv.trans_refl
@[simp] lemma refl_trans (f : M ≃ᵣ[k;G] M₂) : (refl k G M).trans f = f := to_equiv_injective f.to_equiv.refl_trans

lemma symm_apply_eq (f : M ≃ᵣ[k;G] M₂) {x y} : f.symm x = y ↔ x = f y := f.to_equiv.symm_apply_eq
lemma eq_symm_apply (f : M ≃ᵣ[k;G] M₂) {x y} : y = f.symm x ↔ f y = x := f.to_equiv.eq_symm_apply

@[simp] lemma refl_symm : (refl k G M).symm = refl k G M := rfl

@[simp] lemma trans_symm (f : M ≃ᵣ[k;G] M₂) :
  f.trans f.symm = repre_iso.refl k G M :=
by { ext x, simp }

@[simp] lemma symm_trans (f : M ≃ᵣ[k;G] M₂) :
  f.symm.trans f = repre_iso.refl k G M₂ :=
by { ext x, simp }

@[simp, norm_cast] lemma refl_to_repre_hom :
  (repre_iso.refl k G M : M →ᵣ[k;G] M) = repre_hom.id :=
rfl

@[simp, norm_cast]
lemma comp_coe (f : M ≃ᵣ[k;G] M₂) (g : M₂ ≃ᵣ[k;G] M₃) : (g : M₂ →ᵣ[k;G] M₃).comp (f : M →ᵣ[k;G] M₂) = (f.trans g : M →ᵣ[k;G] M₃) :=
rfl

@[simp] lemma mk_coe (e : M ≃ᵣ[k;G] M₂) (h₁ h₂ f h₃ h₄ h₅) :
  (repre_iso.mk e h₁ h₂ f h₃ h₄ h₅ : M ≃ᵣ[k;G] M₂) = e := ext $ λ _, rfl

@[simp] theorem map_add (e : M ≃ᵣ[k;G] M₂) (a b : M) : e (a + b) = e a + e b := e.map_add' a b
@[simp] theorem map_zero (e : M ≃ᵣ[k;G] M₂) : e 0 = 0 := e.to_repre_hom.map_zero
@[simp] theorem map_smul (e : M ≃ᵣ[k;G] M₂) (c : k) (x : M) : e (c • x) = c • e x := e.map_smul' c x
@[simp] theorem map_smul2 (e : M ≃ᵣ[k;G] M₂) (g : G) (x : M) : e (g • x) = g • e x := e.map_smul2' g x

@[simp] lemma map_sum (e : M ≃ᵣ[k;G] M₂) {ι} {s : finset ι} (u : ι → M) : e (∑ i in s, u i) = ∑ i in s, e (u i) :=
e.to_repre_hom.map_sum

@[simp] theorem map_eq_zero_iff (e : M ≃ᵣ[k;G] M₂) {x : M} : e x = 0 ↔ x = 0 :=
e.to_linear_equiv.map_eq_zero_iff
theorem map_ne_zero_iff (e : M ≃ᵣ[k;G] M₂) {x : M} : e x ≠ 0 ↔ x ≠ 0 :=
e.to_linear_equiv.map_ne_zero_iff

@[simp] theorem symm_symm (e : M ≃ᵣ[k;G] M₂) : e.symm.symm = e := by { cases e, refl }

lemma symm_bijective : function.bijective (symm : (M ≃ᵣ[k;G] M₂) → (M₂ ≃ᵣ[k;G] M)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp] lemma mk_coe' (e : M ≃ᵣ[k;G] M₂) (f h₁ h₂ h₃ h₄ h₅) :
  (repre_iso.mk f h₁ h₂ ⇑e h₃ h₄ h₅ : M₂ ≃ᵣ[k;G] M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[simp] theorem symm_mk (e : M ≃ᵣ[k;G] M₂) (f h₁ h₂ h₃ h₄ h₅) :
  (⟨e, h₁, h₂, f, h₃, h₄, h₅⟩ : M ≃ᵣ[k;G] M₂).symm =
  { to_fun := f, inv_fun := e,
    ..(⟨e, h₁, h₂, f, h₃, h₄, h₅⟩ : M ≃ᵣ[k;G] M₂).symm } := rfl

protected lemma bijective (e : M ≃ᵣ[k;G] M₂) : function.bijective e := e.to_equiv.bijective
protected lemma injective (e : M ≃ᵣ[k;G] M₂) : function.injective e := e.to_equiv.injective
protected lemma surjective (e : M ≃ᵣ[k;G] M₂) : function.surjective e := e.to_equiv.surjective
protected lemma image_eq_preimage (e : M ≃ᵣ[k;G] M₂) (s : set M) : e '' s = e.symm ⁻¹' s :=
e.to_equiv.image_eq_preimage s










end add_comm_monoid

-- section add_comm_group

-- variables
--   {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*}
--   [semiring k] [monoid G]
--   [add_comm_group M] [module k M] [repre k G M]
--   [add_comm_group M₂] [module k M₂] [repre k G M₂]

-- end add_comm_group

end repre_iso

/-
TODO : Show repre_hom and repre_iso give hom and iso between the monoid_hom algebras
-/

namespace subrepre

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]

/-- The pushforward of a subrepresentation `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) : subrepre k G M₂ :=
{ smul_mem :=
  begin
    intros g x₂,
    simp,
    intros x h1 h2,
    existsi g • x,
    split,
    { apply p.smul_mem,
      simp,
      exact h1 },
    { simp,
      rw h2 }
  end,
  .. p.to_submodule.map f.to_linear_map }

@[simp] lemma map_coe (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) :
  (map f p : set M₂) = f '' p := rfl

@[simp] lemma mem_map {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {r} (h : r ∈ p) : f r ∈ map f p :=
set.mem_image_of_mem _ h

lemma apply_coe_mem_map (f : M →ᵣ[k;G] M₂) {p : subrepre k G M} (r : p) : f r ∈ map f p :=
mem_map_of_mem r.prop

@[simp] lemma map_id (p : subrepre k G M) : map repre_hom.id p = p :=
subrepre.ext $ λ a, by simp

lemma map_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) (p : subrepre k G M) :
  map (g.comp f) p = map g (map f p) :=
set_like.coe_injective $ by simp [map_coe]; rw ← set.image_comp

lemma map_mono {f : M →ᵣ[k;G] M₂} {p p' : subrepre k G M} : p ≤ p' → map f p ≤ map f p' :=
set.image_subset _

@[simp] lemma map_zero_eq_bot (p : subrepre k G M) : map (0 : M →ᵣ[k;G] M₂) p = ⊥ :=
begin
  have : ∃ (x : M), x ∈ p,
  { existsi (0 : M), simp },
  ext,
  simp [this, eq_comm]
end

/- range_map_nonempty skipped -/

/-- Canonical embedding of a subrepresentation as a repre_hom. -/
protected def subtype (p : subrepre k G M) : p →ᵣ[k;G] M :=
begin
  refine ⟨coe, _, _, _⟩,
  {simp},
  {apply subrepre.coe_smul},
  {apply subrepre.coe_smul2}
end

@[simp] theorem subtype_apply (p : subrepre k G M) (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val (p : subrepre k G M) : ((subrepre.subtype p) : p → M) = subtype.val := rfl

/-- An injective repre_hom gives a repre_iso between the domain and the range. -/
@[simps]
noncomputable def equiv_map_of_injective (f : M →ᵣ[k;G] M₂) (i : function.injective f) (p : subrepre k G M) :
  p ≃ᵣ[k;G] p.map f :=
{ map_add' := by { intros, simp, refl },
  map_smul' := by { intros, simp [subrepre.coe_smul], refl },
  map_smul2' := by { intros, simp [subrepre.coe_smul2], refl },
  ..(equiv.set.image f p i) }

/-- The pullback of a subrepresentation `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ᵣ[k;G] M₂) (p : subrepre k G M₂) : subrepre k G M :=
{ carrier   := f ⁻¹' p,
  smul_mem := by
  { intros g x,
    simp,
    apply smul_mem },
  .. p.to_submodule.comap f.to_linear_map }

@[simp] lemma comap_coe (f : M →ᵣ[k;G] M₂) (p : subrepre k G M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M₂} :
  ∀ x, x ∈ comap f p ↔ f x ∈ p := λ x, iff.rfl

lemma comap_id (p : subrepre k G M) : comap repre_hom.id p = p :=
set_like.coe_injective rfl

lemma comap_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) (p : subrepre k G M₃) :
  comap (g.comp f) p = comap f (comap g p) := rfl

lemma comap_mono {f : M →ᵣ[k;G] M₂} {q q' : subrepre k G M₂} : q ≤ q' → comap f q ≤ comap f q' :=
set.preimage_mono

lemma map_le_iff_le_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} {q : subrepre k G M₂} :
  map f p ≤ q ↔ p ≤ comap f q := set.image_subset_iff

lemma gc_map_comap (f : M →ᵣ[k;G] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ᵣ[k;G] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (p p' : subrepre k G M) (f : M →ᵣ[k;G] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ᵣ[k;G] M₂) (p : ι → subrepre k G M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

@[simp] lemma comap_top (f : M →ᵣ[k;G] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (q q' : subrepre k G M₂) (f : M →ᵣ[k;G] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi {ι : Sort*} (f : M →ᵣ[k;G] M₂) (p : ι → subrepre k G M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero (q : subrepre k G M₂) : comap (0 : M →ᵣ[k;G] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le (f : M →ᵣ[k;G] M₂) (q : subrepre k G M₂) : map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map (f : M →ᵣ[k;G] M₂) (p : subrepre k G M) : p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

/- TODO: galois, finsupp, dfinsupp, etc from linear_algebra.basic -/


end subrepre

namespace repre_hom

variables
  {k : Type*} {G : Type*} {M : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring k] [monoid G]
  [add_comm_monoid M] [module k M] [repre k G M]
  [add_comm_monoid M₂] [module k M₂] [repre k G M₂]
  [add_comm_monoid M₃] [module k M₃] [repre k G M₃]

/-- The range of a repre_hom `f : M → M₂` is a subrepresentation of `M₂`. -/
def range (f : M →ᵣ[k;G] M₂) : subrepre k G M₂ :=
(subrepre.map f ⊤).copy (set.range f) set.image_univ.symm

theorem range_coe (f : M →ᵣ[k;G] M₂) : (range f : set M₂) = set.range f := rfl

@[simp] theorem mem_range {f : M →ᵣ[k;G] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
iff.rfl

lemma range_eq_map (f : M →ᵣ[k;G] M₂) : f.range = subrepre.map f ⊤ :=
by { ext, simp }

theorem mem_range_self (f : M →ᵣ[k;G] M₂) (x : M) : f x ∈ f.range := ⟨x, rfl⟩

@[simp] theorem range_id : range (repre_hom.id : M →ᵣ[k;G] M) = ⊤ :=
set_like.coe_injective set.range_id

theorem range_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : range (g.comp f) = subrepre.map g (range f) :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : range (g.comp f) ≤ range g :=
set_like.coe_mono (set.range_comp_subset_range f g)

theorem range_eq_top {f : M →ᵣ[k;G] M₂} : range f = ⊤ ↔ function.surjective f :=
by rw [set_like.ext'_iff, range_coe, subrepre.top_coe, set.range_iff_surjective]

lemma range_le_iff_comap {f : M →ᵣ[k;G] M₂} {p : subrepre k G M₂} : range f ≤ p ↔ subrepre.comap f p = ⊤ :=
by rw [range_eq_map, subrepre.map_le_iff_le_comap, eq_top_iff]

lemma map_le_range {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} : subrepre.map f p ≤ range f :=
set_like.coe_mono (set.image_subset_range f p)

/- TODO: more from linear_algebra.basic -/

/-- The kernel of a repre_hom `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the set of `x : M` such that `f x = 0`. The kernel is a subrepresentation of `M`. -/
def ker (f : M →ᵣ[k;G] M₂) : subrepre k G M := subrepre.comap f ⊥

@[simp] theorem mem_ker {f : M →ᵣ[k;G] M₂} {y} : y ∈ ker f ↔ f y = 0 := by apply subrepre.mem_comap

@[simp] theorem ker_id : ker (repre_hom.id : M →ᵣ[k;G] M) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : M →ᵣ[k;G] M₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

lemma comp_ker_subtype (f : M →ᵣ[k;G] M₂) : f.comp f.ker.subtype = 0 :=
repre_hom.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

theorem ker_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : ker (g.comp f) = subrepre.comap f (ker g) := rfl

theorem ker_le_ker_comp (f : M →ᵣ[k;G] M₂) (g : M₂ →ᵣ[k;G] M₃) : ker f ≤ ker (g.comp f) := by {rw ker_comp, exact subrepre.comap_mono bot_le}

/- Need disjoint_def, etc -/
-- theorem disjoint_ker {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} :
--   disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
-- by simp [disjoint_def]

-- theorem ker_eq_bot' {f : M →ᵣ[k;G] M₂} :
--   ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
-- by simpa [disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ f ⊤

-- theorem ker_eq_bot_of_inverse {f : M →ᵣ[k;G] M₂} {g : M₂ →ᵣ[k;G] M} (h : g.comp f = id) :
--   ker f = ⊥ :=
-- ker_eq_bot'.2 $ λ m hm, by rw [← id_apply m, ← h, comp_apply, hm, g.map_zero]

lemma le_ker_iff_map {f : M →ᵣ[k;G] M₂} {p : subrepre k G M} : p ≤ ker f ↔ subrepre.map f p = ⊥ :=
by rw [ker, eq_bot_iff, subrepre.map_le_iff_le_comap]

-- lemma ker_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (hf) :
--   ker (cod_restrict p f hf) = ker f :=
-- by rw [ker, comap_cod_restrict, map_bot]; refl

-- lemma range_cod_restrict (p : subrepre k G M) (f : M₂ →ᵣ[k;G] M) (hf) :
--   range (cod_restrict p f hf) = comap p.subtype f.range :=
-- by simpa only [range_eq_map] using map_cod_restrict _ _ _ _

-- lemma ker_restrict {p : subrepre k G M} {f : M →ᵣ[k;G] M} (hf : ∀ x : M, x ∈ p → f x ∈ p) :
--   ker (f.restrict hf) = (f.dom_restrict p).ker :=
-- by rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

lemma map_comap_eq (f : M →ᵣ[k;G] M₂) (q : subrepre k G M₂) :
  subrepre.map f (subrepre.comap f q) = range f ⊓ q :=
le_antisymm (le_inf map_le_range (subrepre.map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma map_comap_eq_self {f : M →ᵣ[k;G] M₂} {q : subrepre k G M₂} (h : q ≤ range f) :
  subrepre.map f (subrepre.comap f q) = q :=
by rwa [map_comap_eq, inf_eq_right]

@[simp] theorem ker_zero : ker (0 : M →ᵣ[k;G] M₂) = ⊤ :=
subrepre.eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero : range (0 : M →ᵣ[k;G] M₂) = ⊥ :=
by simp [range_eq_map]

theorem ker_eq_top {f : M →ᵣ[k;G] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

lemma range_le_bot_iff (f : M →ᵣ[k;G] M₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : M →ᵣ[k;G] M₂} : range f = ⊥ ↔ f = 0 :=
by rw [← range_le_bot_iff, le_bot_iff]

-- lemma range_le_ker_iff {f : M →ᵣ[k;G] M₂} {g : M₂ →ᵣ[k;G] M₃} : range f ≤ ker g ↔ g.comp f = 0 :=
-- ⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, h $ ⟨_, rfl⟩,
--  λ h x hx, mem_ker.2 $ exists.elim hx $ λ y hy, by rw [←hy, ←comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : M →ᵣ[k;G] M₂} (hf : range f = ⊤) {p p'} :
  subrepre.comap f p ≤ subrepre.comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, subrepre.comap_mono⟩

theorem comap_injective {f : M →ᵣ[k;G] M₂} (hf : range f = ⊤) : function.injective (subrepre.comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h))
  ((comap_le_comap_iff hf).1 (ge_of_eq h))

-- theorem ker_eq_bot_of_injective {f : M →ᵣ[k;G] M₂} (hf : function.injective f) : ker f = ⊥ :=
-- begin
--   have : disjoint ⊤ f.ker, by { rw [disjoint_ker, ← map_zero f], exact λ x hx H, hf H },
--   simpa [disjoint]
-- end

end repre_hom

namespace schur

open repre_hom

variables
  {k : Type*} [ring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_group M] [module k M] [nontrivial M]
  [repre k G M]
  {M₂ : Type*} [add_comm_group M₂] [module k M₂] [nontrivial M₂]
  [repre k G M₂] (φ : M →ᵣ[k;G] M₂)

/- TODO: simplify these proofs using repre_hom's ker_eq_bot-/
lemma injective (h : φ ≠ 0) : is_irreducible k G M → function.injective φ :=
begin
  have hneq : φ.ker ≠ ⊤,
  { simp [ker_eq_top], exact h },
  intro irr,
  have heq_bot := irr φ.ker,
  simp [hneq] at heq_bot,
  have : φ.to_linear_map.ker = ⊥,
  { ext, simp, split,
    { intro hh,
      have : x ∈ φ.ker,
      { simp, exact hh },
      simp [heq_bot] at this,
      exact this },
    intro hh,
    simp [hh] },
  rw ←to_linear_map_coe,
  apply linear_map.ker_eq_bot.mp this
end

lemma surjective (h : φ ≠ 0) : is_irreducible k G M₂ → function.surjective φ :=
begin
  have hneq : φ.range ≠ ⊥,
  { simp [range_eq_bot], exact h },
  intro irr,
  have heq_top := irr φ.range,
  simp [hneq] at heq_top,
  apply range_eq_top.mp heq_top
end

end schur

/- TODO: simplify by repre_hom.of_bijective -/
/-- A non-zero repre_hom between irreducible representations is a repre_iso. -/
noncomputable lemma schur
  {k : Type*} [ring k]
  {G : Type*} [monoid G]
  {M : Type*} [add_comm_group M] [module k M] [nontrivial M]
  [repre k G M]
  {M₂ : Type*} [add_comm_group M₂] [module k M₂] [nontrivial M₂]
  [repre k G M₂] (φ : M →ᵣ[k;G] M₂) (h : φ ≠ 0) :
  is_irreducible k G M → is_irreducible k G M₂ → M ≃ᵣ[k;G] M₂ :=
begin
  intros irr irr₂,
  apply repre_iso.of_linear_equiv,
  show M ≃ₗ[k] M₂,
  { apply linear_equiv.of_bijective,
    show M →ₗ[k] M₂,
    { exact φ.to_linear_map },
    { apply linear_map.ker_eq_bot.mpr,
      rw repre_hom.to_linear_map_coe φ,
      exact schur.injective φ h irr },
    { apply linear_map.range_eq_top.mpr,
      rw repre_hom.to_linear_map_coe φ,
      exact schur.surjective φ h irr₂ } },
  intros,
  simp
end

-- example
--   {k : Type*} [ring k]
--   {G : Type*} [comm_monoid G]
--   {M : Type*} [add_comm_group M] [module k M] [nontrivial M]
--   [repre k G M] : module.rank M = 1 :=
-- begin

-- end