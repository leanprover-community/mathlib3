/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import ring_theory.ideal.basic
import category_theory.preadditive.injective
import algebra.category.Module.abelian

/-!
# Injective modules

## Main definitions

* `module.injective`: an `R`-module `Q` is injective if and only if every injective `R`-linear
  map descends to a linear map to `Q`, i.e. in the following diagram, if `f` is injective then there
  is an `R`-linear map `h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
* `module.Baer`: an `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an
  `ideal R` extends to an `R`-linear map `R ⟶ Q`

## Main statements

* `module.Baer.criterion`: an `R`-module is injective if it is Baer.

-/


noncomputable theory

universes u v

variables (R : Type u) [ring R] (Q : Type (max u v)) [add_comm_group Q] [module R Q]

/--An `R`-module `Q` is injective if and only if every injective `R`-linear map descends to a linear
map to `Q`, i.e. in the following diagram, if `f` is injective then there is an `R`-linear map
`h : Y ⟶ Q` such that `g = h ∘ f`
  ```
  X --- f ---> Y
  |
  | g
  v
  Q
  ```
-/
class module.injective : Prop :=
(out : ∀ (X Y : Type (max u v)) [add_comm_group X] [add_comm_group Y] [module R X] [module R Y]
  (f : X →ₗ[R] Y) (hf : function.injective f) (g : X →ₗ[R] Q),
  ∃ (h : Y →ₗ[R] Q), ∀ x, h (f x) = g x)

lemma module.injective_object_of_injective_module [module.injective.{u v} R Q] :
  category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R) :=
{ factors := λ X Y g f mn, begin
    rcases module.injective.out X Y f ((Module.mono_iff_injective f).mp mn) g with ⟨h, eq1⟩,
    exact ⟨h, linear_map.ext eq1⟩,
  end }

lemma module.injective_module_of_injective_object
  [category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R)] :
  module.injective.{u v} R Q :=
{ out := λ X Y ins1 ins2 ins3 ins4 f hf g, begin
    resetI,
    rcases @category_theory.injective.factors (Module R) _ ⟨Q⟩ _ ⟨X⟩ ⟨Y⟩ g f
      ((Module.mono_iff_injective _).mpr hf) with ⟨h, eq1⟩,
    refine ⟨h, λ x, by rw ← eq1; refl⟩,
  end }

lemma module.injective_iff_injective_object :
  module.injective.{u v} R Q ↔ category_theory.injective.{max u v} (⟨Q⟩ : Module.{max u v} R) :=
⟨λ h, @@module.injective_object_of_injective_module R _ Q _ _ h,
 λ h, @@module.injective_module_of_injective_object R _ Q _ _ h⟩

/--An `R`-module `Q` satisfies Baer's criterion if any `R`-linear map from an `ideal R` extends to
an `R`-linear map `R ⟶ Q`-/
def module.Baer : Prop := ∀ (I : ideal R) (g : I →ₗ[R] Q), ∃ (g' : R →ₗ[R] Q),
  ∀ (x : R) (mem : x ∈ I), g' x = g ⟨x, mem⟩

namespace module.Baer

variables {R} {M N : Type (max u v)} [add_comm_group M] [add_comm_group N]
variables [module R M] [module R N] (i : M →ₗ[R] N) (f : M →ₗ[R] Q)
variable {Q}

/-- If we view `M` as a submodule of `N` via the injective linear map `i : M ↪ N`, then a submodule
between `M` and `N` is a submodule `N'` of `N`. To prove Baer's criterion, we need to consider
pairs of `(N', f')` such that `M ≤ N' ≤ N` and `f'` extends `f`. -/
structure extension_of extends linear_pmap R N Q :=
-- (le : i.range ≤ to_submodule)
(le : i.range ≤ domain)
-- (extension : to_submodule →ₗ[R] Q)
-- (is_extension: ∀ (m : M), f m = extension ⟨i m, le ⟨m, rfl⟩⟩)
(is_extension: ∀ (m : M), f m = to_fun ⟨i m, le ⟨m, rfl⟩⟩)

section ext

variables {i f}

@[ext] lemma extension_of.ext {a b : extension_of i f}
  (domain_eq : a.domain = b.domain)
  (to_fun_eq : ∀ x, a.to_fun x = b.to_fun ⟨x, domain_eq ▸ x.2⟩) :
  a = b :=
begin
  rcases a with ⟨a, a_le, e1⟩,
  rcases b with ⟨b, b_le, e2⟩,
  dsimp only at *,
  congr,
  refine linear_pmap.ext domain_eq to_fun_eq,
end

end ext

lemma extension_of.ext_iff (a b : extension_of i f) :
  a = b ↔ ∃ (domain_eq : a.domain = b.domain),
    ∀ x, a.to_fun x = b.to_fun ⟨x, domain_eq ▸ x.2⟩ :=
⟨λ r, r ▸ ⟨rfl, λ x, congr_arg a.to_fun $ subtype.ext_val rfl⟩,
  λ ⟨h1, h2⟩, extension_of.ext h1 h2⟩

variables (hi : function.injective i)

include hi
def extension_of.has_bot : has_bot (extension_of i f) :=
{ bot :=
  { domain := i.range,
    to_fun :=
    { to_fun := λ x, f x.2.some,
      map_add' := λ x y, begin
        have eq1  : _ + _ = (x + y).1 := congr_arg2 (+) x.2.some_spec y.2.some_spec,
        rw [← map_add, ← (x + y).2.some_spec] at eq1,
        rw [← hi eq1, map_add],
      end,
      map_smul' := λ r x, begin
        have eq1 : r • _ = (r • x).1 := congr_arg ((•) r) x.2.some_spec,
        rw [← linear_map.map_smul, ← (r • x).2.some_spec] at eq1,
        rw [ring_hom.id_apply, ← hi eq1, linear_map.map_smul],
      end },
    le := le_refl _,
    is_extension := λ m, begin
      simp only [linear_map.coe_mk],
      erw hi (⟨i m, ⟨_, rfl⟩⟩ : i.range).2.some_spec,
    end } }

def extension_of.inhabited : inhabited (extension_of i f) := ⟨(extension_of.has_bot _ f hi).bot⟩

omit hi
/--
We order the extensions by `(M1, e1) ≤ (M2, e2)` if and only if `M1 ≤ M2` and `e2` extends `e1`.
-/
instance : has_le (extension_of i f) :=
{ le := λ X1 X2, nonempty
    Σ' (h : X1.domain ≤ X2.domain),
      ∀ (m : X1.domain), X2.to_fun ⟨m, h m.2⟩ = X1.to_fun m }

instance : partial_order (extension_of i f) :=
{ le := (≤),
  le_refl := λ a, nonempty.intro
    ⟨le_refl _, λ _, congr_arg _ (subtype.ext_val rfl) ⟩,
  le_antisymm := λ a b ⟨⟨le_ab, hab⟩⟩ ⟨⟨le_ba, hba⟩⟩,
    have m_eq : a.domain = b.domain := (le_antisymm le_ab le_ba),
    extension_of.ext m_eq $ λ x, (hab x).symm,
  le_trans := λ a b c ⟨⟨le_ab, hab⟩⟩ ⟨⟨le_bc, hbc⟩⟩, nonempty.intro
    ⟨le_trans le_ab le_bc, λ z, by rw [← hab z, ← hbc ⟨z, le_ab z.2⟩]; refl⟩ }

section should_be_somewhere_else

variables {R i f}

lemma directed_on' {c : set (extension_of i f)} (hchain : is_chain (≤) c) :
  directed_on (≤) c := directed_on_iff_directed.mpr $ is_chain.directed hchain

lemma exists3 {c : set (extension_of i f)} (hchain : is_chain (≤) c) {α β γ}
  (mem1 : α ∈ c) (mem2 : β ∈ c) (mem3 : γ ∈ c) :
  ∃ (z) (mem4 : z ∈ c), α ≤ z ∧ β ≤ z ∧ γ ≤ z :=
begin
  rcases directed_on' hchain _ mem1 _ mem2 with ⟨z1, ⟨z1_mem, hz1⟩⟩,
  rcases directed_on' hchain z1 z1_mem _ mem3 with ⟨z, ⟨z_mem, hz⟩⟩,
  exact ⟨z, z_mem, le_trans hz1.1 hz.1, le_trans hz1.2 hz.1, hz.2⟩,
end

end should_be_somewhere_else

variables {R i f}
lemma chain_submodule_of_chain_extension_of
  {c : set (extension_of i f)} (hchain : is_chain (≤) c) :
  (is_chain (≤) $ (λ x : extension_of i f, x.domain) '' c) :=
begin
  rintro _ ⟨a, a_mem, rfl⟩ _ ⟨b, b_mem, rfl⟩ (neq : a.domain ≠ b.domain),
  rcases hchain a_mem b_mem (λ r, neq $ r ▸ rfl) with ⟨⟨le1, -⟩⟩ | ⟨⟨le1, -⟩⟩;
  tauto,
end

lemma submodule_le_of_extension_of_le {a b : extension_of i f} (le1 : a ≤ b) :
  a.domain ≤ b.domain := le1.some.1

lemma directed_on_of_chain {c : set (extension_of i f)} (hchain : is_chain (≤) c) :
  directed_on (≤) $ (λ x : extension_of i f, x.domain) '' c :=
directed_on_iff_directed.mpr $ (chain_submodule_of_chain_extension_of hchain).directed

lemma nonempty_of_extension_of {c : set (extension_of i f)} (hnonempty : c.nonempty) :
  ((λ x : extension_of i f, x.domain) '' c).nonempty :=
hnonempty.image _

/--For a nonempty chain of extensions of `f`, if `y` is in the supremum of underlying submodules of
the extensions in chain, then `y` is at least one of the underlying submodule in that chain.
`pick_submodule` picks that submodule-/
def pick_submodule {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  submodule R N :=
((submodule.mem_Sup_of_directed (nonempty_of_extension_of hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some

lemma pick_submodule_mem_image {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  pick_submodule hchain hnonempty y ∈ ((λ x : extension_of i f, x.domain) '' c) :=
((submodule.mem_Sup_of_directed (nonempty_of_extension_of hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some

/--The submodule picked by `pick_submodule` is the underlying submodule of an element in the chain,
i.e. underlying submodule of some `extension_of f`, `pick_extension_of` picks that extension.
-/
def pick_extension_of {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  extension_of i f :=
((submodule.mem_Sup_of_directed (nonempty_of_extension_of hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some.some

lemma pick_extension_of_mem {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  pick_extension_of hchain hnonempty y ∈ c :=
((submodule.mem_Sup_of_directed (nonempty_of_extension_of hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some.some_spec.1

lemma pick_extension_of_to_submodule_mem
  {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  y.1 ∈ (pick_extension_of hchain hnonempty y).domain :=
begin
  unfold pick_extension_of,
  generalize_proofs h mem1,
  convert h.some_spec.some_spec,
  exact mem1.some_spec.2,
end

lemma pick_submodule_mem {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (y : Sup ((λ x : extension_of i f, x.domain) '' c)) :
  y.1 ∈ pick_submodule hchain hnonempty y :=
((submodule.mem_Sup_of_directed (nonempty_of_extension_of hnonempty)
  (directed_on_of_chain hchain)).mp y.2).some_spec.some_spec

/--Every nonempty chain of `extension_of` f has a maximal element, i.e. a pair of `(N', f')`, where
all underlying submodule is submodule of `M'` and `f'` extends all functions. `max_extension` is
this maximal function, it is defined by taking union of all functions in the chain.
-/
def extension_of.max_extension {c : set (extension_of i f)}
  (hchain : is_chain (≤) c) (hnonempty : c.nonempty) :
  Sup ((λ x : extension_of i f, x.domain) '' c) → Q :=
λ y, (pick_extension_of hchain hnonempty y).to_fun
  ⟨y.1, by apply pick_extension_of_to_submodule_mem⟩

lemma extension_of.max_extension_property {c : set (extension_of i f)}
  (hchain : is_chain (≤) c) (hnonempty : c.nonempty)
  (x : Sup ((λ x : extension_of i f, x.domain) '' c))
  {γ : extension_of i f} (mem1 : γ ∈ c)
  (mem2 : ↑x ∈ γ.domain) :
  extension_of.max_extension hchain hnonempty x = γ.to_fun ⟨x, mem2⟩ :=
begin
  unfold extension_of.max_extension,
  generalize_proofs mem3,
  by_cases eq_ineq : pick_extension_of hchain hnonempty x = γ,
  { rw extension_of.ext_iff at eq_ineq,
    rcases eq_ineq with ⟨h1, h2⟩,
    convert h2 _, },
  { rcases hchain (pick_extension_of_mem hchain hnonempty x) mem1 eq_ineq with ⟨⟨_, h1⟩⟩|⟨⟨_, h1⟩⟩;
    erw ← h1 ⟨x, by assumption⟩;
    congr, },
end

lemma extension_of.max_extension.map_add {c : set (extension_of i f)}
  (hchain : is_chain (≤) c) (hnonempty : c.nonempty) (y1 y2):
  extension_of.max_extension hchain hnonempty (y1 + y2) =
  extension_of.max_extension hchain hnonempty y1 +
  extension_of.max_extension hchain hnonempty y2 :=
begin
  have mem_y1 := pick_extension_of_to_submodule_mem hchain hnonempty y1,
  have mem_y2 := pick_extension_of_to_submodule_mem hchain hnonempty y2,
  have mem_add :=  pick_extension_of_to_submodule_mem hchain hnonempty (y1 + y2),
  rw extension_of.max_extension_property hchain hnonempty y1
    (pick_submodule_mem_image hchain hnonempty y1).some_spec.1 mem_y1,
  rw extension_of.max_extension_property hchain hnonempty y2
    (pick_submodule_mem_image hchain hnonempty y2).some_spec.1 mem_y2,
  -- have := extension_of.max_extension_property hchain hnonempty _
  --   (pick_submodule_mem_image hchain hnonempty _).some_spec.1 mem_add,
  rw extension_of.max_extension_property hchain hnonempty _
    (pick_submodule_mem_image hchain hnonempty _).some_spec.1
    (by convert mem_add : ↑(y1 + y2) ∈
      (pick_extension_of hchain hnonempty (y1 + y2)).to_linear_pmap.domain),
  generalize_proofs hadd hy1 hy2,
  have := exists3 hchain hadd.some_spec.1 hy1.some_spec.1 hy2.some_spec.1,
  rcases this with ⟨_, _, ⟨⟨_, h1⟩⟩, ⟨⟨_, h2⟩⟩, ⟨⟨_, h3⟩⟩⟩,
  rw [← h1, ← h2, ← h3, ← map_add],
  congr,
end

lemma extension_of.max_extension.map_smul {c : set (extension_of i f)}
  (hchain : is_chain (≤) c) (hnonempty : c.nonempty) (r : R) (y):
  extension_of.max_extension hchain hnonempty (r • y) =
  r • extension_of.max_extension hchain hnonempty y :=
begin
  have mem_y := pick_extension_of_to_submodule_mem hchain hnonempty y,
  have mem_smul := pick_extension_of_to_submodule_mem hchain hnonempty (r • y),
  rw extension_of.max_extension_property hchain hnonempty y
    (pick_submodule_mem_image hchain hnonempty y).some_spec.1 mem_y,
  rw extension_of.max_extension_property hchain hnonempty (r • y)
    (pick_submodule_mem_image hchain hnonempty (r • y)).some_spec.1 mem_smul,
  generalize_proofs inst hsmul hy,
  rcases directed_on' hchain _ hsmul.some_spec.1 _ hy.some_spec.1 with
    ⟨_, _, ⟨⟨_, h1⟩⟩, ⟨⟨_, h2⟩⟩⟩,
  rw [← h1, ← linear_map.map_smul, ← h2],
  congr,
end

/--The maximal element of every nonempty chain of `extension_of` f-/
def extension_of.max {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) :
  extension_of i f :=
{ domain := Sup ((λ x : extension_of i f, x.domain) '' c),
  le := begin
    cases hnonempty with j hj,
    exact le_trans j.le (le_Sup ⟨j, hj, rfl⟩),
  end,
  to_fun :=
  { to_fun := extension_of.max_extension hchain hnonempty,
    map_add' := extension_of.max_extension.map_add hchain hnonempty,
    map_smul' := extension_of.max_extension.map_smul hchain hnonempty },
  is_extension := λ m, begin
    dsimp,
    generalize_proofs im_mem,
    change _ = (pick_submodule_mem_image hchain hnonempty ⟨i m, im_mem⟩).some.to_fun _,
    generalize_proofs mem_image mem_submodule,
    rw (Exists.some mem_image).is_extension m,
    congr,
  end }

lemma extension_of.le_max {c : set (extension_of i f)} (hchain : is_chain (≤) c)
  (hnonempty : c.nonempty) (a : extension_of i f) (ha : a ∈ c) :
  a ≤ extension_of.max hchain hnonempty :=
begin
  unfold extension_of.max extension_of.max_extension,
  refine ⟨⟨le_Sup ⟨a, ha, rfl⟩, _⟩⟩,
  dsimp at *,
  generalize_proofs mem1 mem_image mem2,
  by_cases eq_ineq : pick_extension_of hchain hnonempty ⟨↑m, mem1⟩ = a,
  { rcases (extension_of.ext_iff i f _ _).mp eq_ineq with ⟨h1, h2⟩,
    convert h2 _,
    rw subtype.ext_iff_val,
    refl, },
  { rcases hchain (pick_extension_of_mem hchain hnonempty _) ha eq_ineq with
      ⟨⟨le1, h1⟩⟩|⟨le1, h1⟩,
    symmetry,
    all_goals { convert h1 _; rw subtype.ext_iff_val; refl }, },
end

lemma extension_of.aux1 : ∀ (c : set (extension_of i f)),
  is_chain has_le.le c →
  c.nonempty →
  (∃ (ub : extension_of i f), ∀ (a : extension_of i f), a ∈ c → a ≤ ub) :=
λ c hchain hnonempty,
  ⟨extension_of.max hchain hnonempty, extension_of.le_max hchain hnonempty⟩

variables (f hi)
/--Since every nonempty chain has a maximal element, by Zorn's lemma, there is a maximal
`extension_of hi f`-/
def extension_of_max : extension_of i f :=
(@zorn_nonempty_partial_order (extension_of i f) _ ⟨(extension_of.has_bot i f hi).bot⟩ (extension_of.aux1)).some

lemma extension_of_max_is_max :
  ∀ (a : extension_of i f),
    (extension_of_max f hi) ≤ a → a = (extension_of_max f hi) :=
(@zorn_nonempty_partial_order (extension_of i f) _ ⟨(extension_of.has_bot i f hi).bot⟩ (extension_of.aux1)).some_spec

variables {hi f}
lemma extension_of_max_adjoin.aux1
  {y : N}
  (x : (extension_of_max f hi).domain ⊔ submodule.span R {y}) :
  ∃ (a : (extension_of_max f hi).domain) (b : R), x.1 = a.1 + b • y :=
begin
  have mem1 : x.1 ∈ (_ : set _) := x.2,
  rw submodule.coe_sup at mem1,
  rcases mem1 with ⟨a, b, a_mem, (b_mem : b ∈ (submodule.span R _ : submodule R N)), eq1⟩,
  rw submodule.mem_span_singleton at b_mem,
  rcases b_mem with ⟨z, eq2⟩,
  exact ⟨⟨a, a_mem⟩, z, by rw [← eq1, ← eq2]⟩,
end

/--If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `fst` pick an arbitrary such `m`.-/
def extension_of_max_adjoin.fst
  {y : N} (x : (extension_of_max f hi).domain ⊔ submodule.span R {y}) :
  (extension_of_max f hi).domain :=
(extension_of_max_adjoin.aux1 x).some

/--If `x ∈ M ⊔ ⟨y⟩`, then `x = m + r • y`, `snd` pick an arbitrary such `r`.-/
def extension_of_max_adjoin.snd
  {y : N} (x : (extension_of_max f hi).domain ⊔ submodule.span R {y}) : R :=
(extension_of_max_adjoin.aux1 x).some_spec.some

lemma extension_of_max_adjoin.eqn
  {y : N} (x : (extension_of_max f hi).domain ⊔ submodule.span R {y}) :
  x.1 = (extension_of_max_adjoin.fst x).1 + (extension_of_max_adjoin.snd x) • y :=
(extension_of_max_adjoin.aux1 x).some_spec.some_spec

variables (hi f)
/--the ideal `I = {r | r • y ∈ N}`-/
def extension_of_max_adjoin.ideal (y : N) :
  ideal R :=
(extension_of_max f hi).domain.comap (linear_map.id.smul_right y)

/--A linear map `I ⟶ Q` by `x ↦ f' (x • y)` where `f'` is the maximal extension-/
def extension_of_max_adjoin.ideal_to (y : N) :
  extension_of_max_adjoin.ideal f hi y →ₗ[R] Q :=
{ to_fun := λ z, (extension_of_max f hi).to_fun ⟨z.1 • y, z.2⟩,
  map_add' := λ z1 z2, by rw [← map_add]; congr; erw add_smul,
  map_smul' := λ z1 z2, begin
    rw [ring_hom.id_apply, ← linear_map.map_smul],
    exact congr_arg _ (subtype.ext_val (mul_smul _ _ _)),
  end }

/-- Since we assumed `Q` being Baer, the linear map `x ↦ f' (x • y) : I ⟶ Q` extends to `R ⟶ Q`,
call this extended map `φ`-/
def extension_of_max_adjoin.extend_ideal_to (h : module.Baer R Q) (y : N) : R →ₗ[R] Q :=
(h (extension_of_max_adjoin.ideal f hi y) (extension_of_max_adjoin.ideal_to f hi y)).some

lemma extension_of_max_adjoin.extend_ideal_to_is_extension (h : module.Baer R Q) (y : N) :
  ∀ (x : R) (mem : x ∈ extension_of_max_adjoin.ideal f hi y),
  extension_of_max_adjoin.extend_ideal_to f hi h y x =
  extension_of_max_adjoin.ideal_to f hi y ⟨x, mem⟩ :=
(h (extension_of_max_adjoin.ideal f hi y) (extension_of_max_adjoin.ideal_to f hi y)).some_spec

lemma extension_of_max_adjoin.extend_ideal_to_wd' (h : module.Baer R Q) {y : N} (r : R)
  (eq1 : r • y = 0) :
  extension_of_max_adjoin.extend_ideal_to f hi h y r = 0 :=
begin
  rw extension_of_max_adjoin.extend_ideal_to_is_extension f hi h y r
    (by rw eq1; exact submodule.zero_mem _ : r • y ∈ _),
  unfold extension_of_max_adjoin.ideal_to,
  simp only [linear_map.coe_mk, eq1],
  convert map_zero _,
end

lemma extension_of_max_adjoin.extend_ideal_to_wd (h : module.Baer R Q) {y : N} (r r' : R)
  (eq1 : r • y = r' • y) :
  extension_of_max_adjoin.extend_ideal_to f hi h y r =
  extension_of_max_adjoin.extend_ideal_to f hi h y r' :=
begin
  rw [← sub_eq_zero, ← map_sub],
  convert extension_of_max_adjoin.extend_ideal_to_wd' f hi h (r - r') _,
  rw [sub_smul, sub_eq_zero, eq1],
end

lemma extension_of_max_adjoin.extend_ideal_to_eq (h : module.Baer R Q) {y : N} (r : R)
  (hr : r • y ∈ (extension_of_max f hi).domain) :
  extension_of_max_adjoin.extend_ideal_to f hi h y r =
  (extension_of_max f hi).to_fun ⟨r • y, hr⟩ :=
by rw extension_of_max_adjoin.extend_ideal_to_is_extension f hi h _ _ hr; refl

/--We can finally define a linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r`
-/
def extension_of_max_adjoin.extension_to_fun (h : module.Baer R Q)
  {y : N} :
  (extension_of_max f hi).domain ⊔ submodule.span R {y} → Q :=
λ x, (extension_of_max f hi).to_fun (extension_of_max_adjoin.fst x) +
  extension_of_max_adjoin.extend_ideal_to f hi h y (extension_of_max_adjoin.snd x)

lemma extension_of_max_adjoin.extension_to_fun_wd (h : module.Baer R Q)
  {y : N} (x : (extension_of_max f hi).domain ⊔ submodule.span R {y})
  (a : (extension_of_max f hi).domain) (r : R)
  (eq1 : x.1 = a.1 + r • y) :
  extension_of_max_adjoin.extension_to_fun f hi h x =
  (extension_of_max f hi).to_fun a +
  extension_of_max_adjoin.extend_ideal_to f hi h y r :=
begin
  have eq2 := eq1,
  rw [extension_of_max_adjoin.eqn, ← sub_eq_zero,
    show ∀ (a b c d : N), (a + b) - (c + d) = (a - c) - (d - b), from λ _ _ _ _, by abel,
    sub_eq_zero, ← sub_smul] at eq2,
  have eq3 := extension_of_max_adjoin.extend_ideal_to_eq f hi h (r - extension_of_max_adjoin.snd x)
    (by rw ← eq2; exact submodule.sub_mem _ (extension_of_max_adjoin.fst x).2 a.2),
  simp only [map_sub, sub_smul, sub_eq_iff_eq_add] at eq3,
  unfold extension_of_max_adjoin.extension_to_fun,
  rw [eq3, ← add_assoc],
  congr' 1,
  rw [← map_add, show ∀ (a b : (extension_of_max f hi).domain), a + b = ⟨a.1 + b.1, _⟩,
    from λ _ _, rfl],
  have eq4 := extension_of_max_adjoin.eqn x,
  rw eq1 at eq4,
  simp only [eq4, add_sub, add_sub_cancel],
  exact congr_arg _ (subtype.ext_val rfl),
end

/--The linear map `M ⊔ ⟨y⟩ ⟶ Q` by `x + r • y ↦ f x + φ r` is an extension of `f`-/
def extension_of_max_adjoin (h : module.Baer R Q) (y : N) :
  extension_of i f :=
{ domain := (extension_of_max f hi).domain ⊔ submodule.span R {y},
  le := le_trans (extension_of_max f hi).le le_sup_left,
  to_fun :=
    { to_fun := extension_of_max_adjoin.extension_to_fun f hi h,
      map_add' := λ a b, begin
        have eq1 : (a + b).val =
          ((extension_of_max_adjoin.fst a) + (extension_of_max_adjoin.fst b)).1 +
          (extension_of_max_adjoin.snd a + extension_of_max_adjoin.snd b) • y,
        { change a.1 + b.1 = _ + _,
          rw [extension_of_max_adjoin.eqn, extension_of_max_adjoin.eqn, add_smul],
          abel, },
        rw [extension_of_max_adjoin.extension_to_fun_wd f hi h (a + b) _ _ eq1, map_add, map_add],
        unfold extension_of_max_adjoin.extension_to_fun,
        abel,
      end,
      map_smul' := λ r a, begin
        rw [ring_hom.id_apply],
        have eq1 : (r • a).1 = (r • extension_of_max_adjoin.fst a).1 +
          (r • extension_of_max_adjoin.snd a) • y,
        { change r • a.1 = _,
          rw [extension_of_max_adjoin.eqn, smul_add, smul_eq_mul, mul_smul],
          refl, },
        rw [extension_of_max_adjoin.extension_to_fun_wd f hi h (r • a) _ _ eq1,
          linear_map.map_smul, linear_map.map_smul, ← smul_add],
        congr',
      end },
  is_extension := λ m, begin
    simp only [linear_map.coe_mk],
    rw [(extension_of_max f hi).is_extension, extension_of_max_adjoin.extension_to_fun_wd f hi h
      _ ⟨i m, _⟩ 0 _, map_zero, add_zero],
    simp,
  end }

lemma extension_of_max_le (h : module.Baer R Q) {y : N} :
  extension_of_max f hi ≤ extension_of_max_adjoin f hi h y := nonempty.intro
⟨le_sup_left, λ m, begin
  generalize_proofs mem,
  have eq1 : (⟨m.1, mem⟩ : (extension_of_max f hi).domain ⊔ submodule.span R {y}).1 =
      m.1 + (0 : R) • y,
  { rw [zero_smul, add_zero], },
  change extension_of_max_adjoin.extension_to_fun f hi h ⟨m.1, mem⟩ = _,
  rw [extension_of_max_adjoin.extension_to_fun_wd f hi h _ _ _ eq1, map_zero, add_zero],
end⟩

lemma extension_of_max_eq (h : module.Baer R Q) (y : N) :
  extension_of_max_adjoin f hi h y = extension_of_max f hi :=
extension_of_max_is_max f hi _ (extension_of_max_le f hi h)

lemma extension_of_max_to_submodule_eq_top (h : module.Baer R Q) :
  (extension_of_max f hi).domain = ⊤ :=
begin
  by_contra rid,
  rcases show ∃ (y : N), y ∉ (extension_of_max f hi).domain,
    by contrapose! rid; ext; exact ⟨λ _, trivial, λ _, rid _⟩ with ⟨y, hy⟩,
  apply hy,
  erw [← extension_of_max_eq f hi h y, submodule.mem_sup],
  exact ⟨0, submodule.zero_mem _, y, submodule.mem_span_singleton_self _, zero_add _⟩,
end

/--**Baer's criterion** for injective module-/
protected theorem injective (h : module.Baer R Q) :
  module.injective R Q :=
{ out := λ X Y ins1 ins2 ins3 ins4 i hi f, begin
  resetI,
  have eq1 := extension_of_max_to_submodule_eq_top f hi h,
  set f'' : (⊤ : submodule R Y) →ₗ[R] Q :=
  { to_fun := λ y, (extension_of_max f hi).to_fun ⟨y.1, eq1.symm ▸ y.2⟩,
    map_add' := λ x y, by { dsimp, erw ← map_add,  congr' 1 },
    map_smul' := λ r x, by { dsimp, erw ← linear_map.map_smul, congr' 1 } } with f''_eq,
  use
  { to_fun := λ y, f'' ⟨y, trivial⟩,
    map_add' := λ x y, by rw ← map_add; congr',
    map_smul' := λ r x, by rw [ring_hom.id_apply, ← linear_map.map_smul]; refl },
  intros x,
  exact ((extension_of_max f hi).is_extension x).symm,
end }

end module.Baer
