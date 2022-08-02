import tactic
import group_theory.group_action.basic
import group_theory.group_action.sub_mul_action
import algebra.homology.exact
import algebra.module.pi
import representation_theory.cohomology.distrib_mul_action_equiv
import group_theory.quotient_group

universes v u w u₁ u₂ u₃

set_option old_structure_cmd true

structure sub_distrib_mul_action (G : Type u)
  (M : Type v)
  [monoid G] [add_comm_group M]
  [distrib_mul_action G M]
extends sub_mul_action G M, add_subgroup M

namespace sub_distrib_mul_action
variables {G : Type u} [monoid G]
variables {M : Type v} [add_comm_group M] [distrib_mul_action G M]
variables {N : Type w} [add_comm_group N] [distrib_mul_action G N]

instance : set_like (sub_distrib_mul_action G M) M :=
⟨carrier, λ p q h, by cases p; cases q; congr'⟩

@[ext] lemma ext {A B : sub_distrib_mul_action G M}
  (h : ∀ m : M, m ∈ A ↔ m ∈ B) : A = B := set_like.ext h

theorem ext_iff {A B : sub_distrib_mul_action G M} :
  A = B ↔ ∀ m : M, m ∈ A ↔ m ∈ B :=
set_like.ext_iff

variables (A : sub_distrib_mul_action G M)

lemma zero_mem : (0 : M) ∈ A :=
A.zero_mem'

lemma add_mem {a b : M} (ha : a ∈ A) (hb : b ∈ A) :
  a + b ∈ A :=
A.add_mem' ha hb

lemma smul_mem (g : G) {a : M} (ha : a ∈ A) :
  g • a ∈ A :=
A.smul_mem' g ha

instance fuckoff : has_coe A M :=
by apply_instance

lemma neg_mem {a : M} (ha : a ∈ A) :
  -a ∈ A :=
A.neg_mem' ha

instance to_add_comm_group (N : sub_distrib_mul_action G M) :
  add_comm_group N :=
add_subgroup.to_add_comm_group N.to_add_subgroup

instance to_distrib_mul_action (N : sub_distrib_mul_action G M) :
  distrib_mul_action G N :=
{ smul := λ g n, ⟨g • (n : M), N.smul_mem g n.2⟩,
  one_smul := λ n, by ext; exact one_smul G n,
  mul_smul := λ g h n, by ext; exact mul_smul _ _ _,
  smul_add := λ g m n, by ext; exact smul_add _ _ _,
  smul_zero := λ g, by ext; exact smul_zero _ }

variables {A}

@[simp] lemma coe_add (a b : A) :
  ((a + b : A) : M) = a + b := rfl

@[simp] lemma coe_zero : ((0 : A) : M) = 0 := rfl

@[simp] lemma coe_neg (a : A) :
  ((-a : A) : M) = -a := rfl

@[simp] lemma coe_sub (a b : A) :
  ((a - b : A) : M) = a - b := rfl

@[simp] lemma coe_smul (g : G) (a : A) :
  ((g • a : A) : M) = g • (a : M) := rfl

variables (A)
def subtype : A →+[G] M :=
{ to_fun := coe,
  map_smul' := coe_smul,
  map_zero' := coe_zero,
  map_add' := coe_add }

def quotient := M ⧸ A.to_add_subgroup

instance : add_comm_group A.quotient :=
by unfold quotient; apply_instance
#exit
instance : distrib_mul_action G A.quotient :=
{ smul := λ g m, quotient.lift_on' m (λ x, quotient_add_group.mk' A.to_add_subgroup (g • x))
  (λ x y (h : _ + _ ∈ _), quotient.eq'.2 $ show _ + _ ∈ _, by
    { rw neg_add_eq_sub at *,
      rw ←smul_sub,
      exact A.smul_mem _ h }),
  one_smul := λ m, quotient.induction_on' m $ λ x, show quotient.mk' _ = _, by rw one_smul,
  mul_smul := λ g h m, quotient.induction_on' m $ λ x,
    show quotient.mk' _ = quotient.mk' _, by rw mul_smul,
  smul_add := λ g m, quotient.induction_on' m $ λ x n, quotient.induction_on' n $ λ y,
    show quotient_add_group.mk' _ _ = _, by rw [smul_add, add_monoid_hom.map_add]; refl,
  smul_zero := λ g, by
  { rw ←(quotient_add_group.mk' A.to_add_subgroup).map_zero,
    show quotient_add_group.mk' A.to_add_subgroup (g • 0) = 0,
    rw [smul_zero, add_monoid_hom.map_zero] }}

def mkq : M →+[G] A.quotient :=
{ map_smul' := λ g x, rfl,
  .. quotient_add_group.mk' A.to_add_subgroup }

lemma mkq_eq_zero_iff {x : M} : A.mkq x = 0 ↔ x ∈ A :=
quotient_add_group.eq_zero_iff x

instance : has_top (sub_distrib_mul_action G M) :=
{ top := by refine
  { carrier := set.univ,
    smul_mem' := _,
    zero_mem' := _,
    add_mem' := _,
    neg_mem' := _ }; { intros, trivial }}

instance : has_bot (sub_distrib_mul_action G M) :=
{ bot :=
  { carrier := {0},
    smul_mem' := λ g x (hx : x = 0), show _ = _, by rw [hx, smul_zero],
    zero_mem' := rfl,
    add_mem' := λ x y (hx : x = 0) (hy : y = 0), show _ = _, by rw [hx, hy, zero_add],
    neg_mem' := λ x (hx : x = 0), show _ = _, by rw [hx, neg_zero] }}

end sub_distrib_mul_action

namespace distrib_mul_action

variables {G : Type u} [monoid G] {M : Type v} [add_comm_group M] [distrib_mul_action G M]

-- ugh can't find these
lemma nsmul_comm (n : ℕ) (g : G) (m : M) :
  n • g • m = g • n • m :=
begin
  induction n with n hn,
  { simp only [zero_smul, smul_zero] },
  { simp only [succ_nsmul, hn, smul_add], }
end

lemma gsmul_comm (n : ℤ) (g : G) (m : M) :
  n • g • m = g • n • m :=
begin
  induction n with n n,
  { simp only [nsmul_comm, int.of_nat_eq_coe, coe_nat_zsmul]},
  { simp only [zsmul_neg_succ_of_nat, nsmul_comm, smul_neg] }
end

end distrib_mul_action

variables {G : Type u} [monoid G] {α : Type u₁}

def pi.eval_distrib_mul_action_hom (M : α → Type*) [Π i, add_comm_group (M i)]
  [Π i, distrib_mul_action G (M i)] (i : α) : (Π i, M i) →+[G] M i :=
{ map_smul' := λ g m, by simp only [pi.eval_add_monoid_hom_apply, add_monoid_hom.to_fun_eq_coe, pi.smul_apply],
  .. pi.eval_add_monoid_hom M i }

namespace distrib_mul_action_hom

variables {M : Type v} [add_comm_group M] [distrib_mul_action G M]
variables {N : Type w} [add_comm_group N] [distrib_mul_action G N]

lemma map_nsmul (f : M →+[G] N) (m : M) (n : ℕ) :
  f (n • m) = n • f m :=
f.to_add_monoid_hom.map_nsmul m n

lemma map_gsmul (f : M →+[G] N) (m : M) (n : ℤ) :
  f (n • m) = n • f m :=
f.to_add_monoid_hom.map_zsmul m n

lemma map_sum (g : M →+[G] N) (f : α → M) (s : finset α) :
  g (s.sum f) = s.sum (λ x, g (f x)) :=
g.to_add_monoid_hom.map_sum f s

-- can't find the add_monoid_hom version of this?
def pi (M : α → Type*) [Π i, add_comm_group (M i)] [Π i, distrib_mul_action G (M i)]
  (F : Π i, N →+[G] M i) : N →+[G] (Π i, M i) :=
{ to_fun := λ x i, F i x,
  map_smul' := by { intros, ext, rw map_smul, refl },
  map_zero' := by { intros, ext, rw map_zero, refl },
  map_add' := by { intros, ext, rw map_add, refl }}

def ker (φ : M →+[G] N) :
  sub_distrib_mul_action G M :=
by { refine_struct {carrier := {m : M | φ m = 0}},
  all_goals { intros, simp only [*, set.mem_set_of_eq] at * },
  { simp only [*, smul_zero, map_smul] },
  { simp only [*, map_add, add_zero] },
  { exact map_zero _ },
  { simp only [*, map_neg, neg_zero] }}

def cod_restrict (A : sub_distrib_mul_action G N) (f : M →+[G] N) (h : ∀ m, f m ∈ A) :
  M →+[G] A :=
{ to_fun := λ m, ⟨f m, h m⟩,
  map_smul' := by { intros, congr, rw map_smul, refl },
  map_zero' := by { congr, rw map_zero },
  map_add' := by { intros, congr, rw map_add }}

@[simp] lemma cod_restrict_apply  (A : sub_distrib_mul_action G N) {f : M →+[G] N}
  {h : ∀ m, f m ∈ A} {x : M} :
  (f.cod_restrict A h x : N) = f x :=
rfl

variable (φ : M →+[G] N)

@[simp] lemma mem_ker {m : M} : m ∈ φ.ker ↔ φ m = 0 := iff.rfl

lemma ker_zero : ker (0 : M →+[G] N) = ⊤ :=
sub_distrib_mul_action.ext $ λ x, ⟨λ h, trivial, λ h, rfl⟩

def range (φ : M →+[G] N) :
  sub_distrib_mul_action G N :=
by { refine_struct {carrier := set.range φ},
  { rintros c x ⟨y, hy⟩,
    exact ⟨c • y, by rw [map_smul, hy]⟩ },
  { rintros a b ⟨x, hx⟩ ⟨y, hy⟩,
    exact ⟨x + y, by rw [map_add, hx, hy]⟩ },
  { exact ⟨0, map_zero _⟩ },
  { rintros x ⟨y, hy⟩,
    exact ⟨-y, by rw [map_neg, hy]⟩ }}

lemma range_coe (n : N) : n ∈ (set.range (⇑φ)) ↔ n ∈ φ.range := iff.rfl
@[simp] lemma mem_range (n : N) : n ∈ (set.range (⇑φ)) ↔ ∃ m : M, φ m = n := iff.rfl
@[simp] lemma mem_range_self {m : M} : φ m ∈ φ.range := ⟨m, rfl⟩

variables {P : Type u₂} [add_comm_group P] [distrib_mul_action G P]
lemma range_le_ker_iff {g : N →+[G] P} : φ.range ≤ g.ker ↔ g.comp φ = 0 :=
⟨λ h, ext $ λ x, h φ.mem_range_self, λ h x ⟨y, hy⟩, by rw ←hy; exact ext_iff.1 h y⟩

lemma range_eq_top_iff : φ.range = ⊤ ↔ function.surjective φ :=
⟨λ h y, show y ∈ φ.range, by rw h; trivial, λ h, sub_distrib_mul_action.ext $ λ x,
  ⟨λ h, trivial, λ hx, h x⟩⟩

lemma range_mkq_comp : φ.range.mkq.comp φ = 0 :=
ext $ λ x, φ.range.mkq_eq_zero_iff.2 φ.mem_range_self

noncomputable def equiv_of_bijective (h : function.bijective φ) : M ≃+[G] N :=
{ inv_fun := λ n, classical.some (h.2 n),
  left_inv := sorry,
  right_inv := sorry, .. φ }


end distrib_mul_action_hom

namespace sub_distrib_mul_action
variables {M : Type v} {N : Type w} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action G N] (A : sub_distrib_mul_action G M)

def lift (f : M →+[G] N) (h : A ≤ f.ker) : A.quotient →+[G] N :=
{ map_smul' := λ g x, quotient.induction_on' x $ λ m, show _ = g • f m, by
  { rw ←f.map_smul, refl },
  .. quotient_add_group.lift A.to_add_subgroup f.to_add_monoid_hom h }

lemma lift_mkq (f : M →+[G] N) (h : A ≤ f.ker) {m : M} :
  A.lift f h (A.mkq m) = f m := rfl

lemma ker_mkq : A.mkq.ker = A :=
ext $ λ x, A.mkq_eq_zero_iff

lemma range_mkq : A.mkq.range = ⊤ :=
A.mkq.range_eq_top_iff.2 $ λ y, quotient.induction_on' y $ λ x, ⟨x, rfl⟩

end sub_distrib_mul_action

namespace distrib_mul_action_hom

variables {M : Type v} {N : Type w} [add_comm_group M] [add_comm_group N] [distrib_mul_action G M]
  [distrib_mul_action G N]

noncomputable def quot_ker_equiv_range (f : M →+[G] N) : f.ker.quotient ≃+[G] f.range :=
(f.ker.lift (f.cod_restrict f.range $ λ _, f.mem_range_self) $
  λ x hx, by ext; exact hx).equiv_of_bijective sorry

noncomputable def quot_ker_equiv_of_surjective (f : M →+[G] N) (hf : function.surjective f) :
  f.ker.quotient ≃+[G] N :=
(f.ker.lift f (λ x, id)).equiv_of_bijective sorry

end distrib_mul_action_hom
