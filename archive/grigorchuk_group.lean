import analysis.special_functions.log
import topology.algebra.order.intermediate_value

/-!
-/

noncomputable theory
open set function real

namespace grigorchuk_group

namespace pre

def a : equiv.perm (list bool) :=
involutive.to_perm (λ l, list.cases_on l [] (λ b l, !b::l)) $ by rintro (_|⟨a, l⟩); simp

@[simp] lemma a_a (l : list bool) : a (a l) = l :=
involutive.to_perm_involutive _ l

def bcd : fin 3 → list bool → list bool
| _ [] := []
| n (ff :: l) := ff :: (if n = 0 then l else a l)
| n (tt :: l) := tt :: bcd (n + 1) l

lemma involutive_bcd (n : fin 3) : involutive (bcd n) :=
begin
  intro l,
  induction l with b l ihl generalizing n, { refl },
  cases b,
  { fin_cases n; norm_num [bcd] },
  { simp [bcd, ihl] }
end

lemma bcd_apply_succ (n : fin 3) (l : list bool) :
  bcd n (bcd (n + 1) l) = bcd (n + 2) l :=
begin
  induction l with b l ihl generalizing n, { refl },
  cases b,
  { fin_cases n; norm_num [bcd] },
  { simp [bcd, ihl, add_right_comm] }
end

def b : equiv.perm (list bool) :=
(involutive_bcd 1).to_perm _

def c : equiv.perm (list bool) :=
(involutive_bcd 2).to_perm _

def d : equiv.perm (list bool) :=
(involutive_bcd 0).to_perm _

end pre

def _root_.grigorchuk_group : subgroup (equiv.perm (list bool)) :=
subgroup.closure {pre.a, pre.b, pre.c, pre.d}

local notation `G` := grigorchuk_group

def a : G := ⟨pre.a, subgroup.subset_closure $ or.inl rfl⟩
def b : G := ⟨pre.b, subgroup.subset_closure $ or.inr $ or.inl rfl⟩
def c : G := ⟨pre.c, subgroup.subset_closure $ or.inr $ or.inr $ or.inl rfl⟩
def d : G := ⟨pre.d, subgroup.subset_closure $ or.inr $ or.inr $ or.inr rfl⟩

instance : equiv_like G (list bool) (list bool) :=
{ coe := λ f, f.1,
  inv := λ f, f.1.symm,
  left_inv := λ f, f.1.left_inv,
  right_inv := λ f, f.1.right_inv,
  coe_injective' := λ f g h₁ h₂, subtype.coe_injective $ fun_like.coe_injective h₁ }

@[simp] lemma a_inv : a⁻¹ = a := rfl
@[simp] lemma b_inv : b⁻¹ = b := rfl
@[simp] lemma c_inv : c⁻¹ = c := rfl
@[simp] lemma d_inv : d⁻¹ = d := rfl

@[simp] lemma a_mul_a : a * a = 1 := fun_like.ext _ _ pre.a_a
@[simp] lemma b_mul_b : b * b = 1 := fun_like.ext _ _ $ pre.involutive_bcd 1
@[simp] lemma c_mul_c : c * c = 1 := fun_like.ext _ _ $ pre.involutive_bcd 2
@[simp] lemma d_mul_d : d * d = 1 := fun_like.ext _ _ $ pre.involutive_bcd 0

@[simp] lemma b_mul_c : b * c = d := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 1 l
@[simp] lemma c_mul_d : c * d = b := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 2 l
@[simp] lemma d_mul_b : d * b = c := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 0 l
@[simp] lemma c_mul_b : c * b = d := inv_injective $ by simp
@[simp] lemma d_mul_c : d * c = b := inv_injective $ by simp
@[simp] lemma b_mul_d : b * d = c := inv_injective $ by simp

lemma exists_eta : ∃ η ∈ Ioo (0.81053 : ℝ) 0.81054, η ^ 3 + η ^ 2 + η = (2 : ℝ) :=
mem_image_iff_bex.1 $ intermediate_value_Ioo (by norm_num)
  (continuous.continuous_on $ by continuity) (by norm_num)

def eta : ℝ := exists_eta.some

local notation `η` := grigorchuk_group.eta

lemma eta_gt_081053 : 0.81053 < η := exists_eta.some_spec.fst.1
lemma eta_lt_081054 : η < 0.81054 := exists_eta.some_spec.fst.2

lemma eta_pos : 0 < η := lt_trans (by norm_num) eta_gt_081053
lemma eta_lt_one : η < 1 := eta_lt_081054.trans (by norm_num)
lemma eta_lt_two : η < 2 := eta_lt_one.trans one_lt_two

def alpha : ℝ := log 2 / log (2 / η)

local notation `α` := alpha

lemma alpha_lt_one : α < 1 :=
(div_lt_one $ log_pos $ (one_lt_div eta_pos).2 eta_lt_two).2 $
  log_lt_log two_pos $ (lt_div_iff eta_pos).2 $
  calc 2 * η < 2 * 1 : (mul_lt_mul_left two_pos).2 eta_lt_one
  ... = 2 : mul_one _

/- 
definitions: normed group, multiplication operation.
definition: equiv. of norms
lemma: for f.g. group, canonical equiv. class of norms

definition: growth of a group = function gamma(n) = #{g in G | |g|<=n}.
definition: gamma ≾, (asymptotic domination) delta if exist C: gamma(n)<=delta(C n). ~ equiv relation.
lemma: independent of choice of metric, for f.g. group

theorem: exp(C n^(1/2)) <= gamma(n) <= exp(C n^alpha)
theorem: exp(n^(1/2)) <~ gamma(n) <~ exp(n^alpha)

-------------------------------------------------
H subgroup of index 2
|.| on G, defined using eta

psi: H -> GxG.

1) psi almost bijection: injective, image has index 8.

2) if psi(h) = (g_0,g_1), then |g_0|+|g_1| <= eta*(|h|+|a|)
 

Finite set S e.g. {a,b,c,d,1}
Finite set X eg. {tt,ff}
map \Psi : SxX -> XxS

---> semigroup G = <S> acting on X^*. Action is: s(x_1x_2...x_n) = y_1 t(x_2...x_n) when Psi(s,x_1)=(y_1,t)

in case Psi(s,-).1 is permutation for all s, then G is group.
-/

end grigorchuk_group
