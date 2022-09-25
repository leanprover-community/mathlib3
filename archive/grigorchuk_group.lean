import analysis.special_functions.log.basic
import topology.algebra.order.intermediate_value
import group_theory.perm.fibered
import group_theory.free_group

/-!
-/

noncomputable theory
open list set function real

namespace grigorchuk_group

namespace pre

def a : equiv.perm (list bool) :=
involutive.to_perm (λ l, list.cases_on l [] (λ b l, !b::l)) $ by rintro (_|⟨a, l⟩); simp

@[simp] lemma a_a (l : list bool) : a (a l) = l :=
involutive.to_perm_involutive _ l

@[simp] lemma length_a (l : list bool) : (a l).length = l.length :=
by induction l; simp only [*, a, involutive.coe_to_perm, length_cons]

@[simp] lemma head'_a (l : list bool) : (a l).head' = l.head'.map bnot := by cases l; refl

def bcd : fin 3 → list bool → list bool
| _ [] := []
| n (ff :: l) := ff :: (if n = 1 then l else a l)
| n (tt :: l) := tt :: bcd (n + 1) l

@[simp] lemma head'_bcd (n : fin 3) (l : list bool) : (bcd n l).head' = l.head' :=
by rcases l with _|⟨(_|_), _⟩; refl

@[simp] lemma length_bcd (n : fin 3) (l : list bool) : (bcd n l).length = l.length :=
begin
  induction l with hd tl ihl generalizing n; [refl, cases hd],
  { rw [bcd], split_ifs; simp only [length_cons, length_a] },
  { rw [bcd, length_cons, length_cons, ihl] }
end

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
(involutive_bcd 0).to_perm _

def c : equiv.perm (list bool) :=
(involutive_bcd 1).to_perm _

def d : equiv.perm (list bool) :=
(involutive_bcd 2).to_perm _

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

@[simp] lemma coe_fn_one : ⇑(1 : G) = id := rfl
lemma one_apply (l : list bool) : (1 : G) l = l := rfl

@[simp] lemma coe_fn_mul (g₁ g₂ : G) : ⇑(g₁ * g₂) = g₁ ∘ g₂ := rfl
lemma mul_apply (g₁ g₂ : G) (l : list bool) : (g₁ * g₂) l = g₁ (g₂ l) := rfl

@[simp] lemma a_inv : a⁻¹ = a := rfl
@[simp] lemma b_inv : b⁻¹ = b := rfl
@[simp] lemma c_inv : c⁻¹ = c := rfl
@[simp] lemma d_inv : d⁻¹ = d := rfl

@[simp] lemma a_mul_a : a * a = 1 := fun_like.ext _ _ pre.a_a
@[simp] lemma b_mul_b : b * b = 1 := fun_like.ext _ _ $ pre.involutive_bcd 0
@[simp] lemma c_mul_c : c * c = 1 := fun_like.ext _ _ $ pre.involutive_bcd 1
@[simp] lemma d_mul_d : d * d = 1 := fun_like.ext _ _ $ pre.involutive_bcd 2

@[simp] lemma b_mul_c : b * c = d := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 0 l
@[simp] lemma c_mul_d : c * d = b := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 1 l
@[simp] lemma d_mul_b : d * b = c := fun_like.ext _ _ $ λ l, pre.bcd_apply_succ 2 l
@[simp] lemma c_mul_b : c * b = d := inv_injective $ by simp
@[simp] lemma d_mul_c : d * c = b := inv_injective $ by simp
@[simp] lemma b_mul_d : b * d = c := inv_injective $ by simp

@[simp] lemma head'_a (l : list bool) : (a l).head' = l.head'.map bnot := pre.head'_a l
@[simp] lemma head'_b (l : list bool) : (b l).head' = l.head' := pre.head'_bcd _ l
@[simp] lemma head'_c (l : list bool) : (c l).head' = l.head' := pre.head'_bcd _ l
@[simp] lemma head'_d (l : list bool) : (d l).head' = l.head' := pre.head'_bcd _ l

@[simp] lemma head'_bcd (n : fin 3) (l : list bool) : (![b, c, d] n l).head' = l.head' :=
by { fin_cases n; exact pre.head'_bcd _ _ }

def to_perm : G →* equiv.perm (list bool) := subgroup.subtype _

@[simp] lemma coe_fn_to_perm (g : G) : ⇑(to_perm g) = g := rfl

@[simp] lemma to_perm_a : to_perm a = pre.a := rfl
@[simp] lemma to_perm_b : to_perm b = pre.b := rfl
@[simp] lemma to_perm_c : to_perm c = pre.c := rfl
@[simp] lemma to_perm_d : to_perm d = pre.d := rfl

@[simp] lemma to_perm_range : to_perm.range = G := subgroup.subtype_range G

lemma to_perm_injective : injective to_perm := subtype.coe_injective

@[simp] lemma closure_abcd : subgroup.closure ({a, b, c, d} : set G) = ⊤ :=
subgroup.map_injective to_perm_injective $
  by { simp only [monoid_hom.map_closure, image_insert_eq, image_singleton,
    ← monoid_hom.range_eq_map, to_perm_range], refl }

@[simp] lemma mclosure_abcd : submonoid.closure ({a, b, c, d} : set G) = ⊤ :=
by simp only [← subgroup.top_to_submonoid, ← closure_abcd, subgroup.closure_to_submonoid,
  inv_insert, inv_singleton, a_inv, b_inv, c_inv, d_inv, union_self]

def of_free_group : free_group (fin 4) →* G := free_group.lift ![a, b, c, d]

@[simp] lemma range_of_free_group : of_free_group.range = ⊤ :=
by simp only [of_free_group, free_group.lift.range_eq_closure, matrix.range_cons,
  matrix.range_empty, ← insert_eq, insert_emptyc_eq, closure_abcd]

lemma surjective_of_free_group : surjective of_free_group :=
monoid_hom.range_top_iff_surjective.mp range_of_free_group

def of_free_monoid : free_monoid (fin 4) →* G := free_monoid.lift ![a, b, c, d]

@[simp] lemma of_free_monoid_of (n : fin 4) : of_free_monoid (free_monoid.of n) = ![a, b, c, d] n :=
free_monoid.lift_eval_of _ _

@[simp] lemma mrange_of_free_monoid : of_free_monoid.mrange = ⊤ :=
by simp only [of_free_monoid, free_monoid.mrange_lift, matrix.range_cons, matrix.range_empty,
  ← insert_eq, insert_emptyc_eq, mclosure_abcd]

lemma surjective_of_free_monoid : surjective of_free_monoid :=
monoid_hom.mrange_top_iff_surjective.1 mrange_of_free_monoid

/-- `to_free_monoid g` is the shortest list that represents `g`. -/
def to_free_monoid (g : G) : free_monoid (fin 4) :=
argmin_on length nat.well_founded_lt.1 (of_free_monoid ⁻¹' {g}) (surjective_of_free_monoid g)

lemma of_free_monoid_to_free_monoid (g : G) : of_free_monoid (to_free_monoid g) = g :=
argmin_on_mem length _ (of_free_monoid ⁻¹' {g}) _

def is_minimal (g : free_monoid (fin 4)) : Prop :=
∀ g', of_free_monoid g = of_free_monoid g' → length g ≤ length g'

lemma is_minimal_to_free_monoid (g : G) : is_minimal (to_free_monoid g) :=
λ g' hg', argmin_on_le _ _ _ $ hg'.symm.trans $ of_free_monoid_to_free_monoid g

lemma exists_is_minimal_of_free_monoid_eq (g : G) : ∃ g', is_minimal g' ∧ of_free_monoid g' = g :=
⟨to_free_monoid g, is_minimal_to_free_monoid g, of_free_monoid_to_free_monoid g⟩

lemma length_to_free_monoid_of_free_monoid_le (g : free_monoid (fin 4)) :
  length (to_free_monoid (of_free_monoid g)) ≤ length g :=
is_minimal_to_free_monoid _ _ $ of_free_monoid_to_free_monoid _

lemma is_minimal.to_infix {g₁ g₂ : free_monoid (fin 4)} (h₁ : is_minimal g₁) (h₂ : g₂ <:+: g₁) :
  is_minimal g₂ :=
begin
  rcases h₂ with ⟨g, g', rfl⟩,
  intros g₂' h₂,
  have H := h₁ (g * g₂' * g') (by simp only [← free_monoid.mul_def, map_mul, h₂]),
  simpa only [free_monoid.mul_def, length_append, add_le_add_iff_left, add_le_add_iff_right] using H
end

protected lemma is_minimal.chain' {g : free_monoid (fin 4)} (h : is_minimal g) :
  g.chain' (λ m n, is_minimal [m, n]) :=
(chain'_is_infix g).imp $ λ m n, h.to_infix

lemma is_minimal.ne {m n : fin 4} (h : is_minimal [m, n]) : m ≠ n :=
begin
  rintro rfl,
  refine (h 1 _).not_lt two_pos,
  rw [← free_monoid.of_mul_eq_cons, ← free_monoid.of_def, map_mul],
  fin_cases m,
  exacts [a_mul_a, b_mul_b, c_mul_c, d_mul_d]
end

lemma is_minimal.chain'_ne {g : free_monoid (fin 4)} (h : is_minimal g) : g.chain' (≠) :=
h.chain'.imp $ λ _ _, is_minimal.ne

lemma is_minimal.eq_0_or_eq_0 {m n : fin 4} (h : is_minimal [m, n]) : m = 0 ∨ n = 0 :=
begin
  have hne := h.ne,
  contrapose! h, cases h with hm hn,
  have h2 : length [m, n] = 2 := rfl,
  simp_rw [is_minimal, not_forall, h2, not_le, exists_prop, ← free_monoid.of_mul_eq_cons m,
    ← free_monoid.of_def, map_mul, of_free_monoid_of],
  fin_cases m; fin_cases n; try { exact absurd rfl ‹_› },
  { exact ⟨free_monoid.of 3, by simp, by simp [free_monoid.of_def]⟩ },
  { exact ⟨free_monoid.of 2, by simp, by simp [free_monoid.of_def]⟩ },
  { exact ⟨free_monoid.of 3, by simp, by simp [free_monoid.of_def]⟩ },
  { exact ⟨free_monoid.of 1, by simp, by simp [free_monoid.of_def]⟩ },
  { exact ⟨free_monoid.of 2, by simp, by simp [free_monoid.of_def]⟩ },
  { exact ⟨free_monoid.of 1, by simp, by simp [free_monoid.of_def]⟩ },
end

lemma is_minimal.chain'_eq_0 {g : free_monoid (fin 4)} (h : is_minimal g) :
  g.chain' (λ m n : fin 4, m = 0 ∨ n = 0) :=
h.chain'.imp $ λ _ _, is_minimal.eq_0_or_eq_0

lemma le_length_preserving : G ≤ equiv.perm.fiberwise length :=
(subgroup.closure_le _).2 $
  begin
    rintro g (rfl|rfl|rfl|(rfl : g = pre.d)),
    exacts [pre.length_a, pre.length_bcd _, pre.length_bcd _, pre.length_bcd _]
  end

def to_length_preserving : G →* equiv.perm.fiberwise (@length bool) :=
subgroup.inclusion le_length_preserving

@[simp] lemma coe_to_length_preserving (g : G) : ⇑(to_length_preserving g) = g := rfl

@[simp] lemma length_apply (g : G) (l : list bool) : length (g l) = length l :=
le_length_preserving g.2 l

@[simp] lemma apply_nil (g : G) : g [] = [] := length_eq_zero.1 $ length_apply g _

lemma head'_of_free_monoid (g : free_monoid (fin 4)) (l : list bool) :
  (of_free_monoid g l).head' = l.head'.map (bnot^[count 0 g]) :=
begin
  induction g using free_monoid.rec_on with x g ihg,
  { exact (congr_fun option.map_id l.head').symm },
  { rw [map_mul, of_free_monoid_of, free_monoid.mul_def, free_monoid.of_def, singleton_append,
      count_cons, mul_apply],
    revert x, refine fin.forall_fin_succ.2 ⟨_, λ x, _⟩,
    { rw [matrix.cons_val_zero, if_pos rfl, iterate_succ', head'_a, ihg, option.map_map] },
    { rw [matrix.cons_val_succ, head'_bcd, ihg, if_neg],
      exact x.succ_ne_zero.symm } }
end

def head_preserving : subgroup G := (equiv.perm.fiberwise head').comap to_perm

local notation `H` := head_preserving

lemma mem_head_preserving {g : G} : g ∈ H ↔ ∀ l, (g l).head' = l.head' := iff.rfl

@[simp] lemma of_free_monoid_mem_head_preserving (g : free_monoid (fin 4)) :
  of_free_monoid g ∈ H ↔ even (count 0 g) :=
calc of_free_monoid g ∈ H ↔ ∀ o : option bool, o.map (bnot ^[count 0 g]) = id o :
  by simp only [mem_head_preserving, head'_of_free_monoid, surjective_head'.forall, id]
... ↔ (bnot ^[count 0 g]) = id : by simp only [← funext_iff, option.map_eq_id]
... ↔ even (count 0 g) : bool.involutive_bnot.iterate_eq_id bool.bnot_ne_id

@[simp] lemma a_nmem_head_preserving : a ∉ H :=
show ![a, b, c, d] 0 ∉ H,
  by { rw [← of_free_monoid_of, of_free_monoid_mem_head_preserving], dec_trivial }

@[simp] lemma b_mem_head_preserving : b ∈ H :=
show ![a, b, c, d] 1 ∈ H,
  by { rw [← of_free_monoid_of, of_free_monoid_mem_head_preserving], dec_trivial }

@[simp] lemma c_mem_head_preserving : c ∈ H :=
show ![a, b, c, d] 2 ∈ H,
  by { rw [← of_free_monoid_of, of_free_monoid_mem_head_preserving], dec_trivial }

@[simp] lemma d_mem_head_preserving : d ∈ H :=
show ![a, b, c, d] 3 ∈ H,
  by { rw [← of_free_monoid_of, of_free_monoid_mem_head_preserving], dec_trivial }

@[simp] lemma mul_mem_head_preserving {g₁ g₂ : G} : g₁ * g₂ ∈ H ↔ (g₁ ∈ H ↔ g₂ ∈ H) :=
begin
  rcases surjective_of_free_monoid g₁ with ⟨g₁, rfl⟩,
  rcases surjective_of_free_monoid g₂ with ⟨g₂, rfl⟩,
  simp_rw [← map_mul, of_free_monoid_mem_head_preserving, free_monoid.mul_def, count_append,
    nat.even_add],
end

lemma a_mul_mem_head_preserving {g : G} : a * g ∈ H ↔ g ∉ H := by simp
lemma b_mul_mem_head_preserving {g : G} : b * g ∈ H ↔ g ∈ H := by simp
lemma c_mul_mem_head_preserving {g : G} : c * g ∈ H ↔ g ∈ H := by simp
lemma d_mul_mem_head_preserving {g : G} : d * g ∈ H ↔ g ∈ H := by simp

#check subgroup.index

lemma head_preserving_eq_closure :
  H = subgroup.closure {b, c, d, a * b * a, a * c * a, a * d * a} :=
begin
  refine le_antisymm (λ g hg, _) (by simp [insert_subset]),
  rcases exists_is_minimal_of_free_monoid_eq g with ⟨g, hmin, rfl⟩,
  
end

def head_preserving_restr (b : bool) : head_preserving →* G :=
{ to_fun := λ e, ⟨_, _⟩,
  map_one' := _,
  map_mul' := _ }

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
              (so: "essentially" gamma(n) <= 1/2 gamma(eta n)^2, by finding good g_0,g_1)
--> upper bound

3) similarly, |h| <= 2(|g_0|+|g_1|) + constant
              (so: "essentially" gamma(n) >= 8gamma(n/2)^2, by finding good h)
--> lower bound

-/

end grigorchuk_group
