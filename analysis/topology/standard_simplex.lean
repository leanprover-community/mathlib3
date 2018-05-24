import algebraic_topology.simplex_category analysis.topology.topological_space analysis.real data.finsupp data.fin algebra.big_operators data.finset data.fintype analysis.nnreal algebra.group
noncomputable theory

open classical


namespace nnrealpown
definition type_pow : Type* → ℕ → Type* := λ α n, fin n → α

instance type_pow_instance : has_pow Type* ℕ := ⟨type_pow⟩

instance {n : ℕ} : topological_space (ℝ≥0^n)
:= by show topological_space (fin n → ℝ≥0); apply_instance

end nnrealpown



namespace standard_simplex

open finset

definition standard_simplex (n : ℕ) : set (ℝ≥0^(n+1)) :=
 λ x : fin (n+1) → ℝ≥0, sum univ x = 1

variable {n : ℕ}

definition induced_map {m n : ℕ} (f : fin (m+1) → fin (n+1))
: standard_simplex m → standard_simplex n := λ x, ⟨λ j, sum (univ.filter (λ i, f i = j)) x.val,begin
    show sum univ (λ (j : fin (n + 1)), sum (univ.filter (λ i, f i = j)) (x.val)) = 1,
    rw ←finset.sum_bind,
    {
        have H : finset.bind univ (λ (x : fin (n + 1)), filter (λ (i : fin (m + 1)), f i = x) univ) = univ
        := begin
            apply ext.2,
            simp,
            intro i,
            exact exists.intro (f i) (eq.refl (f i)),
        end,
        rw H,
        exact x.property,
    },
    {
        intros x hx y hy xney,
        apply ext.2, simp,
        intros i hfi,
        rw hfi,
        exact xney
    }
 end⟩

lemma induced_map_comp {l m n : ℕ} (f : fin (l+1) → fin (m+1)) (g : fin (m+1) → fin (n+1))
: induced_map (g ∘ f) = (induced_map g) ∘ (induced_map f)
:= begin
unfold induced_map,
apply funext,
intro x,
simp,
apply funext,
intro j,
rw ←finset.sum_bind,
{
    have H : finset.bind (filter (λ (i : fin (m + 1)), g i = j) univ)
         (λ (x : fin (m + 1)), filter (λ (i : fin (l + 1)), f i = x) univ) = filter (λ (i : fin (l + 1)), g (f i) = j) univ
         := begin
         apply ext.2, simp
         end,
    rw H
},
{
    intros i hi k hk inek,
    apply ext.2, simp,
    intros x hx,
    rw hx, exact inek
}
end

definition sum_map {m n : ℕ} (f : fin m → fin n) : (ℝ≥0^m) → (ℝ≥0^n)
:= λ x j, sum (univ.filter (λ i, f i = j)) x

lemma commuting_square {m n : ℕ} (f : fin (m+1) → fin (n+1))
: subtype.val ∘ (induced_map f) = (sum_map f) ∘ subtype.val
:= rfl

lemma continuous.pi_mk {X I : Type*} {Y : I → Type*}
[t₁ : topological_space X] [t₂ : Πi, topological_space (Y i)] (f : Πi, X → (Y i)) (H : Πi, continuous (f i))
: continuous (λ x i, f i x) :=
begin
let YY := (Πi, Y i),
apply continuous_Sup_rng,
intros t ht,
cases ht with i hi,
simp at *,
rw hi,
apply continuous_induced_rng,
unfold function.comp,
exact H i,
end

lemma continuous.pi_proj {I : Type*} {Y : I → Type*} [Πi, topological_space (Y i)]
(i : I) : continuous (λ y : Πj, Y j, y i) :=
begin
apply continuous_Sup_dom _ continuous_induced_dom,
existsi i,
simp
end

lemma continuous_sums {α : Type*} [decidable_eq α] {s : finset α} : continuous (λ x : (α → ℝ≥0), s.sum x) :=
begin
apply finset.induction_on s,
{
    have triv : (λ (x : α → ℝ≥0), sum ∅ x) = λ (x : α → ℝ≥0), (0 : ℝ≥0)
    := begin apply funext, intro x, apply finset.sum_empty end,
    rw triv,
    apply @continuous_const _ _ _ _ _,
},
{
    intros a s ha hs,
    have triv : (λ (x : α → ℝ≥0), sum (insert a s) x) =
    ((λ (p : ℝ≥0 × ℝ≥0), p.fst + p.snd) ∘ (λ x, (x a, sum s x)))
    := begin apply funext, intro x, apply finset.sum_insert ha end,
    rw triv,
    apply continuous.comp _ nnreal.continuous_add,
    apply continuous.prod_mk _ hs,
    apply continuous.pi_proj a,
}
end

lemma continuous_sum_map {m n : ℕ} (f : fin m → fin n)
: continuous (sum_map f)
:= begin
unfold sum_map,
apply @continuous.pi_mk (ℝ≥0^m) (fin n) _ _ _ _ _,
intro j,
simp,
apply continuous_sums,
end

theorem continuous_induced_map {m n : ℕ} (f : fin (m+1) → fin (n+1))
: continuous (induced_map f)
:= begin
rw continuous_iff_induced_le,
unfold subtype.topological_space,
have triv : topological_space.induced (induced_map f) (topological_space.induced subtype.val (nnrealpown.topological_space))
 = ((topological_space.induced (induced_map f)) ∘ (topological_space.induced subtype.val)) (nnrealpown.topological_space)
:= begin
unfold function.comp,
end,
rw triv,
rw ←induced_comp,
rw commuting_square,
rw ←continuous_iff_induced_le,
apply continuous.comp continuous_induced_dom (continuous_sum_map f)
end

definition δ {n : ℕ} (i : fin (n + 1 + 1))
: standard_simplex n → standard_simplex n.succ := induced_map (simplex_category.δ i)

lemma continuous_δ {n : ℕ} (i : fin (n + 1 + 1)) : continuous (δ i)
:= continuous_induced_map (simplex_category.δ i)

end standard_simplex

namespace simplicial_set

class simplicial_set :=
(objs : Π n : ℕ, Type*)
(maps {m n : ℕ} {f : fin m → fin n} (hf : monotone f) : objs n → objs m)
(comp {l m n : ℕ} {f : fin l → fin m} {g : fin m → fin n} (hf : monotone f) (hg : monotone g)
: (maps hf) ∘ (maps hg) = (maps (monotone_comp hf hg)))

definition δ {X : simplicial_set} (n : ℕ) (i : fin (n + 1))
:= simplicial_set.maps (simplex_category.δ_monotone i)

end simplicial_set

namespace simplicial_complex

open finset finsupp simplicial_set group

definition C (n : ℕ) (X : simplicial_set) := (@simplicial_set.objs X n) →₀ ℤ

instance (n : ℕ) (X : simplicial_set) : decidable_eq (@simplicial_set.objs X n) := sorry

instance (n : ℕ) (X : simplicial_set) : add_comm_group (C n X)
 := finsupp.add_comm_group

definition induced_map {X G : Type*} [add_comm_group G] (b : X → G) (f : X →₀ ℤ) : G
 := f.support.sum (λ x, gsmul (f x) (b x))

definition boundary (n : ℕ) (X : simplicial_set) : C (n+1) X → C n X
 :=
begin
apply induced_map,
intro x,
exact sum univ (λ i : fin (n.succ), finsupp.single ((simplicial_set.δ n i) x) ((-1 : ℤ)^i.val))
end

instance (n : ℕ) (X : simplicial_set) : is_add_group_hom (boundary n X)
:= begin
sorry
end

lemma C_is_a_complex (n : ℕ) (X : simplicial_set)
: (boundary n X) ∘ (boundary (n+1) X) = (λ γ x, (@has_zero.zero (C n X) _))
begin

sorry
end

end simplicial_complex

namespace singular_set

open simplicial_set

variables {X: Type*} [topological_space X]

definition S : simplicial_set :=
{
    objs := λ n, {φ : standard_simplex.standard_simplex n → X // continuous φ},
    maps := λ m n f hf φ, ⟨φ.val ∘ standard_simplex.induced_map f,
     continuous.comp (standard_simplex.continuous_induced_map f) φ.property⟩,
    comp := λ l m n f g hf hg, funext $ assume φ, begin
    simp,
    rw function.comp.assoc,
    rw ←standard_simplex.induced_map_comp
    end
}

end singular_set

-- begin singular_homology

-- definition Hsing (n : ℕ) (X : Type*) [topological_space X] := sorry

-- end singular_homology
