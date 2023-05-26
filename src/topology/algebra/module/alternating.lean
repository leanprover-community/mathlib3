import linear_algebra.alternating
import topology.algebra.module.multilinear

/-!
-/

open function matrix
open_locale big_operators

structure continuous_alternating_map (R M N ι : Type*) [semiring R]
  [add_comm_monoid M] [module R M] [topological_space M]
  [add_comm_monoid N] [module R N] [topological_space N]
  extends continuous_multilinear_map R (λ i : ι, M) N :=
(map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0)

namespace continuous_alternating_map

section semiring

variables {R M M' N N' ι : Type*} [semiring R]
  [add_comm_monoid M] [module R M] [topological_space M]
  [add_comm_monoid M'] [module R M'] [topological_space M']
  [add_comm_monoid N] [module R N] [topological_space N]
  [add_comm_monoid N'] [module R N'] [topological_space N']
  {n : ℕ} (f g : continuous_alternating_map R M N ι)

theorem to_continuous_multilinear_map_injective :
  injective (continuous_alternating_map.to_continuous_multilinear_map :
    continuous_alternating_map R M N ι → continuous_multilinear_map R (λ i : ι, M) N)
| ⟨f, hf⟩ ⟨g, hg⟩ rfl := rfl

theorem range_to_continuous_multilinear_map :
  set.range (to_continuous_multilinear_map : continuous_alternating_map R M N ι →
    continuous_multilinear_map R (λ i : ι, M) N) =
    {f | ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), f v = 0} :=
set.ext $ λ f, ⟨λ ⟨g, hg⟩, hg ▸ g.2, λ h, ⟨⟨f, h⟩, rfl⟩⟩

instance continuous_map_class :
  continuous_map_class (continuous_alternating_map R M N ι) (ι → M) N :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, to_continuous_multilinear_map_injective $ fun_like.ext' h,
  map_continuous := λ f, f.cont }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def simps.apply (f : continuous_alternating_map R M N ι) : (ι → M) → N := f

initialize_simps_projections continuous_alternating_map
  (-to_continuous_multilinear_map, to_continuous_multilinear_map_to_multilinear_map_to_fun → apply)

@[continuity] lemma coe_continuous : continuous ⇑f := f.cont

@[simp] lemma coe_to_continuous_multilinear_map : ⇑f.to_continuous_multilinear_map = f := rfl
@[simp] lemma coe_mk (f : continuous_multilinear_map R (λ _ : ι, M) N) (h) : ⇑(mk f h) = f := rfl

@[ext] theorem ext {f g : continuous_alternating_map R M N ι} (H : ∀ x, f x = g x) : f = g :=
fun_like.ext _ _ H

theorem ext_iff {f g : continuous_alternating_map R M N ι} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

@[simps { simp_rhs := true }]
def to_alternating_map : alternating_map R M N ι := { .. f }

lemma to_alternating_map_injective :
  injective (to_alternating_map : continuous_alternating_map R M N ι → alternating_map R M N ι) :=
λ f g h, fun_like.ext' $ by convert fun_like.ext'_iff.1 h

@[simp] theorem range_to_alternating_map :
  set.range (to_alternating_map : continuous_alternating_map R M N ι → alternating_map R M N ι) =
    {f | continuous f} :=
set.ext $ λ f, ⟨λ ⟨g, hg⟩, hg ▸ g.cont, λ h, ⟨{ cont := h, .. f}, fun_like.ext' rfl⟩⟩

@[simp] lemma map_add [decidable_eq ι] (m : ι → M) (i : ι) (x y : M) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.map_add' m i x y

@[simp] lemma map_smul [decidable_eq ι] (m : ι → M) (i : ι) (c : R) (x : M) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.map_smul' m i c x

lemma map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
f.to_multilinear_map.map_coord_zero i h

@[simp] lemma map_update_zero [decidable_eq ι] (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
f.to_multilinear_map.map_update_zero m i

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
f.to_multilinear_map.map_zero

lemma map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_zero_of_eq' v i j h hij

lemma map_eq_zero_of_not_injective (v : ι → M) (hv : ¬function.injective v) : f v = 0 :=
f.to_alternating_map.map_eq_zero_of_not_injective v hv

/-- Restrict the codomain of a continuous multilinear map to a submodule. -/
@[simps]
def cod_restrict (f : continuous_alternating_map R M N ι) (p : submodule R N) (h : ∀ v, f v ∈ p) :
  continuous_alternating_map R M p ι :=
{ to_continuous_multilinear_map := f.1.cod_restrict p h,
  .. f.to_alternating_map.cod_restrict p h }

instance : has_zero (continuous_alternating_map R M N ι) :=
⟨⟨0, (0 : alternating_map R M N ι).map_eq_zero_of_eq⟩⟩

instance : inhabited (continuous_alternating_map R M N ι) := ⟨0⟩

@[simp] lemma coe_zero : ⇑(0 : continuous_alternating_map R M N ι) = 0 := rfl

@[simp] lemma to_continuous_multilinear_map_zero :
  (0 : continuous_alternating_map R M N ι).to_continuous_multilinear_map = 0 :=
rfl

@[simp] lemma to_alternating_map_zero :
  (0 : continuous_alternating_map R M N ι).to_alternating_map = 0 :=
rfl

section has_smul

variables {R' R'' A : Type*} [monoid R'] [monoid R''] [semiring A]
  [module A M] [module A N]
  [distrib_mul_action R' N] [has_continuous_const_smul R' N] [smul_comm_class A R' N]
  [distrib_mul_action R'' N] [has_continuous_const_smul R'' N] [smul_comm_class A R'' N]

instance : has_smul R' (continuous_alternating_map A M N ι) :=
⟨λ c f, ⟨c • f.1, (c • f.to_alternating_map).map_eq_zero_of_eq⟩⟩

@[simp] lemma coe_smul (f : continuous_alternating_map A M N ι) (c : R'):
  ⇑(c • f) = c • f := rfl

lemma smul_apply (f : continuous_alternating_map A M N ι) (c : R') (v : ι → M) :
  (c • f) v = c • f v := rfl

@[simp] lemma to_continuous_multilinear_map_smul (c : R') (f : continuous_alternating_map A M N ι) :
  (c • f).to_continuous_multilinear_map = c • f.to_continuous_multilinear_map :=
rfl

@[simp] lemma to_alternating_map_smul (c : R') (f : continuous_alternating_map A M N ι) :
  (c • f).to_alternating_map = c • f.to_alternating_map :=
rfl

instance [smul_comm_class R' R'' N] :
  smul_comm_class R' R'' (continuous_alternating_map A M N ι) :=
⟨λ c₁ c₂ f, ext $ λ x, smul_comm _ _ _⟩

instance [has_smul R' R''] [is_scalar_tower R' R'' N] :
  is_scalar_tower R' R'' (continuous_alternating_map A M N ι) :=
⟨λ c₁ c₂ f, ext $ λ x, smul_assoc _ _ _⟩

instance [distrib_mul_action R'ᵐᵒᵖ N] [is_central_scalar R' N] :
  is_central_scalar R' (continuous_alternating_map A M N ι) :=
⟨λ c₁ f, ext $ λ x, op_smul_eq_smul _ _⟩

instance : mul_action R' (continuous_alternating_map A M N ι) :=
to_continuous_multilinear_map_injective.mul_action to_continuous_multilinear_map (λ _ _, rfl)

end has_smul

section has_continuous_add
variable [has_continuous_add N]

instance : has_add (continuous_alternating_map R M N ι) :=
⟨λ f g, ⟨f.1 + g.1, (f.to_alternating_map + g.to_alternating_map).map_eq_zero_of_eq⟩⟩

@[simp] lemma coe_add : ⇑(f + g) = f + g := rfl

@[simp] lemma add_apply (v : ι → M) : (f + g) v = f v + g v := rfl

@[simp] lemma to_continuous_multilinear_map_add (f g : continuous_alternating_map R M N ι) :
  (f + g).1 = f.1 + g.1 :=
rfl

@[simp] lemma to_alternating_map_add (f g : continuous_alternating_map R M N ι) :
  (f + g).to_alternating_map = f.to_alternating_map + g.to_alternating_map :=
rfl

instance add_comm_monoid : add_comm_monoid (continuous_alternating_map R M N ι) :=
to_continuous_multilinear_map_injective.add_comm_monoid _ rfl (λ _ _, rfl) (λ _ _, rfl)

/-- Evaluation of a `continuous_multilinear_map` at a vector as an `add_monoid_hom`. -/
def apply_add_hom (v : ι → M) : continuous_alternating_map R M N ι →+ N :=
⟨λ f, f v, rfl, λ _ _, rfl⟩

@[simp] lemma sum_apply {α : Type*} (f : α → continuous_alternating_map R M N ι)
  (m : ι → M) {s : finset α} : (∑ a in s, f a) m = ∑ a in s, f a m :=
(apply_add_hom m).map_sum f s

def to_multilinear_add_hom :
  continuous_alternating_map R M N ι →+ continuous_multilinear_map R (λ _ : ι, M) N :=
⟨λ f, f.1, rfl, λ _ _, rfl⟩

end has_continuous_add

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map [decidable_eq ι] (m : ι → M) (i : ι) : M →L[R] N :=
f.1.to_continuous_linear_map m i

/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def prod (f : continuous_alternating_map R M N ι) (g : continuous_alternating_map R M N' ι) :
  continuous_alternating_map R M (N × N') ι :=
⟨f.1.prod g.1, (f.to_alternating_map.prod g.to_alternating_map).map_eq_zero_of_eq⟩

@[simp] lemma prod_apply
  (f : continuous_alternating_map R M N ι) (g : continuous_alternating_map R M N' ι) (m : ι → M) :
  (f.prod g) m = (f m, g m) := rfl

/-- Combine a family of continuous multilinear maps with the same domain and codomains `M' i` into a
continuous multilinear map taking values in the space of functions `Π i, M' i`. -/
def pi {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)] [Π i, topological_space (M' i)]
  [Π i, module R (M' i)] (f : Π i, continuous_alternating_map R M (M' i) ι) :
  continuous_alternating_map R M (Π i, M' i) ι :=
⟨continuous_multilinear_map.pi (λ i, (f i).1),
  (alternating_map.pi (λ i, (f i).to_alternating_map)).map_eq_zero_of_eq⟩

@[simp] lemma coe_pi {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, topological_space (M' i)] [Π i, module R (M' i)]
  (f : Π i, continuous_alternating_map R M (M' i) ι) :
  ⇑(pi f) = λ m j, f j m :=
rfl

lemma pi_apply {ι' : Type*} {M' : ι' → Type*} [Π i, add_comm_monoid (M' i)]
  [Π i, topological_space (M' i)] [Π i, module R (M' i)]
  (f : Π i, continuous_alternating_map R M (M' i) ι) (m : ι → M) (j : ι') :
  pi f m j = f j m :=
rfl

section
variables (R M)

/-- The evaluation map from `ι → M₂` to `M₂` is multilinear at a given `i` when `ι` is subsingleton.
-/
@[simps to_continuous_multilinear_map apply]
def of_subsingleton [subsingleton ι] (i' : ι) : continuous_alternating_map R M M ι :=
{ to_continuous_multilinear_map := continuous_multilinear_map.of_subsingleton R _ i',
  .. alternating_map.of_subsingleton R _ i' }

@[simp] lemma of_subsingleton_to_alternating_map [subsingleton ι] (i' : ι) :
  (of_subsingleton R M i').to_alternating_map = alternating_map.of_subsingleton R M i' :=
rfl

variable (ι)

/-- The constant map is multilinear when `ι` is empty. -/
@[simps to_continuous_multilinear_map apply]
def const_of_is_empty [is_empty ι] (m : N) : continuous_alternating_map R M N ι :=
{ to_continuous_multilinear_map := continuous_multilinear_map.const_of_is_empty R (λ _, M) m,
  .. alternating_map.const_of_is_empty R M ι m }

@[simp] lemma const_of_is_empty_to_alternating_map [is_empty ι] (m : N) :
  (const_of_is_empty R M ι m).to_alternating_map = alternating_map.const_of_is_empty R M ι m :=
rfl

end

/-- If `g` is continuous multilinear and `f` is a collection of continuous linear maps,
then `g (f₁ m₁, ..., fₙ mₙ)` is again a continuous multilinear map, that we call
`g.comp_continuous_linear_map f`. -/
def comp_continuous_linear_map
  (g : continuous_alternating_map R M N ι) (f : M' →L[R] M) :
  continuous_alternating_map R M' N ι :=
{ to_continuous_multilinear_map := g.1.comp_continuous_linear_map (λ _, f),
  .. g.to_alternating_map.comp_linear_map (f : M' →ₗ[R] M) }

@[simp] lemma comp_continuous_linear_map_apply (g : continuous_alternating_map R M N ι)
  (f : M' →L[R] M) (m : ι → M') :
  g.comp_continuous_linear_map f m = g (f ∘ m) :=
rfl

/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def _root_.continuous_linear_map.comp_continuous_alternating_map
  (g : N →L[R] N') (f : continuous_alternating_map R M N ι) :
  continuous_alternating_map R M N' ι :=
{ to_continuous_multilinear_map := g.comp_continuous_multilinear_map f.1,
  .. (g : N →ₗ[R] N').comp_alternating_map f.to_alternating_map }

@[simp] lemma _root_.continuous_linear_map.comp_continuous_alternating_map_coe (g : N →L[R] N')
  (f : continuous_alternating_map R M N ι) :
  ⇑(g.comp_continuous_alternating_map f) = g ∘ f :=
rfl

def _root_.continuous_linear_equiv.continuous_alternating_map_comp (e : M ≃L[R] M') :
  continuous_alternating_map R M N ι ≃ continuous_alternating_map R M' N ι :=
{ to_fun := λ f, f.comp_continuous_linear_map ↑e.symm,
  inv_fun := λ f, f.comp_continuous_linear_map ↑e,
  left_inv := λ f, by { ext, simp [(∘)] },
  right_inv := λ f, by { ext, simp [(∘)] } }

def _root_.continuous_linear_equiv.comp_continuous_alternating_map (e : N ≃L[R] N') :
  continuous_alternating_map R M N ι ≃ continuous_alternating_map R M N' ι :=
{ to_fun := (e : N →L[R] N').comp_continuous_alternating_map,
  inv_fun := (e.symm : N' →L[R] N).comp_continuous_alternating_map,
  left_inv := λ f, by { ext, simp [(∘)] },
  right_inv := λ f, by { ext, simp [(∘)] } }

def _root_.continuous_linear_equiv.continuous_alternating_map_congr
  (e : M ≃L[R] M') (e' : N ≃L[R] N') :
  continuous_alternating_map R M N ι ≃ continuous_alternating_map R M' N' ι :=
e.continuous_alternating_map_comp.trans e'.comp_continuous_alternating_map

/-- `continuous_multilinear_map.pi` as an `equiv`. -/
@[simps]
def pi_equiv {ι' : Type*} {N : ι' → Type*} [Π i, add_comm_monoid (N i)]
  [Π i, topological_space (N i)] [Π i, module R (N i)] :
  (Π i, continuous_alternating_map R M (N i) ι) ≃
  continuous_alternating_map R M (Π i, N i) ι :=
{ to_fun := pi,
  inv_fun := λ f i, (continuous_linear_map.proj i : _ →L[R] N i).comp_continuous_alternating_map f,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
lemma cons_add (f : continuous_alternating_map R M N (fin (n + 1)))
  (m : fin n → M) (x y : M) :
  f (fin.cons (x+y) m) = f (fin.cons x m) + f (fin.cons y m) :=
f.to_multilinear_map.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
lemma vec_cons_add (f : continuous_alternating_map R M N (fin (n + 1)))
  (m : fin n → M) (x y : M) :
  f (vec_cons (x+y) m) = f (vec_cons x m) + f (vec_cons y m) :=
f.to_multilinear_map.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
lemma cons_smul
  (f : continuous_alternating_map R M N (fin (n + 1))) (m : fin n → M) (c : R) (x : M) :
  f (fin.cons (c • x) m) = c • f (fin.cons x m) :=
f.to_multilinear_map.cons_smul m c x

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
lemma vec_cons_smul
  (f : continuous_alternating_map R M N (fin (n + 1))) (m : fin n → M) (c : R) (x : M) :
  f (vec_cons (c • x) m) = c • f (vec_cons x m) :=
f.to_multilinear_map.cons_smul m c x

lemma map_piecewise_add [decidable_eq ι] (m m' : ι → M) (t : finset ι) :
  f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
f.to_multilinear_map.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [decidable_eq ι] [fintype ι] (m m' : ι → M) :
  f (m + m') = ∑ s : finset ι, f (s.piecewise m m') :=
f.to_multilinear_map.map_add_univ _ _

section apply_sum

open fintype finset

variables {α : ι → Type*} [fintype ι] [decidable_eq ι] (g' : Π i, α i → M) (A : Π i, finset (α i))

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the
sum of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/

lemma map_sum_finset : f (λ i, ∑ j in A i, g' i j) = ∑ r in pi_finset A, f (λ i, g' i (r i)) :=
f.to_multilinear_map.map_sum_finset _ _

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
lemma map_sum [∀ i, fintype (α i)] : f (λ i, ∑ j, g' i j) = ∑ r : Π i, α i, f (λ i, g' i (r i)) :=
f.to_multilinear_map.map_sum _

end apply_sum

section restrict_scalar

variables (R) {A : Type*} [semiring A] [has_smul R A] [module A M]
  [module A N] [is_scalar_tower R A M] [is_scalar_tower R A N]

/-- Reinterpret an `A`-multilinear map as an `R`-multilinear map, if `A` is an algebra over `R`
and their actions on all involved modules agree with the action of `R` on `A`. -/
def restrict_scalars (f : continuous_alternating_map A M N ι) :
  continuous_alternating_map R M N ι :=
{ to_continuous_multilinear_map := f.1.restrict_scalars R,
  .. f }

@[simp] lemma coe_restrict_scalars (f : continuous_alternating_map A M N ι) :
  ⇑(f.restrict_scalars R) = f := rfl

end restrict_scalar

end semiring

section ring

variables {R M M' N N' ι : Type*} [ring R]
  [add_comm_group M] [module R M] [topological_space M]
  [add_comm_group M'] [module R M'] [topological_space M']
  [add_comm_group N] [module R N] [topological_space N]
  [add_comm_group N'] [module R N'] [topological_space N']
  {n : ℕ} (f g : continuous_alternating_map R M N ι)

@[simp] lemma map_sub [decidable_eq ι] (m : ι → M) (i : ι) (x y : M) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
f.to_multilinear_map.map_sub _ _ _ _

section topological_add_group
variable [topological_add_group N]

instance : has_neg (continuous_alternating_map R M N ι) :=
⟨λ f,
  { to_continuous_multilinear_map := -f.1,
    .. -f.to_alternating_map }⟩

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl

lemma neg_apply (m : ι → M) : (-f) m = - (f m) := rfl

instance : has_sub (continuous_alternating_map R M N ι) :=
⟨λ f g,
  { to_continuous_multilinear_map := f.1 - g.1,
    .. f.to_alternating_map - g.to_alternating_map }⟩

@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl

lemma sub_apply (m : ι → M) : (f - g) m = f m - g m := rfl

instance : add_comm_group (continuous_alternating_map R M N ι) :=
to_continuous_multilinear_map_injective.add_comm_group _
  rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)

end topological_add_group

end ring

section comm_semiring

variables {R M M' N N' ι : Type*} [comm_semiring R]
  [add_comm_monoid M] [module R M] [topological_space M]
  [add_comm_monoid M'] [module R M'] [topological_space M']
  [add_comm_monoid N] [module R N] [topological_space N]
  [add_comm_monoid N'] [module R N'] [topological_space N']
  {n : ℕ} (f g : continuous_alternating_map R M N ι)

lemma map_piecewise_smul [decidable_eq ι] (c : ι → R) (m : ι → M) (s : finset ι) :
  f (s.piecewise (λ i, c i • m i) m) = (∏ i in s, c i) • f m :=
f.to_multilinear_map.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : ι → M) :
  f (λ i, c i • m i) = (∏ i, c i) • f m :=
f.to_multilinear_map.map_smul_univ _ _

end comm_semiring

section distrib_mul_action

variables {R A M N ι : Type*} [monoid R] [semiring A]
  [add_comm_monoid M] [add_comm_monoid N]
  [topological_space M] [topological_space N]
  [module A M] [module A N]
  [distrib_mul_action R N] [has_continuous_const_smul R N] [smul_comm_class A R N]

instance [has_continuous_add N] : distrib_mul_action R (continuous_alternating_map A M N ι) :=
function.injective.distrib_mul_action
  ⟨to_continuous_multilinear_map, rfl, λ _ _, rfl⟩
  to_continuous_multilinear_map_injective (λ _ _, rfl)

end distrib_mul_action

section module

variables {R A M N ι : Type*} [semiring R] [semiring A]
  [add_comm_monoid M] [add_comm_monoid N]
  [topological_space M] [topological_space N] [has_continuous_add N]
  [module A M] [module A N]
  [module R N] [has_continuous_const_smul R N] [smul_comm_class A R N]

/-- The space of continuous multilinear maps over an algebra over `R` is a module over `R`, for the
pointwise addition and scalar multiplication. -/
instance : module R (continuous_alternating_map A M N ι) :=
function.injective.module _ ⟨to_continuous_multilinear_map, rfl, λ _ _, rfl⟩
  to_continuous_multilinear_map_injective (λ _ _, rfl)

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
@[simps] def to_continuous_multilinear_map_linear :
  continuous_alternating_map A M N ι →ₗ[R] continuous_multilinear_map A (λ i : ι, M) N :=
{ to_fun    := to_continuous_multilinear_map,
  map_add'  := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

/-- `continuous_multilinear_map.pi` as a `linear_equiv`. -/
@[simps {simp_rhs := tt}]
def pi_linear_equiv {ι' : Type*} {M' : ι' → Type*}
  [Π i, add_comm_monoid (M' i)] [Π i, topological_space (M' i)] [∀ i, has_continuous_add (M' i)]
  [Π i, module R (M' i)] [Π i, module A (M' i)] [∀ i, smul_comm_class A R (M' i)]
  [Π i, has_continuous_const_smul R (M' i)] :
  (Π i, continuous_alternating_map A M (M' i) ι) ≃ₗ[R]
    continuous_alternating_map A M (Π i, M' i) ι :=
{ map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl,
  .. pi_equiv }

end module

section smul_right

variables {R A M N ι : Type*} [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N] [topological_space R] [topological_space M]
  [topological_space N] [has_continuous_smul R N] (f : continuous_alternating_map R M R ι) (z : N)

/-- Given a continuous `R`-multilinear map `f` taking values in `R`, `f.smul_right z` is the
continuous multilinear map sending `m` to `f m • z`. -/
@[simps to_continuous_multilinear_map apply] def smul_right : continuous_alternating_map R M N ι :=
{ to_continuous_multilinear_map := f.1.smul_right z,
  .. f.to_alternating_map.smul_right z }

end smul_right

end continuous_alternating_map

namespace continuous_multilinear_map

variables {R M N ι : Type*} [semiring R]
  [add_comm_monoid M] [module R M] [topological_space M]
  [add_comm_group N] [module R N] [topological_space N]
  [topological_add_group N] [fintype ι] [decidable_eq ι]
  (f g : continuous_multilinear_map R (λ _ : ι, M) N)

-- note: squeezed simps to make it compile faster
@[simps apply_to_continuous_multilinear_map { attrs := [] }]
def alternatization :
  continuous_multilinear_map R (λ i : ι, M) N →+ continuous_alternating_map R M N ι :=
{ to_fun := λ f,
    { to_continuous_multilinear_map := ∑ (σ : equiv.perm ι), σ.sign • f.dom_dom_congr σ,
      map_eq_zero_of_eq' := λ v i j hv hne, by simpa only [multilinear_map.alternatization_apply,
        multilinear_map.to_fun_eq_coe, coe_coe, sum_apply, alternating_map.to_fun_eq_coe]
        using f.1.alternatization.map_eq_zero_of_eq' v i j hv hne },
  map_zero' := by { ext, simp only [sum_apply, smul_apply, dom_dom_congr_apply,
    continuous_alternating_map.coe_mk, zero_apply, smul_zero, finset.sum_const_zero,
    continuous_alternating_map.coe_zero, pi.zero_apply] },
  map_add' := λ _ _, by { ext, simp only [finset.sum_add_distrib,
    continuous_alternating_map.coe_mk, continuous_alternating_map.coe_add,
    pi.add_apply, add_apply, sum_apply, smul_apply, dom_dom_congr_apply, smul_add] } }

lemma alternatization_apply_apply (v : ι → M) :
  alternatization f v = ∑ σ : equiv.perm ι, σ.sign • f (v ∘ σ) :=
by simp only [alternatization, add_monoid_hom.coe_mk, continuous_alternating_map.coe_mk, sum_apply,
  smul_apply, dom_dom_congr_apply]

@[simp]
lemma alternatization_apply_to_alternating_map :
  (alternatization f).to_alternating_map = f.1.alternatization :=
by { ext v, simp [alternatization_apply_apply, multilinear_map.alternatization_apply] }

end continuous_multilinear_map

