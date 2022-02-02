import combinatorics.hales_jewett
import combinatorics.pigeonhole
import combinatorics.to_mathlib
/-
# Partition regularity of (m,p,c)-sets

One basic result in additive Ramsey theory is strengthened van der Waerden: for any `p c : ℕ`,
whenever the positive naturals `ℕ⁺` are finitely coloured, there exists `n, d : ℕ⁺` such that
`c * d`, `n`, `n + d`, ... `n + p*d` all have the same colour (we'll call a collection of this form
an 'AP with common difference'). In 1973, Deuber introduced the notion of '`(m,p,c)`-set' (which
reduces to "AP with common difference" in the case `m=2`) and proved the corresponding theorem
for `(m,p,c)`-sets. More precisely, for any `m, p, c` there exists `n, q, d` such that whenever the
naturals are finitely colored, every `n, q, d`-set contains a monochromatic `m, p, c`-set. (Rado's
theorem implies that the notion of `(m,p,c)`-set is in some sense as general as possible for this to
be true.)

This file contains a formalisation of this result. The basic structure of the proof is standard:
we fix a finite number of colors and show that for any `r` there exists `n, q, d` such that any
`(n, q, d)`-set contains an `(r, p, c)`-set where every row is monochromatic. This is sufficient,
since taking `r` large enough guarantees that at least some colour is shared by at least `m` rows.
The proof then proceeds by induction on `r`, using the extended Hales-Jewett theorem in the
inductive step.

But many of the details are non-standard.

- We work with an arbitrary `[comm_monoid_with_zero R]` instead of the integers.

- In place of `{-p, ..., p}`, we work with a general finite subset `p : set R`.

- We allow arbitrary `c : R` and bundle the pair `(p, c)` in a structure `P R`. Henceforth we just
write `p` for this pair.

- Instead of working with `(m, p)`-sets embedded in `R`, we work with the subset of `fin m → R`
which parametrises such a set. The former perspective is dealt with in
`combinatorics/concrete_deuber`.

The proof relies on several different methods of finding an `(m, p)`-set inside an
`(n, q)`-set. We abstract these methods in a structure `inc R m n`. An element `f : inc R m n`
in particular determines a function `f.map_vec : (fin m → R) → (fin n → R)`, and with an additional
assumption (`f.small q`) this function takes the 'abstract' `(m, p)`-set inside the abstract
`(n, p * q)`-set.

Much of the work of the proof is thus delegated to defining various 'inclusions' `f : inc R m n`.
Specifically:

- An injective monotone function `g : fin m ↪o fin m` determines
`order_embedding.inc g : inc R m n`. This corresponds to deleting some rows from an `(m,p)`-set;
it's used to go from 'each row is monochromatic' to 'all rows have the same colour'.

- We can compose inclusions using `inc.comp : inc R n k → inc R m n → inc R m k`. This is used in
several parts of the proof: it corresponds to the idea that from `s ⊆ t ⊆ u` we may deduce `s ⊆ u`.

- `inc.scaling` scales `fin m → R` up by some factor `c : R`. This is used in the inductive step,
to make sure that some numbers are multiples of `c`.

- `inc.extend` gets us from `inc R m n` to `inc R (m+1) (n+1)`. This is used in the inductive step,
to make one more row monochromatic.

- `inc_of_surj` gives us `inc R m n` from a 'partial surjection' `fin n → option (fin m)`.
Essentially, this simultaneously deletes some elements of `fin n` and merges some others. It is a
bit messy since we also need to reorder `fin m`...

One has to be a bit careful when stating the main results to avoid making them vacuous. For example,
the `(m, p, c)`-set determined by the zero `m`-tuple `(0, …, 0)` is just `{0}`, which is always
monochromatic. So really the interesting result is that one can find non-zero `m`-tuples which
determine monochromatic sets. One avoids this trap when saying that the monochromatic
`(m, p, c)`-set can be found in an arbitrary `(n, q, d)`-set, since the latter set can be chosen not
to contain `0`.

In our formulation another trap is the `c = 0` case. Every `(n, q, 0)`-set contains `0`, and there
is a trivial inclusion `inc m n` which sends every `v : fin m → R` to `0`. We get around this by
making the main theorem `deuber` return a power `p^l` of `p` isntead of an arbitrary `q`; as long
as `p.C ≠ 0` we then have `(p^l).C ≠ 0` in cases of interest.

-/

noncomputable theory
open option function combinatorics
open_locale classical

variables (R : Type*) [comm_monoid_with_zero R]

@[ext] structure P :=
(set : set R)
(C : R)
(finite : set.finite)
(zero_mem : (0 : R) ∈ set)
(C_mem : C ∈ set)

instance : comm_monoid (P R) :=
{ mul := λ p q,
  { set := set.image2 (*) p.set q.set,
    C := p.C * q.C,
    finite := set.finite.image2 _ p.finite q.finite,
    zero_mem := ⟨0, 0, p.zero_mem, q.zero_mem, mul_zero 0⟩,
    C_mem := set.mem_image2_of_mem p.C_mem q.C_mem },
  mul_assoc := λ p q r, P.ext _ _ (set.image2_assoc mul_assoc) (mul_assoc _ _ _),
  one :=
    { set := {0, 1},
      C := 1,
      finite := set.finite.insert _ (set.finite_singleton _),
      zero_mem := set.mem_insert 0 {1},
      C_mem := set.mem_insert_of_mem 0 rfl },
  one_mul := λ p, begin ext, split,
      { rintro ⟨_, _, rfl | rfl | _, hp, rfl⟩,
        { rw zero_mul, apply p.zero_mem }, { erw one_mul, exact hp } },
      { intro hp, exact ⟨_, _, P.C_mem _, hp, one_mul _⟩, },
      { exact one_mul p.C },
    end,
  mul_one := λ p, begin ext, split,
      { rintro ⟨_, _, hp, rfl | rfl | _, rfl⟩,
        { rw mul_zero, apply p.zero_mem }, { erw mul_one, exact hp } },
      { intro hp, exact ⟨_, _, hp, P.C_mem _, mul_one _⟩, },
      { exact mul_one p.C },
    end,
  mul_comm := λ a b, P.ext _ _ (by { change set.image2 _ _ _ = set.image2 _ _ _,
    erw set.image2_swap, simp_rw [mul_comm] }) (mul_comm _ _) }

variables (m n k : ℕ) (p q r : P R)

@[simp] lemma mul_C : (p * q).C = p.C * q.C := rfl
@[simp] lemma one_C : (1 : P R).C = 1 := rfl

@[ext] structure inc :=
(emb : fin m →o fin n)
(mat : fin n → option (R × fin m))
(le_emb : ∀ {j r i}, (r, i) ∈ mat j → j ≤ emb i) -- want to join this with mat_mem i think

variables {R m n}

structure inc.small (f : inc R m n) : Prop :=
(mat_mem : ∀ {j r i}, (r, i) ∈ f.mat j → r ∈ p.set)
(mat_emb : ∀ i, f.mat (f.emb i) = some (p.C, i))

variables (m)
def small_vec : set (fin m → R) := { v | ∀ i, v i ∈ p.set }
variable {m}
def row (i : fin m) : set (fin m → R) := small_vec m p ∩ { v | v i = p.C ∧ ∀ j, v j ≠ 0 → j ≤ i }

variables {m n k p q r}

def inc.map_vec (f : inc R m n) (v : fin m → R) (j : fin n) : R :=
(f.mat j).elim 0 (λ x, v x.snd * x.fst)

lemma inc.map_vec_none {f : inc R m n} {v : fin m → R} {j : fin n} (h : f.mat j = none) :
  f.map_vec v j = 0 :=
by rw [inc.map_vec, h, option.elim]

lemma inc.map_vec_some {f : inc R m n} {v : fin m → R} {j i r} (h : f.mat j = some (r, i)) :
  f.map_vec v j = v i * r :=
by rw [inc.map_vec, h, option.elim]

lemma small_map {f : inc R m n} {v : fin m → R} (hf : f.small q) (hv : v ∈ small_vec m p) :
  f.map_vec v ∈ small_vec n (p * q) :=
begin
  intro j,
  rcases ho : f.mat j with _ | ⟨r, i⟩,
  { rw inc.map_vec_none ho, apply P.zero_mem },
  { rw inc.map_vec_some ho, exact set.mem_image2_of_mem (hv _) (hf.mat_mem ho) },
end

lemma inc.map_row {i : fin m} {f : inc R m n} {v : fin m → R} (hf : f.small q) (hv : v ∈ row p i) :
  f.map_vec v ∈ row (p * q) (f.emb i) :=
⟨small_map hf hv.1, by rw [inc.map_vec, hf.mat_emb i, option.elim, hv.2.1, mul_C],
λ j ne, begin
  rcases ho : f.mat j with _ | ⟨r, i⟩,
  { exfalso, rw inc.map_vec_none ho at ne, exact ne rfl },
  { rw inc.map_vec_some ho at ne,
    exact le_trans (f.le_emb ho) (f.emb.monotone $ hv.2.2 _ $ left_ne_zero_of_mul ne) }
end⟩

@[simps] def inc.comp (g : inc R n k) (f : inc R m n) : inc R m k :=
{ emb := g.emb.comp f.emb,
  mat := λ c, g.mat c >>= λ y, (f.mat y.snd).map $ λ x, (x.fst * y.fst, x.snd),
  le_emb := λ j r i h, begin
      simp only [mem_def, bind_eq_some, prod.mk.inj_iff, exists_eq_right_right, map_eq_some',
        prod.exists] at h,
      obtain ⟨r', i', hy, x, hx, rfl⟩ := h,
      exact le_trans (g.le_emb hy) (g.emb.monotone $ f.le_emb hx),
    end }

lemma inc.small.comp {g : inc R n k} {f : inc R m n} (hg : g.small q) (hf : f.small p) :
  (g.comp f).small (p * q) :=
{ mat_mem := λ j r i h, begin
      simp only [mem_def, bind_eq_some, map_eq_some', prod.mk.inj_iff, exists_eq_right_right,
        inc.comp_mat, prod.exists] at h,
      obtain ⟨r', i', hy, x, hx, rfl⟩ := h,
      exact set.mem_image2_of_mem (hf.mat_mem hx) (hg.mat_mem hy),
    end,
  mat_emb := λ i, by simp only [hf.mat_emb, hg.mat_emb, mul_C, some_bind, map_some',
    order_hom.comp_coe, inc.comp_emb, inc.comp_mat],
}

@[simp] lemma inc.comp_map (f : inc R m n) (g : inc R n k) (v : fin m → R) :
  (g.comp f).map_vec v = g.map_vec (f.map_vec v) :=
begin
  ext c,
  rcases h1 : g.mat c with _ | ⟨r, b⟩,
  { rw [inc.map_vec_none _, inc.map_vec_none h1], rw [inc.comp_mat, h1, none_bind] },
  rw inc.map_vec_some h1,
  rcases h2 : f.mat b with _ | ⟨r', a⟩,
  { rw [inc.map_vec_none _, inc.map_vec_none h2, zero_mul], rw [inc.comp_mat, h1,
      option.some_bind, h2, option.map, option.none_bind'] },
  { rw [inc.map_vec_some h2, mul_assoc], apply inc.map_vec_some,
    rw [inc.comp_mat, h1, option.some_bind, h2, option.map_some'] }
end

variables (m p)

@[simps] def scaling : inc R m m :=
{ emb := order_hom.id,
  mat := λ i, some (p.C, i),
  le_emb := by rintros j _ _ ⟨rfl, rfl⟩; refl }

lemma small_scaling : (scaling m p).small p :=
{ mat_mem := by rintros j _ _ ⟨rfl, rfl⟩; exact p.C_mem,
  mat_emb := λ _, rfl }

lemma scaling_map_vec (v : fin m → R) (i : fin m) : (scaling m p).map_vec v i = v i * p.C := rfl

variables (n) (κ : Type*) (R)

def coloring : Type* := (fin m → R) → κ

variables {R m n κ} (co : coloring R n κ)

def coloring.restrict (f : inc R m n) : coloring R m κ := λ v, co (f.map_vec v)
def coloring.mono_row (i : fin n) (k : κ) : Prop := ∀ v ∈ row p i, co v = k
def coloring.mono (k : κ) : Prop := ∀ i, co.mono_row p i k

lemma coloring.restrict_mono_row {k : κ} {i : fin m} {f : inc R m n} (hf : f.small q)
  (h : co.mono_row (p * q) (f.emb i) k) : (co.restrict f).mono_row p i k :=
λ v hv, h _ (inc.map_row hf hv)

@[simp] lemma coloring.restrict_comp (f : inc R m n) (g : inc R n k) (co : coloring R k κ) :
  co.restrict (g.comp f) = (co.restrict g).restrict f :=
by ext v; simp only [coloring.restrict, inc.comp_map]

@[simps] def order_embedding.inc (mon : fin m ↪o fin n) : inc R m n :=
{ emb := mon.to_order_hom,
  mat := λ i, (partial_inv mon i).map (prod.mk 1),
  le_emb := λ i r j h, by { simp only [mem_def, map_eq_some', prod.mk.inj_iff,
    exists_eq_right_right] at h, rw ←(partial_inv_of_injective mon.injective _ _).mp h.1, refl } }

lemma small_order_embedding {mon : fin m ↪o fin n} : mon.inc.small (1 : P R) :=
{ mat_emb := λ i, by simp only [partial_inv_left mon.injective, order_embedding.to_order_hom_coe,
    map_some', order_embedding.inc_mat, order_embedding.inc_emb, one_C],
  mat_mem := λ j r i h, by { simp only [mem_def, prod.mk.inj_iff, exists_eq_right_right,
    map_eq_some', order_embedding.inc_mat] at h, rw ←h.2, apply P.C_mem } }

@[simp] lemma emb_inc_map (mon : fin m ↪o fin n) (i : fin m) (v : fin m → R) :
  mon.inc.map_vec v (mon i) = v i :=
by rw [inc.map_vec, order_embedding.inc_mat, partial_inv_left mon.injective, map_some',
  option.elim, mul_one]

@[simps] def inc.extend (f : inc R m n) (v : fin n → option q.set) : inc R (m+1) (n+1) :=
{ emb := f.emb.succ,
  mat := fin.snoc (λ j, option.orelse ((f.mat j).map (λ x, (x.fst, x.snd.cast_succ)))
    ((v j).map (λ r, (↑r, fin.last m)))) (some (q.C, fin.last m)),
  le_emb := begin
      refine fin.last_cases _ _,
      { intros r i h, simp only [mem_def, prod.mk.inj_iff, fin.snoc_last] at h, rw ←h.2,
        simp only [order_hom.succ_apply_last] },
      intros j r, refine fin.last_cases _ _,
      { intro, rw [order_hom.succ_apply_last], apply fin.le_last },
      intros i h,
      simp only [fin.snoc_cast_succ, option.mem_orelse_iff] at h,
      rcases h with h1 | ⟨_, h1⟩,
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨⟨_, k⟩, ha, hb⟩,
        simp only [order_hom.succ_apply_cast_succ, order_embedding.le_iff_le],
        simp only [prod.mk.inj_iff, order_embedding.eq_iff_eq] at hb, rcases hb with ⟨rfl, rfl⟩,
        exact f.le_emb ha },
      { exfalso, rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨_, _, h1⟩,
        rw prod.mk.inj_iff at h1, refine ne_of_lt _ h1.2.symm, apply fin.cast_succ_lt_last }
    end }

lemma small.extend {f : inc R m n} {v : fin n → option q.set} (hf : f.small q) :
  (f.extend v).small q :=
{ mat_emb := begin
      refine fin.last_cases _ _,
      { simp only [inc.extend_mat, inc.extend_emb, fin.snoc_last, order_hom.succ_apply_last] },
      intro i,
      simp only [inc.extend_mat, inc.extend_emb, fin.snoc_cast_succ,
        order_hom.succ_apply_cast_succ],
      simp only [hf.mat_emb, map_some', some_orelse'],
    end,
  mat_mem := begin
      refine fin.last_cases _ _,
      { intros r i h,
        simp only [mem_def, fin.snoc_last, inc.extend_mat, prod.mk.inj_iff] at h,
        rw ←h.1, apply P.C_mem },
      intros j r i h,
      simp only [mem_def, fin.snoc_cast_succ, inc.extend_mat, option.mem_orelse_iff] at h,
      rcases h with h1 | ⟨_, h1⟩,
      { simp only [mem_def, prod.mk.inj_iff, map_eq_some', prod.exists] at h1,
        rcases h1 with ⟨a, b, ha, rfl, _⟩, exact hf.mat_mem ha },
      { simp only [mem_def, map_eq_some', mem_def, prod.mk.inj_iff, map_eq_some'] at h1,
        rcases h1 with ⟨_, _, rfl, _⟩, apply subtype.mem }
    end }

lemma extend_map_vec_1 {f : inc R m n} {v : fin n → option q.set} {j x} {w : fin (m+1) → R}
  (hx : v j = some x) (hf : f.mat j = none) :
  (f.extend v).map_vec w j.cast_succ = w (fin.last m) * x :=
by simp only [hf, inc.extend_mat, fin.snoc_cast_succ, hx, map_some', none_orelse', map_none',
  inc.map_vec, option.elim]

lemma extend_map_vec_2 {f : inc R m n} {v : fin n → option q.set} {j} {w : fin (m+1) → R}
  (h : v j = none) :
  (f.extend v).map_vec w j.cast_succ = f.map_vec (w ∘ fin.cast_succ) j :=
begin
  rcases ho : f.mat j with _ | ⟨r, i⟩,
  { rw [inc.map_vec_none ho, inc.map_vec_none], rw [inc.extend_mat, fin.snoc_cast_succ, ho,
      map_none', none_orelse', h, map_none'] },
  { rw inc.map_vec_some ho, apply inc.map_vec_some,
    rw [inc.extend_mat, fin.snoc_cast_succ, ho, map_some', some_orelse'] }
end

section inc_of_surj

variables {f : fin n → option (fin m)} (hf : ∀ i, ∃ j, f j = some i)
include hf

def g (i : fin m) : fin n :=
finset.max' (finset.univ.filter $ λ j, f j = some i)
((hf i).imp $ λ j hj, finset.mem_filter.mpr ⟨finset.mem_univ _, hj⟩)

variable (f)
lemma fg_eq_some (i : fin m) : f (g hf i) = some i :=
begin
  have : g hf i ∈ finset.univ.filter (λ j, f j = some i) := finset.max'_mem _ _,
  simpa only [true_and, finset.mem_univ, finset.mem_filter] using this,
end
variable {f}

@[simps] def inc_of_surj : inc R m n :=
{ emb := monotone_replacement_order_hom (fintype.card_fin _) (g hf),
  mat := λ j, (f j).elim none $ λ i,
    some (1, (monotone_replacement_equiv (fintype.card_fin _) (g hf)).symm i),
  le_emb := λ j r i hx, begin
      rw [monotone_replacement_order_hom_apply, g],
      apply finset.le_max',
      simp only [true_and, finset.mem_univ, finset.mem_filter],
      cases f j, { cases hx },
      simp only [mem_def, option.elim, prod.mk.inj_iff] at hx,
      rw [←hx.2, equiv.apply_symm_apply],
    end }

lemma small_inc_of_surj : (inc_of_surj hf).small (1 : P R) :=
{ mat_emb := λ i, by simp only [fg_eq_some f hf, monotone_replacement_order_hom_apply,
    option.elim, equiv.symm_apply_apply, one_C, inc_of_surj_emb, inc_of_surj_mat],
  mat_mem := λ j r i h, by { simp only [mem_def, inc_of_surj_mat] at h, rcases f j,
    { rintro ⟨⟩ }, { rintro ⟨⟩, apply P.C_mem } } }

lemma inc_of_surj_map_vec {i j} {w : fin m → R} (h : f j = some i) :
  (inc_of_surj hf).map_vec w j =
    w ((monotone_replacement_equiv (fintype.card_fin _) (g hf)).symm i) :=
by simp only [h, inc.map_vec, mul_one, option.elim, inc_of_surj_mat]

lemma inc_of_surj_map_vec' {j} {w : fin m → R} (h : f j = none) :
  (inc_of_surj hf).map_vec w j = 0 :=
by simp only [h, inc.map_vec, option.elim, inc_of_surj_mat]

end inc_of_surj

variables {R} (m n p q) (I : ℕ) (κ)

def large_enough : Prop := ∀ co : coloring R n κ, ∃ (f : inc R m n) (k : fin m → κ), f.small q ∧
  ∀ i, (co.restrict f).mono_row p i (k i)

lemma step (h1 : large_enough m n p q κ)
  (h2 : ∀ C : (fin I → (p * q).set) → κ, ∃ l : subspace (fin n) (p * q).set (fin I), l.is_mono C) :
  large_enough (m+1) (I+1) p (p * q) κ := λ co,
begin
  specialize h2 (λ v, co $ fin.snoc (λ i, p.C * v i) (p.C * p.C * q.C)),
  obtain ⟨l, klast, lk⟩ := h2,
  let fo : fin I → option (fin n) := λ j, (l.idx_fun j).elim (λ _, none) some,
  have fo_surj : ∀ i, ∃ j, fo j = some i,
  { intro i, refine (l.proper i).imp _, intros j hj, simp_rw [fo, hj, sum.elim_inr] },
  let nI : inc R n I := (scaling I p).comp (inc_of_surj fo_surj),
  have nI_small : nI.small p,
  { rw ←one_mul p, exact (small_scaling _ _).comp (small_inc_of_surj _) },
  specialize h1 (co.restrict (fin.cast_succ.inc.comp nI)),
  obtain ⟨mn, ksucc, mn_small, hksucc⟩ := h1,
  let fa : fin I → option (p * q).set := λ j, (l.idx_fun j).elim some (λ _, none),
  set mI : inc R (m+1) (I+1) := (nI.comp mn).extend fa with hmI,
  have mI_small : mI.small (p * q) := small.extend _,
  swap, { rw mul_comm, exact nI_small.comp mn_small },
  have map_vec_inl : ∀ {v : fin (m+1) → R} {j : fin I} {r} (h : l.idx_fun j = sum.inl r),
    mI.map_vec v j.cast_succ = v (fin.last m) * r,
  { intros v j r h,
    have : fa j = some r, simp_rw [fa, h, sum.elim_inl],
    rw [hmI, extend_map_vec_1 this],
    simp only [inc.comp_mat, inc_of_surj_mat, fo, h, option.elim, sum.elim_inl, none_bind,
      scaling_mat, some_bind, map_none'], },
  have map_vec_inr : ∀ {v : fin (m+1) → R} {j : fin I} {i} (h : l.idx_fun j = sum.inr i),
    mI.map_vec v j.cast_succ = (nI.comp mn).map_vec (v ∘ fin.cast_succ) j,
  { intros v j i h, apply extend_map_vec_2, simp_rw [fa, h, sum.elim_inr] },
  refine ⟨mI, fin.snoc ksucc klast, mI_small, fin.last_cases _ _⟩,
  { intros v hv, simp only [coloring.restrict, fin.snoc_last],
    let w := mn.map_vec (v ∘ fin.cast_succ),
    have hw : w ∈ small_vec _ (p * q) := small_map mn_small (λ _, hv.1 _),
    specialize lk
      (subtype.coind w hw ∘ (monotone_replacement_equiv (fintype.card_fin _) (g fo_surj)).symm),
    convert lk,
    rw funext_iff,
    refine fin.last_cases _ _,
    { rw [fin.snoc_last], simpa only [inc.extend_emb, order_hom.succ_apply_last, mul_assoc]
        using (inc.map_row mI_small hv).2.1 },
    intro j,
    rw [fin.snoc_cast_succ, hmI],
    rcases ho : l.idx_fun j with r | i,
    { rw [map_vec_inl ho, hv.2.1, subspace.apply_inl ho] },
    { simp only [map_vec_inr ho, subspace.apply_inr ho, inc.comp_map, scaling_map_vec],
      rw mul_comm, congr' 1, apply inc_of_surj_map_vec, rw [ho, sum.elim_inr] } },
  { intros i v hv,
    have vtail_row : v ∘ fin.cast_succ ∈ row p i,
    { refine ⟨λ _, hv.1 _, hv.2.1, _⟩, intros j hj, exact hv.2.2 j.cast_succ hj },
    simp only [fin.snoc_last, coloring.restrict],
    have : mI.map_vec v = (fin.cast_succ.inc.comp (nI.comp mn)).map_vec (v ∘ fin.cast_succ),
    { rw funext_iff, refine fin.last_cases _ _,
      { rw not.imp_symm ((inc.map_row mI_small hv).2.2 (fin.last I)) (not_le_of_lt _),
        have : (fin.cast_succ.inc.comp (nI.comp mn)).map_vec (v ∘ fin.cast_succ) ∈
          row (p * ((q * p) * 1)) _ := inc.map_row (inc.small.comp small_order_embedding
            (nI_small.comp mn_small)) vtail_row,
        exact (not.imp_symm (this.2.2 $ fin.last I) (not_le_of_lt $ fin.cast_succ_lt_last _)).symm,
        rw [inc.extend_emb, order_hom.succ_apply_cast_succ], apply fin.cast_succ_lt_last },
      { intro j, rcases ho : l.idx_fun j with r | i,
        { rw [map_vec_inl ho,
            not.imp_symm (hv.2.2 _) (not_le_of_lt $ fin.cast_succ_lt_last _), zero_mul],
          simp only [inc.comp_map, emb_inc_map],
          rw [scaling_map_vec, inc_of_surj_map_vec', zero_mul],
          rw [ho, sum.elim_inl] },
        { rw map_vec_inr ho, simp only [emb_inc_map, inc.comp_map] } } },
    rw this,
    specialize hksucc i (v ∘ fin.cast_succ) vtail_row,
    simpa only [coloring.restrict, inc.comp_map, fin.snoc_cast_succ] using hksucc }
end

theorem deuber [fintype κ] : ∃ n, ∀ co : coloring R n κ,
  ∃ (f : inc R m n), f.small (p^(fintype.card κ * m + 1)) ∧ ∃ k, (co.restrict f).mono p k :=
begin
  have : ∀ r, ∃ n, large_enough r n p (p^r) κ,
  { intro r, induction r with r ih,
    { exact ⟨0, λ co, ⟨(order_iso.refl _).to_order_embedding.inc, fin_zero_elim,
        small_order_embedding, fin_zero_elim⟩⟩ },
    obtain ⟨n, h⟩ := ih,
    haveI : fintype (p^(r+1)).set := (P.finite _).fintype,
    obtain ⟨I, hI⟩ := subspace.exists_mono_in_high_dimension_fin (p^(r+1)).set κ (fin n),
    exact ⟨I+1, step r n p _ κ I h hI⟩ },
  specialize this (fintype.card κ * m + 1),
  obtain ⟨n, hn⟩ := this,
  refine ⟨n, _⟩,
  intro co,
  specialize hn co,
  obtain ⟨f, ks, f_small, fks⟩ := hn,
  obtain ⟨k, hk : m < _⟩ := fintype.exists_lt_card_fiber_of_mul_lt_card ks _,
  swap, { simp only [fintype.card_fin, lt_add_iff_pos_right, nat.lt_one_iff] },
  refine ⟨f.comp (order_emb_of_card_le (le_of_lt hk)).inc, _, k, _⟩,
  { convert f_small.comp small_order_embedding, rw one_mul _ },
  { intro i,
    rw [coloring.restrict_comp],
    refine coloring.restrict_mono_row _ _ small_order_embedding _,
    rw mul_one, convert fks _,
    have := order_emb_mem (le_of_lt hk) i,
    simp only [true_and, finset.mem_univ, finset.mem_filter] at this,
    exact this.symm }
end
