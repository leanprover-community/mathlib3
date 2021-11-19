import combinatorics.hales_jewett
import data.fintype.sort
import combinatorics.pigeonhole

noncomputable theory
open option function combinatorics

def partial_inv_spec {α β} {f : α → β} {b : β} {a : α} (h : a ∈ partial_inv f b) : f a = b :=
by { unfold partial_inv at h, split_ifs at h with h1; cases h, exact classical.some_spec h1 }

def preorder_hom.succ {m n : ℕ} (f : fin m →ₘ fin n) : fin (m+1) →ₘ fin (n+1) :=
{ to_fun := @fin.last_cases m (λ i, fin (n+1)) (fin.last n) (λ i, (f i).cast_succ),
  monotone' := begin
    refine fin.last_cases _ _,
    { intros j ij, cases fin.eq_last_of_not_lt (not_lt_of_le ij), refl },
    intros i, refine fin.last_cases _ _,
    { intro junk, rw [fin.last_cases_last], apply fin.le_last },
    intros j ij,
    rw [fin.last_cases_cast_succ, fin.last_cases_cast_succ, order_embedding.le_iff_le],
    apply f.mono, exact ij,
  end }

@[simp] lemma preorder_hom.succ_apply_last {m n : ℕ} (f : fin m →ₘ fin n) :
  f.succ (fin.last m) = fin.last n :=
by { unfold preorder_hom.succ, simp only [preorder_hom.coe_fun_mk, fin.last_cases_last] }

@[simp] lemma preorder_hom.succ_apply_cast_succ {m n : ℕ} (f : fin m →ₘ fin n) (i : fin m) :
  f.succ (i.cast_succ) = (f i).cast_succ :=
by { unfold preorder_hom.succ, simp only [preorder_hom.coe_fun_mk, fin.last_cases_cast_succ] }

def option.disjoint {α β} (a : option α) (b : option β) : Prop := a = none ∨ b = none

lemma option.disjoint.orelse_comm {α} {a b : option α} (h : a.disjoint b) :
  (a <|> b) = (b <|> a) :=
by rcases h with rfl | rfl; simp only [orelse_none, none_orelse]

lemma option.mem_orelse {α} {a b : option α} {x : α} (h : x ∈ (a <|> b)) : x ∈ a ∨ x ∈ b :=
begin
  cases a, { right, simpa only [mem_def, none_orelse] using h }, { left, simpa only using h}
end

section bla

variables (R : Type) [monoid_with_zero R]

@[ext] structure P :=
(set : set R)
(finite : set.finite)
(zero_mem : (0 : R) ∈ set)
(one_mem : (1 : R) ∈ set)

instance : preorder (P R) := preorder.lift P.set

instance : monoid (P R) :=
{ mul := λ p q,
  { set := set.image2 (*) p.set q.set,
    finite := set.finite.image2 _ p.finite q.finite,
    zero_mem := ⟨0, 0, p.zero_mem, q.zero_mem, mul_zero 0⟩,
    one_mem := ⟨1, 1, p.one_mem, q.one_mem, mul_one 1⟩ },
  mul_assoc := λ p q r, P.ext _ _
    (by { dsimp only, rw [set.image2_image2_left, set.image2_image2_right], simp_rw mul_assoc }),
  one :=
    { set := {0, 1},
      finite := set.finite.insert _ (set.finite_singleton _),
      zero_mem := set.mem_insert 0 {1},
      one_mem := set.mem_insert_of_mem 0 rfl },
  one_mul := λ p, begin ext, split,
    { rintro ⟨_, _, rfl | rfl | _, hp, rfl⟩,
      { rw zero_mul, apply p.zero_mem }, { erw one_mul, exact hp } },
    { intro hp, exact ⟨_, _, P.one_mem _, hp, one_mul _⟩, }
  end,
  mul_one := λ p, begin ext, split,
    { rintro ⟨_, _, hp, rfl | rfl | _, rfl⟩,
      { rw mul_zero, apply p.zero_mem }, { erw mul_one, exact hp } },
    { intro hp, exact ⟨_, _, hp, P.one_mem _, mul_one _⟩, }
  end }

variables (m n k : ℕ) (p q r : P R)

structure inc : Type :=
(emb : fin m →ₘ fin n)
(mat : fin n → option (R × fin m))
(le_emb : ∀ {j r i}, (r, i) ∈ mat j → j ≤ emb i)

variables {R m n}

structure inc.small (f : inc R m n) : Prop :=
(mat_mem : ∀ {j r i}, (r, i) ∈ f.mat j → r ∈ p.set)
(mat_emb : ∀ i, f.mat (f.emb i) = some (1, i)) -- include this in 'small' in anticipation of `C`

variables (m)
def small_vec : set (fin m → R) := { v | ∀ i, v i ∈ p.set }
variable {m}
def row (i : fin m) : set (fin m → R) := small_vec m p ∩ { v | v i = 1 ∧ ∀ j, v j ≠ 0 → j ≤ i }

variables {m n k p q r}

def inc.map_vec (f : inc R m n) (v : fin m → R) (j : fin n) : R :=
(f.mat j).elim 0 (λ x, v x.snd * x.fst)

lemma small_map {f : inc R m n} {v : fin m → R} (hf : f.small q) (hv : v ∈ small_vec m p) :
  f.map_vec v ∈ small_vec n (p * q) :=
begin
  intro j,
  rw inc.map_vec,
  set o := f.mat j with ho, clear_value o, rcases o with _ | ⟨r, i⟩,
  { apply P.zero_mem },
  { exact set.mem_image2_of_mem (hv _) (hf.mat_mem ho.symm) },
end

def inc.map_row {i : fin m} {f : inc R m n} {v : fin m → R} (hf : f.small q) (hv : v ∈ row p i) :
  f.map_vec v ∈ row (p * q) (f.emb i) :=
⟨small_map hf hv.1, by simp_rw [inc.map_vec, hf.mat_emb i, option.elim, hv.2.1, one_mul],
λ j ne, begin
  rw inc.map_vec at ne,
  set o := f.mat j with ho, clear_value o, rcases o with _ | ⟨r, i⟩,
  { exfalso, exact ne rfl },
  { exact le_trans (f.le_emb ho.symm) (f.emb.monotone $ hv.2.2 _ $ left_ne_zero_of_mul ne) }
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
  mat_emb := λ i, by simp only [hf.mat_emb, hg.mat_emb, mul_one, some_bind, map_some',
    preorder_hom.comp_coe, inc.comp_emb, inc.comp_mat],
}

@[simp] lemma inc.comp_map (f : inc R m n) (g : inc R n k) (v : fin m → R) :
  (g.comp f).map_vec v = g.map_vec (f.map_vec v) :=
begin
  ext j,
  simp only [inc.map_vec, inc.comp_mat],
  set o := g.mat j, clear_value o, cases o with x,
  { refl },
  simp only [option.elim, some_bind],
  set o := f.mat x.snd, clear_value o, cases o with y,
  { simp only [map_none', option.elim, zero_mul], },
  { simp only [option.elim, map_some', mul_assoc], }
end

variables (m p n) (κ : Type) (R)

def coloring : Type := (fin m → R) → κ

variables {R m n κ} (co : coloring R n κ)

def coloring.restrict (f : inc R m n) : coloring R m κ := λ v, co (f.map_vec v)
def coloring.mono_row (i : fin n) (k : κ) : Prop := ∀ v ∈ row p i, co v = k
def coloring.mono (k : κ) : Prop := ∀ i, co.mono_row p i k

lemma coloring.restrict_mono_row {k : κ} {i : fin m} {f : inc R m n} (hf : f.small q)
  (h : co.mono_row (p * q) (f.emb i) k) : (co.restrict f).mono_row p i k :=
λ v hv, h _ (inc.map_row hf hv)

@[simps] def inc_mul : inc R m m :=
{ emb := preorder_hom.id,
  mat := λ i, some (1, i),
  le_emb := λ j r i h, by { simp only [mem_def, prod.mk.inj_iff] at h, rw h.2, refl } }

lemma small_inc_mul : (inc_mul : inc R m m).small p :=
{ mat_emb := λ _, rfl,
  mat_mem := λ j r i h,
    by { simp only [mem_def, inc_mul_mat, prod.mk.inj_iff] at h, rw ←h.1, apply P.one_mem } }

@[simps] def inc_of_emb (mon : fin m ↪o fin n) : inc R m n :=
{ emb := mon.to_preorder_hom,
  mat := λ i, (partial_inv mon i).map (prod.mk 1),
  le_emb := λ i r j h, by { simp only [mem_def, map_eq_some', prod.mk.inj_iff,
    exists_eq_right_right] at h, rw ←partial_inv_spec h.1, refl } }

lemma small_inc_of_emb (mon : fin m ↪o fin n) : (inc_of_emb mon).small p :=
{ mat_emb := λ i, by simp only [partial_inv_left mon.injective,
    order_embedding.to_preorder_hom_coe, map_some', inc_of_emb_mat, inc_of_emb_emb],
  mat_mem := λ j r i h, by { simp only [mem_def, prod.mk.inj_iff, exists_eq_right_right,
    map_eq_some', inc_of_emb_mat] at h, rw ←h.2, apply P.one_mem } }

@[simps] def inc.extend (f : inc R m n) (v : fin n → option q.set) (h : ∀ j, (v j).disjoint (f.mat j)) :
  inc R (m+1) (n+1) :=
{ emb := f.emb.succ,
  mat := @fin.last_cases n (λ _, option (R × fin (m+1))) (some (1, fin.last m))
    (λ j, (v j).map (λ r, (↑r, fin.last m)) <|> (f.mat j).map (λ x, (x.fst, x.snd.cast_succ))),
  le_emb := begin
      refine fin.last_cases _ _,
      { intros r i h, simp only [mem_def, prod.mk.inj_iff, fin.last_cases_last] at h, rw ←h.2,
        simp only [preorder_hom.succ_apply_last] },
      intros j r, refine fin.last_cases _ _,
      { intro, rw [preorder_hom.succ_apply_last], apply fin.le_last },
      intros i h,
      simp only [mem_def, fin.last_cases_cast_succ] at h,
      cases option.mem_orelse h with h1 h1,
      { exfalso, rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨_, _, h1⟩,
        rw prod.mk.inj_iff at h1, refine ne_of_lt _ h1.2.symm, apply fin.cast_succ_lt_last },
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨⟨_, k⟩, ha, hb⟩,
        simp only [preorder_hom.succ_apply_cast_succ, order_embedding.le_iff_le],
        simp only [prod.mk.inj_iff, order_embedding.eq_iff_eq] at hb, rcases hb with ⟨rfl, rfl⟩,
        exact f.le_emb ha }
    end }

def small.extend {f : inc R m n} {v : fin n → option q.set} {h : ∀ j, (v j).disjoint (f.mat j)}
  (hf : f.small q) : (f.extend v h).small q :=
{ mat_emb := begin
      refine fin.last_cases _ _,
      { simp only [inc.extend_mat, inc.extend_emb, fin.last_cases_last,
        preorder_hom.succ_apply_last] },
      intro i,
      simp only [inc.extend_mat, inc.extend_emb, fin.last_cases_cast_succ,
        preorder_hom.succ_apply_cast_succ],
      cases h (f.emb i) with h1 h2,
      { simp only [h1, none_orelse, map_none', hf.mat_emb, map_some'] },
      { rw hf.mat_emb at h2, cases h2 }
    end,
  mat_mem := begin
      refine fin.last_cases _ _,
      { intros r i h,
        simp only [mem_def, fin.last_cases_last, inc.extend_mat, prod.mk.inj_iff] at h,
        rw ←h.1, apply P.one_mem },
      intros j r i h,
      simp only [mem_def, fin.last_cases_cast_succ, inc.extend_mat] at h,
      cases option.mem_orelse h with h1 h1,
      { simp only [mem_def, map_eq_some', mem_def, prod.mk.inj_iff, map_eq_some'] at h1,
        rcases h1 with ⟨_, _, rfl, _⟩, apply subtype.mem },
      { simp only [mem_def, prod.mk.inj_iff, map_eq_some', prod.exists] at h1,
        rcases h1 with ⟨a, b, ha, rfl, _⟩, exact hf.mat_mem ha }
    end }

end bla

section ugh

parameters {R : Type} {m n : ℕ} [monoid_with_zero R] {p : P R} (f : fin n → option (fin m))
  (h : ∀ i, ∃ j, f j = some i)
include h

def m' : Type := fin m

def g (i : m') : fin n :=
finset.max' (finset.univ.filter $ λ j, f j = some i)
((h i).imp $ λ j hj, finset.mem_filter.mpr ⟨finset.mem_univ _, hj⟩)

lemma fg_eq_some (i : m') : f (g i) = some i :=
begin
  have : g i ∈ finset.univ.filter (λ j, f j = some i) := finset.max'_mem _ _,
  simpa only [true_and, finset.mem_univ, finset.mem_filter] using this,
end

lemma inj : injective g := λ i j ij, some_injective _ (by rw [←fg_eq_some, ←fg_eq_some, ij])

instance : fintype m' := fin.fintype m
instance : linear_order m' := linear_order.lift g inj

def g_mono : m' →ₘ fin n := { to_fun := g, monotone' := λ i j, id }
def mm' : fin m ≃o m' := mono_equiv_of_fin m' (fintype.card_fin m)

@[simps] def inc_of_this : inc R m n :=
{ emb := g_mono.comp (order_embedding.to_preorder_hom mm'.to_rel_embedding),
  mat := λ j, (f j).elim none $ λ i : m', some (1, mm'.symm i),
  le_emb := λ j r i hx, finset.le_max' _ _ begin
      simp only [order_embedding.to_preorder_hom_coe, true_and, rel_iso.to_rel_embedding_eq_coe,
        rel_iso.coe_coe_fn, finset.mem_univ, finset.mem_filter],
      set o := f j, clear_value o, cases o, { cases hx },
      simp only [mem_def, option.elim, prod.mk.inj_iff] at hx,
      simp only [←hx, order_iso.apply_symm_apply],
    end }

lemma small_inc_of_this : inc_of_this.small p :=
{ mat_emb := λ i, by simp only [g_mono, order_embedding.to_preorder_hom_coe,
    rel_iso.to_rel_embedding_eq_coe, rel_iso.coe_coe_fn, preorder_hom.coe_fun_mk,
    preorder_hom.comp_coe, fg_eq_some (mm' i), option.elim, order_iso.symm_apply_apply,
    inc_of_this_emb, inc_of_this_mat],
  mat_mem := λ j r i h, by { simp only [mem_def, inc_of_this_mat] at h,
    set o := f j, clear_value o, cases o, { cases h_1 }, { cases h_1, apply P.one_mem } } }

end ugh

variables {R : Type} [monoid_with_zero R] (m n I : ℕ) (p q : P R) (κ : Type)

def large_enough : Prop := ∀ co : coloring R n κ, ∃ (f : inc R m n) (k : fin m → κ), f.small q ∧
  ∀ i, (co.restrict f).mono_row p i (k i)

lemma claim (h1 : large_enough m n p q κ) (h2 : extended_HJ_works q.set κ (fin n) (fin I)) :
  large_enough (m+1) (I+1) p (p * q) κ := λ co,
begin
  specialize h2 (λ v, co $ fin.last_cases 1 (λ i, coe (v i))),
  obtain ⟨l, klast, lk⟩ := h2,
  set fo : fin I → option (fin n) := λ j, (l.idx_fun j).elim (λ _, none) some with hfo,
  let nI : inc n I (p * 1) := (inc_of_this fo _).comp (inc_mul _),
end
