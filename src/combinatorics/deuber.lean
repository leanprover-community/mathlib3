import combinatorics.hales_jewett
import data.fintype.sort
import combinatorics.pigeonhole

noncomputable theory
open option function combinatorics

def order_emb_of_card_le {m β} [linear_order β] {s : finset β} (h : m ≤ s.card) : fin m ↪o β :=
(fin.cast_le h).trans (s.order_emb_of_fin rfl)

def order_emb_mem {m β} [linear_order β] {s : finset β} (h : m ≤ s.card) (a) :
  order_emb_of_card_le h a ∈ s :=
by simp only [order_emb_of_card_le, rel_embedding.coe_trans, finset.order_emb_of_fin_mem]

def preorder_hom.succ {m n : ℕ} (f : fin m →ₘ fin n) : fin (m+1) →ₘ fin (n+1) :=
{ to_fun := fin.snoc (λ i, (f i).cast_succ) (fin.last _),
  monotone' := begin
    refine fin.last_cases _ _,
    { intros j ij, cases fin.eq_last_of_not_lt (not_lt_of_le ij), refl },
    intros i, refine fin.last_cases _ _,
    { intro junk, rw [fin.snoc_last], apply fin.le_last },
    intros j ij,
    rw [fin.snoc_cast_succ, fin.snoc_cast_succ, order_embedding.le_iff_le],
    apply f.mono, exact ij,
  end }

@[simp] lemma preorder_hom.succ_apply_last {m n : ℕ} (f : fin m →ₘ fin n) :
  f.succ (fin.last m) = fin.last n :=
by { unfold preorder_hom.succ, simp only [preorder_hom.coe_fun_mk, fin.snoc_last] }

@[simp] lemma preorder_hom.succ_apply_cast_succ {m n : ℕ} (f : fin m →ₘ fin n) (i : fin m) :
  f.succ (i.cast_succ) = (f i).cast_succ :=
by { unfold preorder_hom.succ, simp only [preorder_hom.coe_fun_mk, fin.snoc_cast_succ] }

lemma option.mem_orelse_iff {α} (a b : option α) (x : α) :
  x ∈ a.orelse b ↔ x ∈ a ∨ (a = none ∧ x ∈ b) :=
begin
  cases a,
  { simp only [true_and, false_or, not_mem_none, eq_self_iff_true, none_orelse'] },
  { simp only [some_orelse', or_false, false_and] }
end

variables (R : Type) [comm_monoid_with_zero R]

@[ext] structure P :=
(set : set R)
(C : R)
(finite : set.finite)
(zero_mem : (0 : R) ∈ set)
(C_mem : C ∈ set)

instance : preorder (P R) := preorder.lift P.set

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

@[ext] structure inc : Type :=
(emb : fin m →ₘ fin n)
(mat : fin n → option (R × fin m))
(le_emb : ∀ {j r i}, (r, i) ∈ mat j → j ≤ emb i) -- want to join this with mat_mem i think

variables {R m n}

structure inc.small (f : inc R m n) : Prop :=
(mat_mem : ∀ {j r i}, (r, i) ∈ f.mat j → r ∈ p.set)
(mat_emb : ∀ i, f.mat (f.emb i) = some (p.C, i)) -- include this in 'small' in anticipation of `C`

variables (m)
def small_vec : set (fin m → R) := { v | ∀ i, v i ∈ p.set }
variable {m}
def row (i : fin m) : set (fin m → R) := small_vec m p ∩ { v | v i = p.C ∧ ∀ j, v j ≠ 0 → j ≤ i }

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
⟨small_map hf hv.1, by rw [inc.map_vec, hf.mat_emb i, option.elim, hv.2.1, mul_C],
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
  mat_emb := λ i, by simp only [hf.mat_emb, hg.mat_emb, mul_C, some_bind, map_some',
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

variables (m p)

@[simps] def scaling : inc R m m :=
{ emb := preorder_hom.id,
  mat := λ i, some (p.C, i),
  le_emb := by rintros j _ _ ⟨rfl, rfl⟩; refl }

lemma small_scaling : (scaling m p).small p :=
{ mat_mem := by rintros j _ _ ⟨rfl, rfl⟩; exact p.C_mem,
  mat_emb := λ _, rfl }

lemma scaling_map_vec (v : fin m → R) (i : fin m) : (scaling m p).map_vec v i = v i * p.C := rfl

variables (n) (κ : Type) (R)

def coloring : Type := (fin m → R) → κ

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
{ emb := mon.to_preorder_hom,
  mat := λ i, (partial_inv mon i).map (prod.mk 1),
  le_emb := λ i r j h, by { simp only [mem_def, map_eq_some', prod.mk.inj_iff,
    exists_eq_right_right] at h, rw ←(partial_inv_of_injective mon.injective _ _).mp h.1, refl } }

lemma small_order_embedding {mon : fin m ↪o fin n} : mon.inc.small (1 : P R) :=
{ mat_emb := λ i, by simp only [partial_inv_left mon.injective, order_embedding.to_preorder_hom_coe,
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
        simp only [preorder_hom.succ_apply_last] },
      intros j r, refine fin.last_cases _ _,
      { intro, rw [preorder_hom.succ_apply_last], apply fin.le_last },
      intros i h,
      simp only [fin.snoc_cast_succ, option.mem_orelse_iff] at h,
      rcases h with h1 | ⟨_, h1⟩,
      { rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨⟨_, k⟩, ha, hb⟩,
        simp only [preorder_hom.succ_apply_cast_succ, order_embedding.le_iff_le],
        simp only [prod.mk.inj_iff, order_embedding.eq_iff_eq] at hb, rcases hb with ⟨rfl, rfl⟩,
        exact f.le_emb ha },
      { exfalso, rw [mem_def, map_eq_some'] at h1, rcases h1 with ⟨_, _, h1⟩,
        rw prod.mk.inj_iff at h1, refine ne_of_lt _ h1.2.symm, apply fin.cast_succ_lt_last }
    end }

lemma small.extend {f : inc R m n} {v : fin n → option q.set} (hf : f.small q) :
  (f.extend v).small q :=
{ mat_emb := begin
      refine fin.last_cases _ _,
      { simp only [inc.extend_mat, inc.extend_emb, fin.snoc_last, preorder_hom.succ_apply_last] },
      intro i,
      simp only [inc.extend_mat, inc.extend_emb, fin.snoc_cast_succ,
        preorder_hom.succ_apply_cast_succ],
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
  simp only [h, inc.extend_mat, fin.snoc_cast_succ, map_none', orelse_none', inc.map_vec, comp_app],
  set o := f.mat j, clear_value o, cases o,
  { simp only [map_none', option.elim], }, { simp only [option.elim, map_some'] }
end

section bla

variables {f : fin n → option (fin m)} (hf : ∀ i, ∃ j, f j = some i)
include hf

def m' : Type := fin m

def g (i : m' hf) : fin n :=
finset.max' (finset.univ.filter $ λ j, f j = some i)
((hf i).imp $ λ j hj, finset.mem_filter.mpr ⟨finset.mem_univ _, hj⟩)

variable (f)
lemma fg_eq_some (i : m' hf) : f (g hf i) = some i :=
begin
  have : g hf i ∈ finset.univ.filter (λ j, f j = some i) := finset.max'_mem _ _,
  simpa only [true_and, finset.mem_univ, finset.mem_filter] using this,
end
variable {f}

lemma inj : injective (g hf) := λ i j ij, some_injective _ (by rw [←fg_eq_some, ←fg_eq_some, ij])

instance : fintype (m' hf) := fin.fintype m
instance : linear_order (m' hf) := linear_order.lift (g hf) (inj hf)

def g_mono : m' hf →ₘ fin n := { to_fun := g hf, monotone' := λ i j, id }
def mm' : fin m ≃o (m' hf) := mono_equiv_of_fin (m' hf) (fintype.card_fin m)

@[simps] def inc_of_this : inc R m n :=
{ emb := (g_mono hf).comp (order_embedding.to_preorder_hom (mm' hf).to_rel_embedding),
  mat := λ j, (f j).elim none $ λ i : m' hf, some (1, (mm' hf).symm i),
  le_emb := λ j r i hx, finset.le_max' _ _ begin
      simp only [order_embedding.to_preorder_hom_coe, true_and, rel_iso.to_rel_embedding_eq_coe,
        rel_iso.coe_coe_fn, finset.mem_univ, finset.mem_filter],
      set o := f j, clear_value o, cases o, { cases hx },
      simp only [mem_def, option.elim, prod.mk.inj_iff] at hx,
      simp only [←hx, order_iso.apply_symm_apply],
    end }

lemma small_inc_of_this : (inc_of_this hf).small (1 : P R) :=
{ mat_emb := λ i, by simp only [g_mono, fg_eq_some f hf, order_embedding.to_preorder_hom_coe,
    rel_iso.to_rel_embedding_eq_coe, rel_iso.coe_coe_fn, option.elim, order_iso.symm_apply_apply,
    preorder_hom.coe_fun_mk, preorder_hom.comp_coe, one_C, inc_of_this_emb, inc_of_this_mat],
  mat_mem := λ j r i h, by { simp only [mem_def, inc_of_this_mat] at h,
    set o := f j, clear_value o, cases o, { cases h }, { cases h, apply P.C_mem } } }

lemma inc_of_this_map_vec {i j} {w : fin m → R} (h : f j = some i) :
  (inc_of_this hf).map_vec w j = w ((mm' hf).symm i) :=
by simp only [h, inc.map_vec, mul_one, option.elim, inc_of_this_mat]

lemma inc_of_this_map_vec' {j} {w : fin m → R} (h : f j = none) :
  (inc_of_this hf).map_vec w j = 0 :=
by simp only [h, inc.map_vec, option.elim, inc_of_this_mat]

end bla

variables {R} (m n p q) (I : ℕ) (κ)

def large_enough : Prop := ∀ co : coloring R n κ, ∃ (f : inc R m n) (k : fin m → κ), f.small q ∧
  ∀ i, (co.restrict f).mono_row p i (k i)

lemma step (h1 : large_enough m n p q κ) (h2 : extended_HJ_works (p * q).set κ (fin n) (fin I)) :
  large_enough (m+1) (I+1) p (p * q) κ := λ co,
begin
  specialize h2 (λ v, co $ fin.snoc (λ i, p.C * v i) (p.C * p.C * q.C)),
  obtain ⟨l, klast, lk⟩ := h2,
  let fo : fin I → option (fin n) := λ j, (l.idx_fun j).elim (λ _, none) some,
  have fo_surj : ∀ i, ∃ j, fo j = some i,
  { intro i, refine Exists.imp _ (l.proper i), intros j hj, simp_rw [fo, hj, sum.elim_inr] },
  let nI : inc R n I := (scaling I p).comp (inc_of_this fo_surj),
  have nI_small : nI.small p,
  { rw ←one_mul p, exact (small_scaling _ _).comp (small_inc_of_this _) },
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
    simp only [inc.comp_mat, inc_of_this_mat, fo, h, option.elim, sum.elim_inl, none_bind,
      scaling_mat, some_bind, map_none'], },
  have map_vec_inr : ∀ {v : fin (m+1) → R} {j : fin I} {i} (h : l.idx_fun j = sum.inr i),
    mI.map_vec v j.cast_succ = (nI.comp mn).map_vec (v ∘ fin.cast_succ) j,
  { intros v j i h, apply extend_map_vec_2, simp_rw [fa, h, sum.elim_inr] },
  refine ⟨mI, fin.snoc ksucc klast, mI_small, fin.last_cases _ _⟩,
  { intros v hv, simp only [coloring.restrict, fin.snoc_last],
    let w := mn.map_vec (v ∘ fin.cast_succ),
    have hw : w ∈ small_vec _ (p * q) := small_map mn_small (λ _, hv.1 _),
    specialize lk (subtype.coind w hw ∘ (mm' fo_surj).symm),
    convert lk,
    rw funext_iff,
    refine fin.last_cases _ _,
    { rw [fin.snoc_last], simpa only [inc.extend_emb, preorder_hom.succ_apply_last, mul_assoc]
        using (inc.map_row mI_small hv).2.1 },
    intro j,
    rw [fin.snoc_cast_succ, hyperline.apply, hmI],
    set o := l.idx_fun j with ho, clear_value o, rcases o with r | i,
    { rw [map_vec_inl ho.symm, sum.elim_inl, hv.2.1, id.def] },
    { simp only [map_vec_inr ho.symm, sum.elim_inr, inc.comp_map, nI, scaling_map_vec],
      rw mul_comm, congr' 1, apply inc_of_this_map_vec, rw [←ho, sum.elim_inr] } },
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
        rw [inc.extend_emb, preorder_hom.succ_apply_cast_succ], apply fin.cast_succ_lt_last },
      { intro j, set o := l.idx_fun j with ho, clear_value o, rcases o with r | i,
        { rw [map_vec_inl ho.symm,
            not.imp_symm (hv.2.2 _) (not_le_of_lt $ fin.cast_succ_lt_last _), zero_mul],
          simp only [inc.comp_map, emb_inc_map],
          rw [scaling_map_vec, inc_of_this_map_vec', zero_mul],
          rw [←ho, sum.elim_inl] },
        { rw map_vec_inr ho.symm, simp only [emb_inc_map, inc.comp_map] } } },
    rw this,
    specialize hksucc i (v ∘ fin.cast_succ) vtail_row,
    simpa only [coloring.restrict, inc.comp_map, fin.snoc_cast_succ] using hksucc }
end

theorem deuber [fintype κ] [decidable_eq κ] :
  ∃ n q, ∀ co : coloring R n κ, ∃ (f : inc R m n) (k : κ), f.small q ∧ (co.restrict f).mono p k :=
begin
  have : ∀ r, ∃ n q, large_enough r n p q κ,
  { intro r, induction r with r ih,
    { exact ⟨0, 1, λ co, ⟨(order_iso.refl _).to_order_embedding.inc, fin_zero_elim,
        small_order_embedding, fin_zero_elim⟩⟩ },
    obtain ⟨n, q, h⟩ := ih,
    haveI : fintype (p * q).set := (P.finite _).fintype,
    obtain ⟨I, hI⟩ := extended_HJ_fin (p * q).set κ (fin n),
    exact ⟨I+1, (p * q), step r n p q κ I h hI⟩ },
  specialize this (fintype.card κ * m + 1),
  obtain ⟨n, q, hn⟩ := this,
  refine ⟨n, q, _⟩,
  intro co,
  specialize hn co,
  obtain ⟨f, ks, f_small, fks⟩ := hn,
  obtain ⟨k, hk : m < _⟩ := fintype.exists_lt_card_fiber_of_mul_lt_card ks _,
  swap, { simp only [fintype.card_fin, lt_add_iff_pos_right, nat.lt_one_iff] },
  refine ⟨f.comp (order_emb_of_card_le (le_of_lt hk)).inc, k, _, _⟩,
  { convert f_small.comp small_order_embedding, rw one_mul q },
  { intro i,
    rw [coloring.restrict_comp],
    refine coloring.restrict_mono_row _ _ small_order_embedding _,
    rw mul_one, convert fks _,
    have := order_emb_mem (le_of_lt hk) i,
    simp only [true_and, finset.mem_univ, finset.mem_filter] at this,
    exact this.symm }
end
