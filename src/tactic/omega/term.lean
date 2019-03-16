import tactic.omega.coeffs 

def term : Type := int × coeffs 

namespace term

@[omega] def val (v : nat → int) : term → int 
| (b,as) := b + coeffs.val v as

@[omega] def neg : term → term 
| (b,as) := (-b, as.neg) 

@[omega] def add : term → term → term 
| (c1,cfs1) (c2,cfs2) := (c1+c2, list.add cfs1 cfs2) 

@[omega] def sub : term → term → term 
| (c1,cfs1) (c2,cfs2) := (c1 - c2, list.sub cfs1 cfs2) 

@[omega] def div (i : int) : term → term 
| (b,as) := (b/i, as.map (λ x, x / i)) 

lemma val_neg {v} {t : term} :
(neg t).val v = -(t.val v) := 
begin cases t with b as, simp_omega [neg_add] end

@[omega] lemma val_sub {v} {t1 t2 : term} :
(sub t1 t2).val v = t1.val v - t2.val v :=
begin 
  cases t1, cases t2, 
  simp_omega, ring, 
end

@[omega] lemma val_add {v} {t1 t2 : term} :
(add t1 t2).val v = t1.val v + t2.val v :=
begin 
  cases t1, cases t2,
  simp_omega, ring, 
end

def mul (i : int) : term → term 
| (b,as) := (i * b, as.map ((*) i))

@[omega] lemma val_mul {v i t} :
val v (mul i t) = i * (val v t) := 
begin 
  cases t, 
  simp_omega [mul, mul_add, add_mul,
  coeffs.val, list.length_map],
end

lemma val_div {v i} {b as} :
i ∣ b → (∀ x ∈ as, i ∣ x) → 
(div i (b,as)).val v = (val v (b,as)) / i := 
begin
  intros h1 h2, simp_omega, 
  rw [int.add_div h1 (coeffs.dvd_val h2)],
  apply fun_mono_2 rfl,
  rw ← coeffs.val_map_div h2
end

def fresh_index (t : term) : nat := t.snd.length

end term

def terms.fresh_index : list term → nat 
| []      := 0
| (t::ts) := max t.fresh_index (terms.fresh_index ts)