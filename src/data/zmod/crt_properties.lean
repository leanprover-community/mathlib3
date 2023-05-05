/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.zmod.basic
import number_theory.padics.ring_homs

/-!
# Properties of ℤ/nℤ for the Chinese Remainder Theorem

This file has some theorems regarding coercions with respect to the Chinese Remainder Theorem for
`zmod n` for all `n`.

## Main definitions and theorems
 * `proj_fst`, `proj_snd`, `inv_fst`, `inv_snd` : lemmas regarding CRT

## Tags
zmod, CRT
-/

lemma proj_fst' {m n : ℕ} (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show m ∣ m * n, from dvd.intro n rfl) (zmod m)
    ((zmod.chinese_remainder h).symm (a,b)) = a :=
begin
  change _ = prod.fst (a, b),
  have h2 : zmod.cast_hom (show m.lcm n ∣ m * n, by simp [nat.lcm_dvd_iff]) (zmod m × zmod n) _ = _,
    exact (zmod.chinese_remainder h).right_inv (a,b),
  conv_rhs { rw ←h2, },
  convert_to _ = (ring_hom.comp (ring_hom.fst (zmod m) (zmod n))
    (zmod.cast_hom _ (zmod m × zmod n))) ((zmod.chinese_remainder h).inv_fun (a, b)) using 1,
  apply congr _ rfl, congr,
  refine ring_hom.ext_zmod _ _,
end

lemma proj_snd' {m n : ℕ} (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show n ∣ m * n, from dvd.intro_left m rfl) (zmod n)
    ((zmod.chinese_remainder h).symm (a,b)) = b :=
begin
  change _ = prod.snd (a, b),
  have h2 : zmod.cast_hom (show m.lcm n ∣ m * n, by simp [nat.lcm_dvd_iff]) (zmod m × zmod n) _ = _,
    exact (zmod.chinese_remainder h).right_inv (a,b),
  conv_rhs { rw ←h2, },
  convert_to _ = (ring_hom.comp (ring_hom.snd (zmod m) (zmod n))
    (zmod.cast_hom _ (zmod m × zmod n))) ((zmod.chinese_remainder h).inv_fun (a, b)) using 1,
  apply congr _ rfl, congr,
  refine ring_hom.ext_zmod _ _,
end

open zmod
lemma inv_fst' {m n : ℕ} (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod m) :=
by { simp only [zmod.chinese_remainder, ring_equiv.to_equiv_eq_coe, ring_equiv.coe_to_equiv,
  ring_equiv.coe_mk, cast_hom_apply, prod.fst_zmod_cast]}
-- takes a long time to compile if not squeezed

lemma inv_snd' {m n : ℕ} (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod n) :=
by { simp only [zmod.chinese_remainder, ring_equiv.to_equiv_eq_coe, ring_equiv.coe_to_equiv,
  ring_equiv.coe_mk, zmod.cast_hom_apply, prod.snd_zmod_cast], }

variables {p : ℕ} {d : ℕ}
open padic_int

lemma proj_fst [fact p.prime] {n : ℕ} (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).symm (x.fst, (to_zmod_pow n) x.snd)) = x.fst := proj_fst' _ _ _

lemma proj_snd [fact p.prime] {n : ℕ} (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).symm (x.fst, (to_zmod_pow n) x.snd)) =
  (to_zmod_pow n) x.snd :=
proj_snd' _ _ _

lemma inv_fst {n : ℕ} (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod d) := inv_fst' x _

lemma inv_snd {n : ℕ} (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod (p^n)) := inv_snd' _ _

variable (p)
lemma proj_fst'' {n : ℕ} (hd : d.coprime p) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : zmod d) = a.fst :=
by { rw ring_equiv.inv_fun_eq_symm, apply proj_fst', }

lemma proj_snd'' [fact p.prime] {n : ℕ} (hd : d.coprime p) (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
(padic_int.to_zmod_pow n) ((zmod.chinese_remainder (nat.coprime.pow_right n hd)).inv_fun (↑(a.fst), ↑(a.snd)) : ℤ_[p]) = a.snd :=
begin
  rw [← zmod.int_cast_cast, map_int_cast, zmod.int_cast_cast, ring_equiv.inv_fun_eq_symm],
  convert proj_snd' _ _ _,
end
