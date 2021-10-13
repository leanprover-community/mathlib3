import tactic.lint
import data.list.basic
open tactic

lemma test_a : true :=
have 1 = 1 := rfl,
trivial

run_cmd do
  d ← get_decl ``test_a,
  some t ← linter.unused_haves_suffices.test d,
  guard $ "unnecessary have".is_prefix_of t

lemma test_b : true :=
have h : 1 = 1 := rfl,
trivial

run_cmd do
  d ← get_decl ``test_b,
  some t ← linter.unused_haves_suffices.test d,
  guard $ "unnecessary have h".is_prefix_of t

lemma test_c : true :=
suffices h : 1 = 1, from trivial,
rfl

run_cmd do
  d ← get_decl ``test_c,
  some t ← linter.unused_haves_suffices.test d,
  guard $ "unnecessary suffices h".is_prefix_of t

-- test a non-trivial example obtained by printing the term for `list.map_reverse` and adding
-- some unnecessary terms
universes u v
theorem test_map_reverse : ∀ {α : Type u} {β : Type v} (f : α → β) (l : list α),
  list.map f l.reverse = (list.map f l).reverse :=
λ {α : Type u} {β : Type v} (f : α → β) (l : list α),
  list.rec (eq.refl (list.map f list.nil.reverse))
    (λ (l_hd : α) (l_tl : list α) (l_ih : list.map f l_tl.reverse = (list.map f l_tl).reverse),
       (id
          ((λ (a a_1 : list β) (e_1 : a = a_1) (a a_1 : list β) (e_2 : a = a_1),
              congr (congr_arg eq e_1) e_2)
             (list.map f (l_hd :: l_tl).reverse)
             ((list.map f l_tl).reverse ++ [f l_hd])
             ((((λ (f f_1 : α → β) (e_1 : f = f_1) (a a_1 : list α) (e_2 : a = a_1),
                   congr (congr_arg list.map e_1) e_2)
                  f
                  f
                  (eq.refl f)
                  (l_hd :: l_tl).reverse
                  (l_tl.reverse ++ [l_hd])
                  (list.reverse_cons l_hd l_tl)).trans
                 (list.map_append f l_tl.reverse [l_hd])).trans
                ((λ [self : has_append (list β)] (a a_1 : list β) (e_2 : a = a_1) (a_2 a_3 : list β)
                  (e_3 : a_2 = a_3), congr (congr_arg append e_2) e_3)
                   (list.map f l_tl.reverse)
                   (list.map f l_tl).reverse
                   l_ih
                   (list.map f [l_hd])
                   [f l_hd]
                   ((list.map.equations._eqn_2 f l_hd list.nil).trans
                      ((λ (hd hd_1 : β) (e_1 : hd = hd_1) (tl tl_1 : list β) (e_2 : tl = tl_1),
                          congr (congr_arg list.cons e_1) e_2)
                         (f l_hd)
                         (have 1 = 1 := rfl, f l_hd)
                         (eq.refl (f l_hd))
                         (list.map f list.nil)
                         list.nil
                         (list.map.equations._eqn_1 f)))))
             (list.map f (l_hd :: l_tl)).reverse
             ((list.map f l_tl).reverse ++ [f l_hd])
             (((λ (a a_1 : list β) (e_1 : a = a_1), congr_arg list.reverse e_1)
              (list.map f (l_hd :: l_tl))
                 (f l_hd :: list.map f l_tl)
                 (list.map.equations._eqn_2 f l_hd l_tl)).trans
                (list.reverse_cons (f l_hd) (list.map f l_tl))))).mpr
         (eq.refl (suffices hh : true, from (list.map f l_tl).reverse ++ [f l_hd], trivial)))
    l

run_cmd do
  d ← get_decl ``test_map_reverse,
  some t ← linter.unused_haves_suffices.test d,
  guard $ "unnecessary have".is_prefix_of t,
  guard $ " unnecessary suffices hh".is_prefix_of (t.split_on ',').tail.head

theorem test_d : ∃ (n : ℕ), n^2 + 1 = 37 :=
have np : 2 ≤ 3, from le_of_not_ge $ λ h,
  have f1 : 1 = 1 := rfl,
  have f2 : 2 * 1 = 2 * 1 := congr_arg (has_mul.mul 2) f1,
  suffices 1 = 1,
  from (dec_trivial : ¬ 2 ≥ 3) h,
  rfl,
⟨6, dec_trivial⟩

run_cmd do
  d ← get_decl ``test_d,
  some t ← linter.unused_haves_suffices.test d,
  guard $ (t.split_on ',').length = 3
