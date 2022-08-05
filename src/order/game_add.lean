import logic.relation
import order.basic

variables {α β : Type*} (rα : α → α → Prop) (rβ : β → β → Prop)

/-- The "addition of games" relation in combinatorial game theory, on the product type: if
  `rα a' a` means that `a ⟶ a'` is a valid move in game `α`, and `rβ b' b` means that `b ⟶ b'`
  is a valid move in game `β`, then `game_add rα rβ` specifies the valid moves in the juxtaposition
  of `α` and `β`: the player is free to choose one of the games and make a move in it,
  while leaving the other game unchanged. -/
inductive game_add : α × β → α × β → Prop
| fst {a' a b} : rα a' a → game_add (a',b) (a,b)
| snd {a b' b} : rβ b' b → game_add (a,b') (a,b)

/-- `game_add` is a `subrelation` of `prod.lex`. -/
lemma game_add_le_lex : game_add rα rβ ≤ prod.lex rα rβ :=
λ _ _ h, h.rec (λ _ _ b, prod.lex.left b b) (λ a _ _, prod.lex.right a)

/-- `prod.rprod` is a subrelation of the transitive closure of `game_add`. -/
lemma rprod_le_trans_gen_game_add : prod.rprod rα rβ ≤ relation.trans_gen (game_add rα rβ) :=
λ _ _ h, h.rec begin
  intros _ _ _ _ hα hβ,
  exact trans_gen.tail (trans_gen.single $ game_add.fst hα) (game_add.snd hβ),
end

variables {rα rβ}

/-- If `a` is accessible under `rα` and `b` is accessible under `rβ`, then `(a, b)` is
  accessible under `relation.game_add rα rβ`. Notice that `prod.lex_accessible` requires the
  stronger condition `∀ b, acc rβ b`. -/
lemma _root_.acc.game_add {a b} (ha : acc rα a) (hb : acc rβ b) : acc (game_add rα rβ) (a, b) :=
begin
  induction ha with a ha iha generalizing b,
  induction hb with b hb ihb,
  refine acc.intro _ (λ h, _),
  rintro (⟨_,_,_,ra⟩|⟨_,_,_,rb⟩),
  exacts [iha _ ra (acc.intro b hb), ihb _ rb],
end

/-- The sum of two well-founded games is well-founded. -/
lemma _root_.well_founded.game_add (hα : well_founded rα) (hβ : well_founded rβ) :
  well_founded (game_add rα rβ) := ⟨λ ⟨a,b⟩, (hα.apply a).game_add (hβ.apply b)⟩
