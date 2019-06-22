namespace interactive

open lean interactive.types

meta def opt_single_or_list {α : Type} (ps : parser α) : parser (list α) :=
  list_of ps <|> ((λ h, list.cons h []) <$> ps) <|> return []

end interactive
