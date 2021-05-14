import tactic.pretty_cases
import data.list.perm

example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  induction h,
  do { x ← tactic.pretty_cases_advice,
       guard (x =
"Try this:
  case list.perm.nil
  { admit },
  case list.perm.cons : h_x h_l₁ h_l₂ h_ᾰ h_ih
  { admit },
  case list.perm.swap : h_x h_y h_l
  { admit },
  case list.perm.trans : h_l₁ h_l₂ h_l₃ h_ᾰ h_ᾰ_1 h_ih_ᾰ h_ih_ᾰ_1
  { admit }"
) <|> fail!"expecting: {repr x}" },
  all_goals { trivial }
end

example {α} (xs ys : list α) (h : xs ~ ys) : true :=
begin
  cases h,
  do { x ← tactic.pretty_cases_advice,
       guard (x =
"Try this:
  case list.perm.nil
  { admit },
  case list.perm.cons : h_x h_l₁ h_l₂ h_ᾰ
  { admit },
  case list.perm.swap : h_x h_y h_l
  { admit },
  case list.perm.trans : xs h_l₂ ys h_ᾰ h_ᾰ_1
  { admit }") },
  all_goals { trivial }
end
