meta def error_msg (s : string) : bool := @undefined_core bool $ s ++ ".decidable not inlined"

meta def examine (b : Prop) [decidable b] : bool := b

#eval examine $ ff ∧ (error_msg "and")
#eval examine $ tt ∨ (error_msg "or")
