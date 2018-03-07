/--
 Tag lemmas of the form:

 ```
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```
 -/
@[user_attribute]
meta def extensional_attribute : user_attribute :=
{ name := `extensionality,
  descr := "lemmas usable by `ext` tactic" }

attribute [extensionality] _root_.funext array.ext
