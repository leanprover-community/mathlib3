
namespace string

def map_tokens (c : char) (f : list string → list string) : string → string :=
intercalate (singleton c) ∘ f ∘ split (= c)

def over_list (f : list char → list char) : string → string :=
list.as_string ∘ f ∘ string.to_list

end string
