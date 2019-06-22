import data.buffer

import data.list.defs

-- def string.lconcat : list string → string := string.intercalate ""

def string.split_on (c : char) (s : string) := (s.to_list.split_on c).map (λ l, l.as_string)

-- def char_buffer.from_list (l : list char) : char_buffer := buffer.nil.append_list l
