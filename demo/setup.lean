import tactic.back
import data.nat.prime

open nat

attribute [back] ne_of_gt le_of_lt nat.dvd_add_iff_right prime.pos prime.not_dvd_one
attribute [back!] succ_lt_succ fact_pos min_fac_prime min_fac_dvd
attribute [back] dvd_fact
