# this file will be run by the remote sage server, so should not import local files.
from functools import reduce
from typing import Optional
import dataclasses

from attr import dataclass
from sage.rings.polynomial.polydict import ETuple

def mk_app(*args: str) -> str:
    return "(" + " ".join(args) + ")"

def const_to_string(coeff: QQ) -> str:
    return mk_app("poly.const", str(coeff.numerator()) + "/" + str(coeff.denominator()))

def power_to_string(var: int, pow: int) -> str:
    assert pow != 0
    var_s = mk_app("poly.var", str(var))
    if pow == 1:
        return var_s
    return mk_app("poly.pow", var_s, str(pow))

def combine_terms(s: str, t: str) -> str:
    print(s, t)
    if t[0] == '-':
        return mk_app("poly.sub", s, t[1:])
    else:
        return mk_app("poly.add", s, t)

@dataclass
class MonomForm:
    pos_form: str
    neg_form: Optional[str] = None

def sum_to_string_aux(old: str, rest: list[MonomForm]) -> str:
    try:
        nxt = next(rest)
    except StopIteration:
        return old
    s = mk_app("poly.sub" if nxt is not None else "poly.add", old, nxt.pos_form)
    return sum_to_string_aux(s, rest)

def sum_to_string(terms: list[MonomForm]) -> str:
    try:
        first = next(terms)
    except StopIteration:
        return const_to_string(QQ(0))
    else:
        first_form = first.neg_form if first.neg_form is not None else first.pos_form
        return sum_to_string_aux(first_form, terms)


def monomial_to_string(etuple: ETuple, coeff: QQ) -> MonomForm:
    pos_form = reduce(
        lambda s, t: mk_app("poly.mul", s, power_to_string(t[0], t[1])),
        etuple.sparse_iter(),
        const_to_string(abs(coeff)))
    neg_form = reduce(
        lambda s, t: mk_app("poly.mul", s, power_to_string(t[0], t[1])),
        etuple.sparse_iter(),
        const_to_string(coeff))if coeff < 0 else None
    return MonomForm(pos_form, neg_form)


def polynomial_to_string(p) -> str:
    return sum_to_string(monomial_to_string(pows, coeff) for pows, coeff in p.dict().items())
