# this file will be run by the remote sage server, so should not import local files.
from functools import reduce
from typing import Optional, Iterator
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

@dataclass
class MonomForm:
    pos_form: str
    neg_form: Optional[str] = None

def sum_to_string_aux(old: str, nxt: MonomForm) -> str:
    return mk_app("poly.sub" if nxt.neg_form is not None else "poly.add", old, nxt.pos_form)

def sum_to_string(terms: Iterator[MonomForm]) -> str:
    try:
        first = next(terms)
    except StopIteration:
        return const_to_string(QQ(0))
    else:
        first_form = first.neg_form if first.neg_form is not None else first.pos_form
        return reduce(sum_to_string_aux, terms, first_form)

def monomial_to_string(etuple: ETuple, coeff: QQ) -> MonomForm:
    etuple = list(etuple.sparse_iter())
    if abs(coeff) == 1 and len(etuple) > 0:
        powforms = [power_to_string(t[0], t[1]) for t in etuple]
        pos_form = reduce(
            lambda s, t: mk_app("poly.mul", s, t), powforms)
        return MonomForm(pos_form, mk_app("poly.neg", pos_form) if coeff < 0 else None)
    else:
        pos_form = reduce(
            lambda s, t: mk_app("poly.mul", s, power_to_string(t[0], t[1])),
            etuple,
            const_to_string(abs(coeff)))
        neg_form = reduce(
            lambda s, t: mk_app("poly.mul", s, power_to_string(t[0], t[1])),
            etuple,
            const_to_string(coeff)) if coeff < 0 else None
    return MonomForm(pos_form, neg_form)


def polynomial_to_string(p) -> str:
    return sum_to_string(monomial_to_string(pows, coeff) for pows, coeff in p.dict().items())
