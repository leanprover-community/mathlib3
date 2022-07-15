# this file will be run by the remote sage server, so should not import local files.
from functools import reduce
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

def sum_to_string(terms: list[str]) -> str:
    terms = iter(terms)
    try:
        first = next(terms)
    except StopIteration:
        return const_to_string(QQ(0))
    else:
        return reduce(lambda s, t: mk_app("poly.add", s, t), terms, first)

def monomial_to_string(etuple: ETuple, coeff: QQ) -> str:
    return reduce(
        lambda s, t: mk_app("poly.mul", s, power_to_string(t[0], t[1])),
        etuple.sparse_iter(),
        const_to_string(coeff))

def polynomial_to_string(p) -> str:
    return sum_to_string(monomial_to_string(pows, coeff) for pows, coeff in p.dict().items())
