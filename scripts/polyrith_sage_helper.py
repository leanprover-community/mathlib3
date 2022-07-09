# this file will be run by the remote sage server, so should not import local files.
def const_string(const):
    num = str(const)
    if "/" not in num:
        num += "/1"
    return "(poly.const " + num + ")"

def var_string(var):
    if "var" in var:
        var = var.replace("var", "")
        var = "(poly.var " + var + ")"
    return var

def mul_vars_string(var_list):
    if var_list == []:
        return const_string(1)
    elif len(var_list) == 1:
        return var_list[0]
    return f'(poly.mul {mul_vars_string(var_list[:-1])} {var_list[-1]})'

# assumes a monomial is always (var^nat)*(var^nat)... true?
def format_monom_component(e):
    if "^" not in e:
        return var_string(e)
    base, exp = e.split("^")
    return f'(poly.pow {var_string(base)} {int(exp)})'

def monomial_to_string(m):
    m = str(m)
    m_list = m.replace(" ", "").split("*")
    var_things = [format_monom_component(e) for e in m_list]
    return mul_vars_string(var_things)

def poly_terms_string(terms):
    if terms == []:
        return const_string(1)
    elif len(terms) == 1:
        if "-" in terms[0]:
            return f'(poly.sub {const_string(0)} {terms[0].replace("-", "")})'
        return terms[0]
    elif "-" in terms[-1]:
        return f'(poly.sub {poly_terms_string(terms[:-1])} {terms[-1].replace("-", "")})'
    return f'(poly.sum {poly_terms_string(terms[:-1])} {terms[-1]})'

def polynomial_to_string(p):
    monomials = p.monomials()
    coeffs = p.coefficients()
    if len(monomials) == 0:
        return const_string(0)
    out = []
    for i in range(len(coeffs)):
        if str(monomials[i]) == "1":
            n = QQ(float(coeffs[i]))
            out.append(const_string(n))
        elif str(coeffs[i]) == "1":
            out.append(monomial_to_string(monomials[i]))
        elif str(coeffs[i]) == "-1":
            out.append("-" + monomial_to_string(monomials[i]))
        else:
            out.append("(poly.mul " + const_string(coeffs[i]) + " " + monomial_to_string(monomials[i]) + ")")
    return poly_terms_string(out)
