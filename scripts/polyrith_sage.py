import requests
import json
import sys

polynomial_formatting_functions = '''
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
'''

# future extensions may change behavior depending on the base type
def type_str(type):
    return "QQ"

def var_names(var_list_string):
    return var_list_string[1:-1].replace(" ", "")

def create_query(type: str, var_list, eq_list, goal_type):
    query = f'''
{var_names(var_list)} = {type_str(type)}['{var_names(var_list)}'].gens()
gens = {eq_list}
p = {goal_type}
I = ideal(gens)
coeffs = p.lift(I)
print(list(map(polynomial_to_string, coeffs)))
'''
    return query

class EvaluationError(Exception):
    def __init__(self, ename, evalue, message='Error in Sage communication'):
        self.ename = ename
        self.evalue = evalue
        self.message = message
        super().__init__(self.message)

def evaluate_in_sage(query: str, format=False) -> str:
    if format:
        clean_query = query
        query = (f'print({clean_query})')
    data = {'code': query}
    headers = {'content-type': 'application/x-www-form-urlencoded'}
    response = requests.post('https://sagecell.sagemath.org/service', data, headers=headers)
    response = json.loads(response.text)
    if response['success']:
        return response['stdout'] if 'stdout' in response else None
    elif 'execute_reply' in response and 'ename' in response['execute_reply'] and 'evalue' in response['execute_reply']:
        raise EvaluationError(response['execute_reply']['ename'], response['execute_reply']['evalue'])
    else:
        raise Exception(response)

def main():
    command = create_query(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5])
    final_query = polynomial_formatting_functions + "\n" + command
    if sys.argv[1] == 'tt': # trace enabled
        print(command)
    else:
        try:
            output = evaluate_in_sage(final_query).replace("'", "")
            output = output.replace(",", "")
            output = output.replace("[", "").replace("]", "").strip()
            output += " "
            print(output)
        except EvaluationError as e:
            print(f'%{e.ename}%{e.evalue}')


if __name__ == "__main__":
    main()
