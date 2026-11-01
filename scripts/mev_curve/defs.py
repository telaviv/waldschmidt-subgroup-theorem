"""Parse the law and fibre-correction definitions from the Lean sources into sympy."""
import re, os
import sympy as sp

g2, g3, U1, V1, W1, U2, V2, W2 = sp.symbols('g2 g3 U1 V1 W1 U2 V2 W2')
LOC = {'g2': g2, 'g3': g3, 'U1': U1, 'V1': V1, 'W1': W1, 'U2': U2, 'V2': V2, 'W2': W2}
TR = str.maketrans({'₁': '1', '₂': '2', '₃': '3'})

def parse(path, want):
    src = open(path, encoding='utf-8').read()
    out = {}
    pat = r'def (\S+) \((\S+) (\S+) U₁ V₁ W₁ U₂ V₂ W₂ : R\) : R :=\n((?:    .*\n)+)'
    for m in re.finditer(pat, src):
        name, body = m.group(1), m.group(4)
        if not want(name):
            continue
        body = body.translate(TR).replace('^', '**').replace('\n', ' ')
        out[name] = sp.sympify(body, locals=LOC)
    return out

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..')
D1 = parse(os.path.join(ROOT, 'LSG/Elliptic/AdditionLaws.lean'),
           lambda n: n[:3] == 'law' and len(n) == 5)
D2 = parse(os.path.join(ROOT, 'LSG/Elliptic/NaturalLawsPoly.lean'), lambda n: n.startswith('kap'))
LAW = {0: [D1['law₁U'], D1['law₁V'], D1['law₁W']],
       1: [D1['law₂U'], D1['law₂V'], D1['law₂W']]}
NM = {0: '₁', 1: '₂'}
LM = {0: 'V', 1: 'W'}

def kapW(i, j, k):
    return D2[f'kapW{NM[i]}{LM[j]}{LM[k]}']

def kapV(i, j, k):
    return D2[f'kapV{NM[i]}{LM[j]}{LM[k]}']

def F(U, V, W):
    return V**2*W - 4*U**3 + g2*U*W**2 + g3*W**3

if __name__ == '__main__':
    print(len(D1), len(D2))
