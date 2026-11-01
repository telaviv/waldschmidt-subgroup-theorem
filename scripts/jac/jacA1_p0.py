import sys, sympy as sp
sys.path.insert(0,'.')
import slots
a=sp.symbols('a')
def red(e): return sp.rem(sp.expand(e), a**5-2, a)
m=[a, 0, 2*a**4, -1]
X=[1, m[2]**2/4-m[0]**3+m[0]*m[1], -m[1], m[0], -2*m[3]*m[0]**2+m[3]*m[1]-m[2]**3/4+m[2]*m[0]**3-3*m[2]*m[0]*m[1],
   -m[3]*m[0]-m[2]*m[1], m[3], m[2], m[3]*m[2]/sp.Integer(2)+2*m[0]**2*m[1]]
X=[red(sp.nsimplify(v)) for v in X]
Y=[X[0],X[1],X[2],X[3],-X[4],-X[5],-X[6],-X[7],X[8]]
laws=slots.load_laws()
def mono(v,c): 
    r=1
    for i in range(9): r*=v[i]**(c//8**i%8)
    return r
for l in range(9):
  s=0
  for ac,row in laws[(l,0)]:
    for bc,c,neg in row:
      s+= (-c if neg else c)*mono(X,ac)*mono(Y,bc)
  print(l, red(s))
print(X)
# quotient for law0 component 4
s=0
for ac,row in laws[(4,0)]:
  for bc,c,neg in row:
    s+= (-c if neg else c)*mono(X,ac)*mono(Y,bc)
q,r=sp.div(sp.expand(s-128*a), a**5-2, a); print('q4 =', q, 'r=',r)
# grantJ components raw
m0,m2,m3=a,4/a,-1; m1=0
raw=[1, m2**2/4-m0**3+m0*m1, -m1, m0, -2*m3*m0**2+m3*m1-m2**3/4+m2*m0**3-3*m2*m0*m1, -m3*m0-m2*m1, m3, m2, m3*m2/2+2*m0**2*m1]
for i,(rw,t) in enumerate(zip(raw,X)):
  num=sp.together(rw - t); n,d=sp.fraction(num); qq,rr=sp.div(sp.expand(n), a**5-2, a); print(i, 'num/den', d, 'q', qq, rr)
