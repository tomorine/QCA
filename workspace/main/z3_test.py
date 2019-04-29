from z3 import *

A = IntVector('a',5)
B = RealVector('b',5)
C = IntVector('c',5)
print (A)
print (B)
print (C)
print ([b**2 for b in B])
print (Sum([b**2 for b in B]))

x = Int('x')
y = Int('y')
p,q = Bools(["p","q"])

s = Solver()
s.add(q==True, p!=q)
s.add(x*x -x == 2)

r = s.check()
if r == sat:
    m = s.model()
else:
    print (r)

solution_p = is_true(m[p])
solution_x = m[x].as_long()

print (solution_p,solution_x)
# solve(x>2, y<7, x + 2*y == 7)
# print simplify(x + y + 2*x +3)
# print simplify(x < y + x + 2)
# print simplify(And(x + 1 >= 3, x**2 + y**2 + 2 >= 5))
