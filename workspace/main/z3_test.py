from z3 import *

s = Solver()
x = Int('x')
y = Int('y')
z = Int('z')

s.add(x==1)
s.add(y==1)
s.add(And(z >=0, z <=1))
s.add(Implies(And(x==0,y==1),z==1))

frg1 = Int("frg1")
s.add(frg1 <= 100, frg1 >=0)
frg2 = Int("frg2")
s.add(frg2 <= 100, frg2 >=0)
frg3 = Int("frg3")
s.add(frg3 <= 100, frg3 >=0)
frg4 = Int("frg4")
s.add(frg4 <= 100, frg4 >=0)
tmplist = []

tmplist.append(x)
s.add(frg1 == Sum([tmp for tmp in tmplist]))
tmplist.append(x)
s.add(frg2 == Sum([tmp for tmp in tmplist]))
tmplist.append(x)
s.add(frg3 == Sum([tmp for tmp in tmplist]))
tmplist.append(x)
s.add(frg4 == Sum([tmp for tmp in tmplist]))

r = s.check()
if r == sat:
    m = s.model()
    print('frg1 = %d' % m[frg1].as_long())
    print('frg2 = %d' % m[frg2].as_long())
    print('frg3 = %d' % m[frg3].as_long())
    print('frg4 = %d' % m[frg4].as_long())
else:
    print (r)
# solve(x>2, y<7, x + 2*y == 7)
# print simplify(x + y + 2*x +3)
# print simplify(x < y + x + 2)
# print simplify(And(x + 1 >= 3, x**2 + y**2 + 2 >= 5))
