from z3 import *

def search_length(tmplist):
    tmplist.append(1)
    if len(tmplist) >= 5:
        return(tmplist)
    else:
        tmplist = search_length(tmplist)

s = Solver()
x = Int('x')
y = Int('y')
z = Int('z')

tmplist = []
search_length(tmplist)
for i in tmplist:
    print(i)

"""
if r == sat:
    m = s.model()
    print(r)
else:
    print (r)
    """
# solve(x>2, y<7, x + 2*y == 7)
# print simplify(x + y + 2*x +3)
# print simplify(x < y + x + 2)
# print simplify(And(x + 1 >= 3, x**2 + y**2 + 2 >= 5))
