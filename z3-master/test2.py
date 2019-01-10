# モジュールをimport
from z3 import *

# 変数を作成．引数は人間が見てわかりやすい変数名．
p, q = Bools(["p", "q"])
x = Int("x")

# ソルバのインスタンスを生成して
s = Solver()

# 制約を追加
s.add(q == True, p != q)
s.add(x * x - x == 2)

# 解を探索，モデルを取得
r = s.check()
if r == sat:
    m = s.model()
else:
    print(r)
    # exit(1)
    
    # 解を取得
solution_p = is_true(m[p])
solution_x = m[x].as_long()

print(solution_p, solution_x)
