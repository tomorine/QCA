# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
# インポートz3
from z3 import *  
from circ import *
import time
from collections import defaultdict
# import sys
# main
def main():
    start_time = time.time()
    # コマンドラインからファイルを引数で取得
    argv = sys.argv
    argc = len(argv)
    if argc!=2:
        print ("Usage: python3 ",argv[0]," filename")
        quit()
    str = argv[1]
    circ = Make_Network.blif(str)
    Print_Network.node_inf(circ)

    hi = 5 # circuit high
    wd = 6 # circuit wide
    s = Solver() # sは制約式の集合

    # 以下制約式の追加
    # op_exist is int variable : op_exist[op_id][wide][high]が存在するとき１になる
    # wire_exist is int variable : wire_exist[source_op][distination_op][wide][high]が存在するとき１になる
    # clock_zone is int variable : clock_zone[wide][high]のクロックゾーンを管理(1<=clock_zone<=4)
    # path is int variable : path[a][b][c][d]が位置の時クロックゾーン[a][b]から[c][d]にデータフローが存在する
    # connect is int variable : operatorの周りのクロックゾーンにファンイン数（ファンアウト数）と同じ数だけ入力（出力）を確約する。
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[[Int("wire_exist[%d][%d][%d][%d]" % (m,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)] for m in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j, i)) for i in range(hi)] for j in range(wd)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (l,k,j,i)) for i in range(hi+1)] for j in range(wd+1)] for k in range(hi+1)] for l in range(wd+1)]
    connect = [[[[Int("connect[%d][%d][%d][%d]" % (m,k,j,i)) for i in range(hi+1)] for j in range(wd+1)] for k in range(hi+1)] for m in range(wd+1)]
    # 0 <= op_exist,wire_exist <= 1
    # 1 <= clock_zone <= 4
    for i in range(circ.op_num):
        for j in range(wd):
            for k in range(hi):
                s.add(0 <= op_exist[i][j][k], op_exist[i][j][k] <= 1)
                s.add(1 <= clock_zone[j][k], clock_zone[j][k] <= 4)
                for node in range(circ.op_num):
                    s.add(0 <= wire_exist[i][node][j][k], wire_exist[i][node][j][k] <= 1)
    # 0 <= connect <= 1
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    s.add(0 <= connect[i][j][ir][jr], connect[i][j][ir][jr] <= 1)
    # すべてのopは一度必ず使わなければならない
    for i in range(circ.op_num):
        tmplist = []
        for j in range(wd):
            for k in range(hi):
                tmplist.append(op_exist[i][j][k])
        s.add(Sum([tmp for tmp in tmplist]) == 1)
    # クロックゾーンには１つのopかwireしか存在できない制約
    for k in range(hi):
        for j in range(wd):
            tmplist = []
            for i in range(circ.op_num):
                for node in circ.find_node_id(i).input:
                    id = node.id
                    tmplist.append(wire_exist[id][i][j][k])
                tmplist.append(op_exist[i][j][k])
            s.add(Sum([tmp for tmp in tmplist]) <= 1)
    # 隣接するクロックゾーンは違う数字でなければならない制約
    for i in range(wd):
        for j in range(hi):
            if i<wd-2:
                s.add(clock_zone[i][j]!=clock_zone[i+1][j])
            if j<hi - 1:
                s.add(clock_zone[i][j]!=clock_zone[i][j+1])
    # operatorの隣接するクロックゾーンにファンイン（ファンアウト）数と同じ数のconnectを定義する制約
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                inlist = [] # この配列の総和がそのままファンイン数になる
                outlist = [] # この配列の総和がそのままファンアウト数になる
                if i < wd-1:
                    inlist.append(connect[i + 1][j][i][j])
                    outlist.append(connect[i][j][i + 1][j])
                if i > 0:
                    inlist.append(connect[i-1][j][i][j])
                    outlist.append(connect[i][j][i-1][j])
                if j < hi-1:
                    inlist.append(connect[i][j + 1][i][j])
                    outlist.append(connect[i][j][i][j + 1])
                if j > 0:
                    inlist.append(connect[i][j - 1][i][j])
                    outlist.append(connect[i][j][i][j - 1])
                s.add(Implies(op_exist[node][i][j] == 1, Sum([tmp for tmp in inlist]) == len(circ.find_node_id(node).input))) # opのファンイン数を定義
                s.add(Implies(op_exist[node][i][j] == 1, Sum([tmp for tmp in outlist]) == len(circ.find_node_id(node).output))) # opのファンアウト数を定義
    # wireに対してconnectを定義する
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                inlist = []
                outlist = []
                if i < wd - 1:
                    inlist.append(connect[i+1][j][i][j])
                    outlist.append(connect[i][j][i+1][j])
                if i > 0:
                    inlist.append(connect[i-1][j][i][j])
                    outlist.append(connect[i][j][i-1][j])
                if j < hi - 1:
                    inlist.append(connect[i][j+1][i][j])
                    outlist.append(connect[i][j][i][j+1])
                if j > 0:
                    inlist.append(connect[i][j-1][i][j])
                    outlist.append(connect[i][j][i][j-1])
                for sonode in circ.find_node_id(node).input:
                    id = sonode.id
                    s.add(Implies(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in inlist]) == 1))  # wireに対してイン数を定義(in)
                    s.add(Implies(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in outlist]) == 1))  # wireに対してアウト数を定義(out)
    # connectがある所はwireかopが存在する制約
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                for sonode in circ.find_node_id(node).input:
                    right = []
                    left = []
                    down = []
                    up = []
                    id = sonode.id
                    if i < wd-1:
                        right.append(wire_exist[id][node][i+1][j])
                        right.append(op_exist[id][i+1][j])
                    if i > 0:
                        left.append(op_exist[id][i-1][j])
                        left.append(wire_exist[id][node][i-1][j])
                    if j < hi-1:
                        down.append(op_exist[id][i][j+1])
                        down.append(wire_exist[id][node][i][j+1])
                    if j > 0:
                        up.append(op_exist[id][i][j-1])
                        up.append(wire_exist[id][node][i][j-1])
                    s.add(Implies(Or(op_exist[node][i][j] == 1, wire_exist[id][node][i][j] == 1),
                                    Sum([tmp for tmp in right]) * connect[i+1][j][i][j]
                                    + Sum([tmp for tmp in left]) * connect[i-1][j][i][j]
                                    + Sum([tmp for tmp in down]) * connect[i][j+1][i][j]
                                    + Sum([tmp for tmp in up]) * connect[i][j-1][i][j] == 1))
                    for tonode in circ.find_node_id(node).output:
                        right = []
                        left = []
                        down = []
                        up = []
                        id = tonode.id
                        if i < wd-1:
                            right.append(op_exist[id][i+1][j])
                            right.append(wire_exist[node][id][i+1][j])
                        if i > 0:
                            left.append(op_exist[id][i-1][j])
                            left.append(wire_exist[node][id][i-1][j])
                        if j < hi-1:
                            down.append(op_exist[id][i][j+1])
                            down.append(wire_exist[node][id][i][j+1])
                        if j > 0:
                            up.append(op_exist[id][i][j-1])
                            up.append(wire_exist[node][id][i][j-1])
                        s.add(Implies(Or(op_exist[node][i][j] == 1, wire_exist[node][id][i][j] == 1),
                                        Sum([tmp for tmp in right])*connect[i][j][i+1][j]
                                      + Sum([tmp for tmp in left])*connect[i][j][i-1][j]
                                      + Sum([tmp for tmp in down])*connect[i][j][i][j+1]
                                      + Sum([tmp for tmp in up])*connect[i][j][i][j-1] == 1))
    # wireはループしない制約
    # 0 <= path <= 1 
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    s.add(path[i][j][ir][jr]>=0, path[i][j][ir][jr]<=1)
                    s.add(path[i][j][i][j]==0)
                    for irr in range(wd+1):
                        for jrr in range(hi+1):
                            s.add(Implies(And(path[i][j][ir][jr]==1, path[ir][jr][irr][jrr]==1),path[i][j][irr][jrr]==1))
    # connectが距離１以上にならないようにする制約
    for i in range(wd+1):
        for j in range(hi+1):
            for ir in range(wd+1):
                for jr in range(hi+1):
                    if abs((j-jr)+(i-ir)) >= 2:
                        s.add(connect[i][j][ir][jr] == 0)
    # connectが存在する所にpathを通す制約
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    s.add(Implies(connect[i][j][ir][jr]==1, path[i][j][ir][jr]==1))
    # 空白のクロックゾーンからconnectが出ないようにする制約
    for i in range(wd+1):
        for j in range(hi+1):
            tmplist = []
            tmplist.append(0)
            if i < wd and j < hi:
                for node in range(circ.op_num):
                    tmplist.append(op_exist[node][i][j])
                    for sonode in circ.find_node_id(node).input:
                        id = sonode.id
                        tmplist.append(wire_exist[id][node][i][j])
            if i < wd:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i+1][j] == 0, connect[i+1][j][i][j] == 0)))
            if i > 0:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i-1][j] == 0, connect[i-1][j][i][j] == 0)))
            if j < hi:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i][j+1] == 0, connect[i][j+1][i][j] == 0)))
            if j > 0:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(connect[i][j][i][j-1] == 0, connect[i][j][i][j-1] == 0)))
            """
            s.add(Implies(And(connect[i][j][i+1][j] == 0, connect[i+1][j][i][j] == 0,
                          connect[i][j][i-1][j] == 0, connect[i-1][j][i][j] == 0,
                          connect[i][j][i][j+1] == 0, connect[i][j+1][i][j] == 0,
                          connect[i][j][i][j-1] == 0, connect[i][j-1][i][j] == 0),Sum([tmp for tmp in tmplist])==0))
    """
    # 同じクロックゾーンを跨るconnectが2つ以上存在しない制約
    for i in range(wd):
        for j in range(hi):
            clist = []
            if i < wd:
                clist.append(connect[i+1][j][i][j])
                clist.append(connect[i][j][i+1][j])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                clist.clear()
            if i > 0:
                clist.append(connect[i - 1][j][i][j])
                clist.append(connect[i][j][i - 1][j])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                clist.clear()
            if j < hi:
                clist.append(connect[i][j+1][i][j])
                clist.append(connect[i][j][i][j+1])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                clist.clear()
            if j > 0:
                clist.append(connect[i][j-1][i][j])
                clist.append(connect[i][j][i][j-1])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                clist.clear()
    # クロックゾーンが提供するデータパスに従ってのみconnectを定義できる制約
    for i in range(wd):
        for j in range(hi):
            if i < wd - 1:
                s.add(If(connect[i][j][i+1][j] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i+1][j] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i+1][j] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i+1][j] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i+1][j] == 1)),
                                                     connect[i][j][i+1][j] == 0))
            if i > 0:
                s.add(If(connect[i][j][i-1][j] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i-1][j] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i-1][j] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i-1][j] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i-1][j] == 1)),
                                                     connect[i][j][i-1][j] == 0))
            if j < hi - 1:
                s.add(If(connect[i][j][i][j+1] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i][j+1] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i][j+1] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i][j+1] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i][j+1] == 1)),
                                                     connect[i][j][i][j+1] == 0))
            if j > 0:
                s.add(If(connect[i][j][i][j-1] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i][j-1] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i][j-1] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i][j-1] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i][j-1] == 1)),
                                                     connect[i][j][i][j-1] == 0))

    # スループットを向上させる制約のための再起関数。本当はmain外に書きたいが疲れたのでまた今度
    def search_length(sonode, tonode, tmplist):
        tmplist.append(1)
        for i in range(wd):
            for j in range(hi):
                tmplist.append(wire_exist[sonode.id][tonode.id][i][j])
        if sonode.gatetype == "p_input":
            return (tmplist)
        else:
            for node in sonode.input:
                tmplist = search_length(node, sonode, tmplist)
    # スループットを向上させる制約
    for node in range(circ.op_num):
        tmplistlist = []
        if len(circ.find_node_id(node).input) >= 2:
            for sonode in circ.find_node_id(node).input:
                tmplist = []
                search_length(sonode, circ.find_node_id(node), tmplist)
                tmplistlist.append(tmplist)
            if len(tmplistlist) == 2:
                s.add(Sum([tmp for tmp in tmplistlist[0]]) == Sum([tmp for tmp in tmplistlist[1]]))
            if len(tmplistlist) == 3:
                s.add(Sum([tmp for tmp in tmplistlist[0]]) == Sum([tmp for tmp in tmplistlist[1]]))
                s.add(Sum([tmp for tmp in tmplistlist[0]]) == Sum([tmp for tmp in tmplistlist[2]]))
                s.add(Sum([tmp for tmp in tmplistlist[1]]) == Sum([tmp for tmp in tmplistlist[2]]))
    # todo : clock_wireを通すようにクロックゾーンを配置する制約
    # print model or
    r = s.check()
    if r == sat:
        m = s.model()
        # print operator
        print("oprater")
        for k in range(hi):
            frg = '*'
            for j in range(wd):
                for i in range(circ.op_num):
                    if m[op_exist[i][j][k]].as_long() != 0:
                        frg = i
                print(" [%s] " % frg, end='')
                frg = '*'
            print()
        # print wire
        print("\nwire")
        for k in range(hi):
            frg = '*'
            frg2 = '*'
            for j in range(wd):
                for i in range(circ.op_num):
                    for node in circ.find_node_id(i).input:
                        id = node.id
                        if m[wire_exist[id][i][j][k]].as_long() !=0:
                            frg = id
                            frg2 = i
                print(' [%s:%s] '% (frg, frg2), end='')
                frg = '*'
                frg2 = '*'
            print()
        # for node in range(circ.op_num)
        # print path
        """
        print("\npath")
        for j in range(hi+1):
            for i in range(wd):
                print("[ ]",end='')
                if m[path[i][j][i+1][j]].as_long()==1:
                    print(">",end='')
                elif m[path[i+1][j][i][j]].as_long()==1:
                    print("<",end='')
                else:
                    print(" ",end='')
            print("[ ]")
            for i in range(wd+1):
                if j<hi-1 and m[path[i][j][i][j+1]].as_long()==1:
                    print(" v  ",end='')
                elif j<hi-1 and m[path[i][j+1][i][j]].as_long()==1:
                    print(" A  ",end='')
                else:
                    print("    ",end='')
            print()
        """
        print("\nconnect")
        for j in range(hi+1):
            for i in range(wd):
                print("[ ]",end='')
                if m[connect[i][j][i+1][j]].as_long()==1:
                    print(">",end='')
                elif m[connect[i+1][j][i][j]].as_long()==1:
                    print("<",end='')
                else :
                    print(" ",end='')
            print("[ ]")
            for i in range(wd+1):
                if j<hi and m[connect[i][j][i][j+1]].as_long() == 1:
                    print(" V ",end='')
                elif j<hi and m[connect[i][j+1][i][j]].as_long() == 1:
                    print(" A ",end='')
                else:
                    print("   ",end='')
                print(" ",end='')
            print()
        """
        print("\nclock_zone")
        for j in range(hi):
            for i in range(wd):
                print (" [%d] " % m[clock_zone[i][j]].as_long(), end='')
            print()
        print()
        """
        print("\nconnnect list")
        for i in range(wd+1):
            for j in range(hi+1):
                for ir in range(wd+1):
                    for jr in range(hi+1):
                        if m[connect[i][j][ir][jr]].as_long() == 1:
                            print("connect[%d][%d][%d][%d]"%(i, j, ir, jr))

    else:
        print(r)
    elapsed_time = time.time() - start_time
    print("elapsed_time:{0}".format(elapsed_time) + "[sec]")

if __name__ == '__main__':
    main()
