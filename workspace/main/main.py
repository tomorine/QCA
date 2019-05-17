# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
# Implies関数はバグの元. 極力If関数を使うべし
# インポートz3
from z3 import *  
from circ import *
from collections import defaultdict
# import sys

# main
def main():
    # コマンドラインからファイルを引数で取得
    argv = sys.argv
    argc = len(argv)
    if argc!=2:
        print ("Usage: python3 ",argv[0]," filename")
        quit()
    str = argv[1]
    circ = Make_Network.blif(str)
    Print_Network.node_inf(circ)

    hi = 6 # circuit high
    wd = 7 # circuit wide
    s = Solver() # sは制約式の集合

    # 以下制約式の追加
    # op_exist is int variable : op_exist[op_id][wide][high]が存在するとき１になる
    # wire_exist is int variable : wire_exist[source_op][distination_op][wide][high]が存在するとき１になる
    # clock_zone is int variable : clock_zone[wide][high]のクロックゾーンを管理(1<=clock_zone<=4)
    # path is int variable : path[a][b][c][d]が位置の時クロックゾーン[a][b]から[c][d]にデータフローが存在する
    # ic is int variable : operatorの周りのクロックゾーンにファンイン数（ファンアウト数）と同じ数だけ入力（出力）を確約する。
    # todo : wireがoperatorから離れてしまう問題(4/30)
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[[Int("wire_exist[%d][%d][%d][%d]" % (m,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)] for m in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j, i)) for i in range(hi)] for j in range(wd)]
    path = [[[[Int("path[%d][%d][%d][%d]" % (l,k,j,i)) for i in range(hi+1)] for j in range(wd+1)] for k in range(hi+1)] for l in range(wd+1)]
    connect = [[[[Int("connect[%d][%d][%d][%d]" % (m,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(hi)] for m in range(wd)]
    # 0 <= op_exist,wire_exist,connect <= 1
    # 1 <= clock_zone <= 4
    for i in range(circ.op_num):
        for j in range(wd):
            for k in range(hi):
                s.add(0 <= op_exist[i][j][k], op_exist[i][j][k] <= 1)
                s.add(1 <= clock_zone[j][k], clock_zone[j][k] <= 4)
                for ir in range(wd):
                    for jr in range(hi):
                        s.add(0 <= connect[j][k][ir][jr], connect[j][k][ir][jr] <= 1)
                for node in range(circ.op_num):
                    s.add(0 <= wire_exist[i][node][j][k], wire_exist[i][node][j][k] <= 1)
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
            if i<wd-1:
                s.add(clock_zone[i][j]!=clock_zone[i+1][j])
            if j<hi-1:
                s.add(clock_zone[i][j]!=clock_zone[i][j+1])
    # operatorの隣接するクロックゾーンにファンイン（ファンアウト）数と同じ数のconnectを定義する制約
    # 同時にopかwireを定義する定義する制約
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                inlist = [] # この配列の総和がそのままファンイン数になる
                outlist = [] # この配列の総和がそのままファンアウト数になる
                if i < wd - 1:
                    inlist.append(connect[i + 1][j][i][j])
                    outlist.append(connect[i][j][i + 1][j])
                if i > 0:
                    inlist.append(connect[i-1][j][i][j])
                    outlist.append(connect[i][j][i-1][j])
                if j < hi - 1:
                    inlist.append(connect[i][j + 1][i][j])
                    outlist.append(connect[i][j][i][j + 1])
                if j > 0:
                    inlist.append(connect[i][j - 1][i][j])
                    outlist.append(connect[i][j][i][j - 1])
                s.add(If(op_exist[node][i][j] == 1, Sum([tmp for tmp in inlist]) == len(circ.find_node_id(node).input),
                         op_exist[node][i][j] == 0)) # opのファンイン数を定義
                s.add(If(op_exist[node][i][j] == 1, Sum([tmp for tmp in outlist]) == len(circ.find_node_id(node).output),
                        op_exist[node][i][j] == 0)) # opのファンアウト数を定義
                # opに入る方のpath
                rtmplist = [] # 右方向のwireかopを複数回使わせないための変数
                ltmplist = [] # 左方向のwireかopを複数回使わせないための変数
                utmplist = [] # 上方向のwireかopを複数回使わせないための変数
                dtmplist = [] # 下方向のwireかopを複数回使わせないための変数
                # opに入る方のpath
                for sonode in circ.find_node_id(node).input:
                    rinlist = [] # opの隣接セルを定義するための変数（右）
                    uinlist = [] # opの隣接セルを定義するための変数（左）
                    dinlist = [] # opの隣接セルを定義するための変数（下）
                    linlist = [] # opの隣接セルを定義するための変数（上）
                    id = sonode.id
                    if i < wd-1:
                        rinlist.append(op_exist[id][i+1][j])
                        rinlist.append(wire_exist[id][node][i+1][j])
                        s.add(Implies(And(op_exist[node][i][j] == 1, path[i+1][j][i][j] == 1,
                                          Sum([tmp for tmp in rtmplist]) == 0), Sum([tmp for tmp in rinlist]) == 1))
                        rtmplist.append(op_exist[id][i+1][j])
                        rtmplist.append(wire_exist[id][node][i+1][j])
                    if i > 0:
                        linlist.append(op_exist[id][i-1][j])
                        linlist.append(wire_exist[id][node][i-1][j])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i-1][j][i][j] == 1, Sum([tmp for tmp in ltmplist]) == 0,
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i+1][j][i][j]==0)),
                                Sum([tmp for tmp in linlist]) == 1))
                        ltmplist.append(op_exist[id][i-1][j])
                        ltmplist.append(wire_exist[id][node][i-1][j])
                    if j < hi-1:
                        dinlist.append(op_exist[id][i][j+1])
                        dinlist.append(wire_exist[id][node][i][j+1])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i][j+1][i][j] == 1, Sum([tmp for tmp in dtmplist]) == 0,
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i+1][j][i][j] == 0),
                                Or(Sum([tmp for tmp in ltmplist]) == 1, path[i-1][j][i][j] == 0)),
                                Sum([tmp for tmp in dinlist]) == 1))
                        dtmplist.append(op_exist[id][i][j+1])
                        dtmplist.append(wire_exist[id][node][i][j+1])
                    if j > 0:
                        uinlist.append(op_exist[id][i][j-1])
                        uinlist.append(wire_exist[id][node][i][j-1])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i][j-1][i][j] == 1, Sum([tmp for tmp in utmplist]) == 0,
                                Or(Sum([tmp for tmp in dtmplist]) == 1, path[i][j+1][i][j] == 0),
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i+1][j][i][j] == 0),
                                Or(Sum([tmp for tmp in ltmplist]) == 1, path[i-1][j][i][j] == 0)),
                                Sum([tmp for tmp in uinlist]) == 1))
                        utmplist.append(op_exist[id][i][j-1])
                        utmplist.append(wire_exist[id][node][i][j-1])
                    s.add(If(op_exist[node][i][j] == 1, Sum([tmp for tmp in rinlist])+Sum([tmp for tmp in linlist])+Sum(
                        [tmp for tmp in dinlist])+Sum([tmp for tmp in uinlist]) == 1, op_exist[node][i][j] == 0))
                rtmplist.clear()
                ltmplist.clear()
                utmplist.clear()
                dtmplist.clear()
                # opから出る方のpathに対し定義
                for tonode in circ.find_node_id(node).output:
                    routlist = []
                    uoutlist = []
                    doutlist = []
                    loutlist = []
                    id = tonode.id
                    if i < wd-1:
                        routlist.append(op_exist[id][i+1][j])
                        routlist.append(wire_exist[node][id][i+1][j])
                        s.add(Implies(And(op_exist[node][i][j] == 1, path[i][j][i+1][j] == 1,
                                          Sum([tmp for tmp in rtmplist]) == 0), Sum([tmp for tmp in routlist]) == 1))
                        rtmplist.append(op_exist[id][i+1][j])
                        rtmplist.append(wire_exist[node][id][i+1][j])
                    if i > 0:
                        loutlist.append(op_exist[id][i-1][j])
                        loutlist.append(wire_exist[node][id][i-1][j])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i][j][i-1][j] == 1, Sum([tmp for tmp in ltmplist]) == 0,
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i][j][i+1][j] == 0)),
                            Sum([tmp for tmp in loutlist]) == 1))
                        ltmplist.append(op_exist[id][i-1][j])
                        ltmplist.append(wire_exist[node][id][i-1][j])
                    if j < hi-1:
                        doutlist.append(op_exist[id][i][j+1])
                        doutlist.append(wire_exist[node][id][i][j+1])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i][j][i][j+1] == 1, Sum([tmp for tmp in dtmplist]) == 0,
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i][j][i+1][j] == 0),
                                Or(Sum([tmp for tmp in ltmplist]) == 1, path[i][j][i-1][j] == 0)),
                            Sum([tmp for tmp in doutlist]) == 1))
                        dtmplist.append(op_exist[id][i][j+1])
                        dtmplist.append(wire_exist[node][id][i][j+1])
                    if j > 0:
                        uoutlist.append(op_exist[id][i][j-1])
                        uoutlist.append(wire_exist[node][id][i][j-1])
                        s.add(Implies(
                            And(op_exist[node][i][j] == 1, path[i][j][i][j-1] == 1, Sum([tmp for tmp in utmplist]) == 0,
                                Or(Sum([tmp for tmp in dtmplist]) == 1, path[i][j][i][j+1] == 0),
                                Or(Sum([tmp for tmp in rtmplist]) == 1, path[i][j][i+1][j] == 0),
                                Or(Sum([tmp for tmp in ltmplist]) == 1, path[i][j][i-1][j] == 0)),
                            Sum([tmp for tmp in uoutlist]) == 1))
                        utmplist.append(op_exist[id][i][j-1])
                        utmplist.append(wire_exist[node][id][i][j-1])
                    s.add(If(op_exist[node][i][j] == 1,
                             Sum([tmp for tmp in routlist])+Sum([tmp for tmp in loutlist])+Sum(
                                 [tmp for tmp in doutlist])+Sum([tmp for tmp in uoutlist]) == 1,
                             op_exist[node][i][j] == 0))
                rtmplist.clear()
                ltmplist.clear()
                utmplist.clear()
                dtmplist.clear()
    # wireに対してpathを定義する
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                inlist = []
                outlist = []
                if i < wd-1:
                    inlist.append(connect[i+1][j][i][j])
                    outlist.append(connect[i][j][i+1][j])
                if i > 0:
                    inlist.append(connect[i-1][j][i][j])
                    outlist.append(connect[i][j][i-1][j])
                if j < hi-1:
                    inlist.append(connect[i][j+1][i][j])
                    outlist.append(connect[i][j][i][j+1])
                if j > 0:
                    inlist.append(connect[i][j-1][i][j])
                    outlist.append(connect[i][j][i][j-1])
                rtmplist = []
                ltmplist = []
                dtmplist = []
                utmplist = []
                for sonode in circ.find_node_id(node).input:
                    id = sonode.id
                    s.add(If(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in inlist]) == 1,
                            wire_exist[id][node][i][j] == 0))  # wireに対してイン数を定義(in)
                    s.add(If(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in outlist]) == 1,
                            wire_exist[id][node][i][j] == 0))  # wireに対してアウト数を定義(out)
                    rinlist = []
                    linlist = []
                    dinlist = []
                    uinlist = []
                    if i < wd-1:
                        rinlist.append(wire_exist[id][node][i+1][j])
                        rinlist.append(op_exist[id][i+1][j])
                        s.add(Implies(And(wire_exist[id][node][i][j]==1, path[i+1][j][i][j]==1), Sum([tmp for tmp in rinlist])==1))
                        rtmplist.append(wire_exist[id][node][i+1][j])
                        rtmplist.append(op_exist[id][i+1][j])
                    if i > 0:
                        linlist.append(wire_exist[id][node][i-1][j])
                        linlist.append(op_exist[id][i-1][j])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i-1][j][i][j] == 1,
                                          Or(path[i+1][j][i][j] == 0, Sum([tmp for tmp in rtmplist]) == 1)),
                                        Sum([tmp for tmp in linlist]) == 1))
                        ltmplist.append(wire_exist[id][node][i-1][j])
                        ltmplist.append(op_exist[id][i-1][j])
                    if j < hi-1:
                        dinlist.append(wire_exist[id][node][i][j+1])
                        dinlist.append(op_exist[id][i][j+1])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i][j+1][i][j] == 1,
                                          Or(path[i+1][j][i][j] == 0, Sum([tmp for tmp in rtmplist]) == 1),
                                          Or(path[i-1][j][i][j] == 0, Sum([tmp for tmp in ltmplist]) == 1)),
                                      Sum([tmp for tmp in dinlist]) == 1))
                        dtmplist.append(wire_exist[id][node][i][j+1])
                        dtmplist.append(op_exist[id][i][j+1])
                    if j > 0:
                        uinlist.append(wire_exist[id][node][i][j-1])
                        uinlist.append(op_exist[id][i][j-1])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i][j-1][i][j] == 1,
                                          Or(path[i+1][j][i][j] == 0, Sum([tmp for tmp in rtmplist]) == 1),
                                          Or(path[i-1][j][i][j] == 0, Sum([tmp for tmp in ltmplist]) == 1),
                                          Or(path[i][j+1][i][j] == 0, Sum([tmp for tmp in dtmplist]) == 1),),
                                      Sum([tmp for tmp in uinlist]) == 1))
                        utmplist.append(wire_exist[id][node][i][j-1])
                        utmplist.append(op_exist[id][i][j-1])
                    s.add(If(op_exist[node][i][j] == 1,
                             Sum([tmp for tmp in rinlist])+Sum([tmp for tmp in linlist])+Sum(
                                 [tmp for tmp in dinlist])+Sum([tmp for tmp in uinlist]) == 1,
                             op_exist[node][i][j] == 0))
                rtmplist.clear()
                ltmplist.clear()
                utmplist.clear()
                dtmplist.clear()
                for tonode in circ.find_node_id(node).output:
                    id = tonode.id
                    routlist = []
                    loutlist = []
                    doutlist = []
                    uoutlist = []
                    if i < wd-1:
                        routlist.append(wire_exist[node][id][i+1][j])
                        routlist.append(op_exist[id][i+1][j])
                        s.add(Implies(And(wire_exist[node][id][i][j] == 1, path[i][j][i+1][j] == 1),
                                      Sum([tmp for tmp in routlist]) == 1))
                        rtmplist.append(wire_exist[node][id][i+1][j])
                        rtmplist.append(op_exist[id][i+1][j])
                    if i > 0:
                        loutlist.append(wire_exist[id][node][i-1][j])
                        loutlist.append(op_exist[id][i-1][j])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i][j][i-1][j] == 1,
                                          Or(path[i][j][i+1][j] == 0, Sum([tmp for tmp in rtmplist]) == 1)),
                                      Sum([tmp for tmp in loutlist]) == 1))
                        ltmplist.append(wire_exist[id][node][i-1][j])
                        ltmplist.append(op_exist[id][i-1][j])
                    if j < hi-1:
                        doutlist.append(wire_exist[id][node][i][j+1])
                        doutlist.append(op_exist[id][i][j+1])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i][j][i][j+1] == 1,
                                          Or(path[i][j][i+1][j] == 0, Sum([tmp for tmp in rtmplist]) == 1),
                                          Or(path[i][j][i-1][j] == 0, Sum([tmp for tmp in ltmplist]) == 1)),
                                      Sum([tmp for tmp in doutlist]) == 1))
                        dtmplist.append(wire_exist[id][node][i][j+1])
                        dtmplist.append(op_exist[id][i][j+1])
                    if j > 0:
                        uoutlist.append(wire_exist[id][node][i][j-1])
                        uoutlist.append(op_exist[id][i][j-1])
                        s.add(Implies(And(wire_exist[id][node][i][j] == 1, path[i][j][i][j-1] == 1,
                                          Or(path[i][j][i+1][j] == 0, Sum([tmp for tmp in rtmplist]) == 1),
                                          Or(path[i][j][i-1][j] == 0, Sum([tmp for tmp in ltmplist]) == 1),
                                          Or(path[i][j][i][j+1] == 0, Sum([tmp for tmp in dtmplist]) == 1), ),
                                      Sum([tmp for tmp in uoutlist]) == 1))
                        utmplist.append(wire_exist[id][node][i][j-1])
                        utmplist.append(op_exist[id][i][j-1])
                    s.add(If(op_exist[node][i][j] == 1, Sum([tmp for tmp in routlist])+Sum([tmp for tmp in loutlist])+Sum(
                        [tmp for tmp in doutlist])+Sum([tmp for tmp in uoutlist]) == 1, op_exist[node][i][j] == 0))
                rtmplist.clear()
                ltmplist.clear()
                utmplist.clear()
                dtmplist.clear()
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
    # connectが存在する所にpathを通す制約
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    s.add(Implies(connect[i][j][ir][jr]==1, path[i][j][ir][jr]==1))
    # wireが合流しないようにする制約
    for i in range(wd):
        for j in range(hi):
                intmplist = []
                outtmplist = []
                if i<wd-1:
                    intmplist.append(path[i+1][j][i][j])
                    outtmplist.append(path[i][j][i+1][j])
                if i>0:
                    intmplist.append(path[i-1][j][i][j])
                    outtmplist.append(path[i][j][i-1][j])
                if j<hi - 1:
                    intmplist.append(path[i][j+1][i][j])
                    outtmplist.append(path[i][j][i][j+1])
                if j>0:
                    intmplist.append(path[i][j-1][i][j])
                    outtmplist.append(path[i][j][i][j-1])
                for node in range(circ.op_num):
                    for sonode in circ.find_node_id(node).input:
                        id = sonode.id
                        s.add(Implies(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in intmplist]) <= 1))
                        s.add(Implies(wire_exist[id][node][i][j] == 1, Sum([tmp for tmp in outtmplist]) <= 1))
    # wireがあった場合sourceのopにつながっているようにする制約
    for i in range(wd):
        for j in range(hi):
            for node in range(circ.op_num):
                for sonode in circ.find_node_id(node).input:
                    id = sonode.id
                    for ir in range(wd):
                        for jr in range(hi):
                            s.add(Implies(And(wire_exist[id][node][i][j]==1, op_exist[id][ir][jr]==1), path[ir][jr][i][j]==1))
    # 空白のクロックゾーンからpathが出ないようにする制約
    for i in range(wd):
        for j in range(hi):
            tmplist = []
            for node in range(circ.op_num):
                tmplist.append(op_exist[node][i][j])
                for sonode in circ.find_node_id(node).input:
                    id = sonode.id
                    tmplist.append(wire_exist[id][node][i][j])
            if i < wd-1:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(path[i][j][i+1][j] == 0, path[i+1][j][i][j] == 0)))
            if i > 0:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(path[i][j][i-1][j] == 0, path[i-1][j][i][j] == 0)))
            if j < hi-1:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(path[i][j][i][j+1] == 0, path[i][j+1][i][j] == 0)))
            if j > 0:
                s.add(Implies(Sum([tmp for tmp in tmplist]) == 0, And(path[i][j][i][j-1] == 0, path[i][j][i][j-1] == 0)))
    # 同じクロックゾーンを跨るpathが2つ以上存在しない制約
    for i in range(wd):
        for j in range(hi):
            tmplist = []
            clist = []
            if i < wd - 1:
                tmplist.append(path[i+1][j][i][j])
                tmplist.append(path[i][j][i+1][j])
                s.add(Sum([tmp for tmp in tmplist])<=1)
                clist.append(connect[i+1][j][i][j])
                clist.append(connect[i][j][i+1][j])
                s.add(Sum([tmp for tmp in clist])<=1)
                tmplist.clear()
                clist.clear()
            if i > 0:
                tmplist.append(path[i-1][j][i][j])
                tmplist.append(path[i][j][i-1][j])
                s.add(Sum([tmp for tmp in tmplist]) <= 1)
                clist.append(connect[i - 1][j][i][j])
                clist.append(connect[i][j][i - 1][j])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                tmplist.clear()
                clist.clear()
            if j < hi - 1:
                tmplist.append(path[i][j+1][i][j])
                tmplist.append(path[i][j][i][j+1])
                s.add(Sum([tmp for tmp in tmplist]) <= 1)
                clist.append(connect[i][j+1][i][j])
                clist.append(connect[i][j][i][j+1])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                tmplist.clear()
                clist.clear()
            if j > 0:
                tmplist.append(path[i][j-1][i][j])
                tmplist.append(path[i][j][i][j-1])
                clist.append(connect[i][j-1][i][j])
                clist.append(connect[i][j][i][j-1])
                s.add(Sum([tmp for tmp in clist]) <= 1)
                s.add(Sum([tmp for tmp in tmplist]) <= 1)
    # クロックゾーンが提供するデータパスに従ってのみpathを定義できる制約
    for i in range(wd):
        for j in range(hi):
            if i < wd-1:
                s.add(If(path[i][j][i+1][j] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i+1][j] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i+1][j] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i+1][j] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i+1][j] == 1)),
                                                     path[i][j][i+1][j] == 0))
            if i > 0:
                s.add(If(path[i][j][i-1][j] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i-1][j] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i-1][j] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i-1][j] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i-1][j] == 1)),
                                                     path[i][j][i-1][j] == 0))
            if j < hi-1:
                s.add(If(path[i][j][i][j+1] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i][j+1] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i][j+1] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i][j+1] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i][j+1] == 1)),
                                                     path[i][j][i][j+1] == 0))
            if j > 0:
                s.add(If(path[i][j][i][j-1] == 1, Or(And(clock_zone[i][j] == 1, clock_zone[i][j-1] == 2),
                                                     And(clock_zone[i][j] == 2, clock_zone[i][j-1] == 3),
                                                     And(clock_zone[i][j] == 3, clock_zone[i][j-1] == 4),
                                                     And(clock_zone[i][j] == 4, clock_zone[i][j-1] == 1)),
                                                     path[i][j][i][j-1] == 0))
    # pathが存在するところにはopかwireが存在するという制約
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
                print(' [%s:%s] '% (frg, ), end='')
                frg = '*'
            print()
        # for node in range(circ.op_num)
        # print path
        print("\npath")
        for j in range(hi):
            for i in range(wd-1):
                print("[ ]",end='')
                if m[path[i][j][i+1][j]].as_long()==1:
                    print(">",end='')
                elif m[path[i+1][j][i][j]].as_long()==1:
                    print("<",end='')
                else:
                    print(" ",end='')
            print("[ ]")
            for i in range(wd):
                if j<hi-1 and m[path[i][j][i][j+1]].as_long()==1:
                    print(" v  ",end='')
                elif j<hi-1 and m[path[i][j+1][i][j]].as_long()==1:
                    print(" A  ",end='')
                else:
                    print("    ",end='')
            print()
        """
        print("\nconnect")
        for j in range(hi):
            for i in range(wd-1):
                print("[ ]",end='')
                if m[connect[i][j][i+1][j]].as_long()==1:
                    print(">",end='')
                elif m[connect[i+1][j][i][j]].as_long()==1:
                    print("<",end='')
                else :
                    print(" ",end='')
            print("[ ]")
            for i in range(wd):
                if j<hi-1 and m[connect[i][j][i][j+1]].as_long() == 1:
                    print(" V ",end='')
                elif j<hi-1 and m[connect[i][j+1][i][j]].as_long() == 1:
                    print(" A ",end='')
                else:
                    print("   ",end='')
                print(" ",end='')
            print()
        
        print("\nclock_zone")
        for j in range(hi):
            for i in range(wd):
                print (" [%d] " % m[clock_zone[i][j]].as_long(), end='')
            print()
        print()
        """""
    else:
        print(r)

if __name__ == '__main__':
    main()
