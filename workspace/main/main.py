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

    # 制約式の追加
    hi = 5 # circuit high
    wd = 5 # circuit wide
    s = Solver()
    
    # op_exist is int variable : op_exist[op_id][wide][high]
    # wire_exist is int variable : wire_exist[source_op][wide][high]
    # clock_zone is int variable : clock_zone[wide][high]
    # path is int variable : if information flow exist as operater[a][b] or wire[a][b] -> operater[c][d] or wire[c][d], path[source_node][a][b][c][d] is 1
    # ic is int variable : operatorの周りのクロックゾーンにファンイン数（ファンアウト数）と同じ数だけ入力（出力）を確約する。
    # todo : pathのデータフローが衝突する問題(4/30)
    # todo : wireがoperatorから離れてしまう問題（新しい変数icが必要）(4/30)
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[Int("wire_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j, i)) for i in range(hi)] for j in range(wd)]
    path = [[[[[Int("path[%d][%d][%d][%d][%d]" % (m,l,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(hi)] for l in range(wd)] for m in range(circ.op_num)]
    ic = [[[[Int("clock_zone[%d][%d][%d][%d]" % (m,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(hi)] for m in range(wd)]
    
    # 0 <= op_exist,wire_exist <= 1
    # 1 <= clock_zone <= 4
    for i in range(circ.op_num):
        for j in range(wd):
            for k in range(hi):
                s.add(0 <= op_exist[i][j][k], op_exist[i][j][k] <= 1)
                s.add(0 <= wire_exist[i][j][k], wire_exist[i][j][k] <= 1)
                s.add(1 <= clock_zone[j][k], clock_zone[j][k] <= 4)

    # op should be used only once
    for i in range(circ.op_num):
        tmplist = []
        for j in range(wd):
            for k in range(hi):
                tmplist.append(op_exist[i][j][k])
        s.add(Sum([tmp for tmp in tmplist]) == 1)

    # clock zone can have only one oprater or one wire
    for k in range(hi):
        for j in range(wd):
            tmplist = []
            for i in range(circ.op_num):
                tmplist.append(wire_exist[i][j][k])
                tmplist.append(op_exist[i][j][k])
            s.add(Sum([tmp for tmp in tmplist]) <= 1)

    # adjacent clock zone has different number
    for i in range(wd):
        for j in range(hi):
            if i<wd-1:
                s.add(clock_zone[i][j]!=clock_zone[i+1][j])
            if j<hi-1:
                s.add(clock_zone[i][j]!=clock_zone[i][j+1])

    # operator has adjacent wire or operator
    for j in range(wd):
        for k in range(hi):
            for i in range(circ.op_num):
                sumlist = []
                idlist=[]
                node = circ.find_node_id(i)
                if node.gatetype != 'p_input':
                    for input in node.input:
                        tmp = input.id
                        idlist.append(tmp)
                        tmplist = []
                        if j<wd-1:
                            tmplist.append(op_exist[tmp][j+1][k])
                            tmplist.append(wire_exist[tmp][j+1][k])
                        if j>0:
                            tmplist.append(op_exist[tmp][j-1][k])
                            tmplist.append(wire_exist[tmp][j-1][k])
                        if k<hi-1:
                            tmplist.append(op_exist[tmp][j][k+1])
                            tmplist.append(wire_exist[tmp][j][k+1])
                        if k>0:
                            tmplist.append(op_exist[tmp][j][k-1])
                            tmplist.append(wire_exist[tmp][j][k-1])
                        for rist in tmplist:
                            sumlist.append(rist)
                        s.add(If(op_exist[i][j][k]==1, Sum([tmp for tmp in tmplist])==1, op_exist[i][j][k]==0))
                for id in idlist:
                    s.add(If(wire_exist[id][j][k]==1, Sum([sum_ for sum_ in sumlist])>=2, wire_exist[id][j][k]==0))
                    s.add(If(op_exist[i][j][k]==1, Sum([sum_ for sum_ in sumlist])==len(node.input), op_exist[i][j][k]==0))
                    

    # wireはループしない制約
    # 0 <= path <= 1 
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    for node in range(circ.op_num):
                        s.add(path[node][i][j][ir][jr]>=0, path[node][i][j][ir][jr]<=1)
                        s.add(path[node][i][j][i][j]==0)
                        for irr in range(wd):
                            for jrr in range(hi):
                                s.add(Implies(And(path[node][i][j][ir][jr]==1, path[node][ir][jr][irr][jrr]==1),path[node][i][j][irr][jrr]==1))
    # setting path on oparater or wire
    # wireとoperatorが隣接していないクロックゾーンのpathを0にする方がきれいかも
    for tonode in range(circ.op_num):
        input = circ.find_node_id(tonode).input
        for node in input:
            for i in range(wd):
                for j in range(hi):
                    # 右方向
                    if i<wd-1:
                        # もしoparaterやwireが隣接するクロックゾーンに存在するならデータフローに従ってpathを定義する
                        s.add(Implies(Or(And(op_exist[tonode][i][j]==1, wire_exist[node.id][i+1][j]==1),And(op_exist[tonode][i][j]==1, op_exist[node.id][i+1][j]==1)), path[node.id][i+1][j][i][j]==1))
                        s.add(Implies(And(wire_exist[tonode][i][j]==1, wire_exist[node.id][i+1][j]==1), path[node.id][i+1][j][i][j]==1))
                    # 左方向
                    if i>0:
                        s.add(Implies(Or(And(op_exist[tonode][i][j]==1, wire_exist[node.id][i-1][j]==1),And(op_exist[tonode][i][j]==1, op_exist[node.id][i-1][j]==1)), path[node.id][i-1][j][i][j]==1))
                        s.add(Implies(And(wire_exist[tonode][i][j]==1, wire_exist[node.id][i-1][j]==1), path[node.id][i-1][j][i][j]==1))
                    # 下方向
                    if j<hi-1:
                        s.add(Implies(Or(And(op_exist[tonode][i][j]==1, wire_exist[node.id][i][j+1]==1),And(op_exist[tonode][i][j]==1, op_exist[node.id][i][j+1]==1)), path[node.id][i][j+1][i][j]==1))
                        s.add(Implies(And(wire_exist[tonode][i][j]==1, wire_exist[node.id][i][j+1]==1), path[node.id][i][j+1][i][j]==1))
                    # 上方向    
                    if j>0:
                        s.add(Implies(Or(And(op_exist[tonode][i][j]==1, wire_exist[node.id][i][j-1]==1),And(op_exist[tonode][i][j]==1, op_exist[node.id][i][j-1]==1)), path[node.id][i][j-1][i][j]==1))
                        s.add(Implies(And(wire_exist[tonode][i][j]==1, wire_exist[node.id][i][j-1]==1), path[node.id][i][j-1][i][j]==1))

    # wireが途切れないようにする制約
    for k in range(wd):
        for k in range(hi):
            for tonode in range(circ.op_num):
                if circ.find_node_id(tonode)!=-1:
                    for node in circ.find_node_id(tonode).input:
                        i = node.id
                        tmplist = []
                        pathlist = []
                        if j<wd-1:
                            tmplist.append(wire_exist[i][j+1][k])
                            tmplist.append(op_exist[i][j+1][k])
                            tmplist.append(op_exist[tonode][j+1][k])
                            pathlist.append(path[i][j][k][j+1][k])
                            pathlist.append(path[i][j+1][k][j][k])
                        if j>0:
                            tmplist.append(wire_exist[i][j-1][k])
                            tmplist.append(op_exist[i][j-1][k])
                            tmplist.append(op_exist[tonode][j-1][k])
                            pathlist.append(path[i][j][k][j-1][k])
                            pathlist.append(path[i][j-1][k][j][k])
                        if k>hi-1:
                            tmplist.append(wire_exist[i][j][k+1])
                            tmplist.append(op_exist[i][j][k+1])
                            tmplist.append(op_exist[tonode][j][k+1])
                            pathlist.append(path[i][j][k][j][k+1])
                            pathlist.append(path[i][j][k+1][j][k])
                        if k>0:
                            tmplist.append(wire_exist[i][j][k-1])
                            tmplist.append(op_exist[i][j][k-1])
                            tmplist.append(op_exist[tonode][j][k-1])
                            pathlist.append(path[i][j][k][j][k-1])
                            pathlist.append(path[i][j][k-1][j][k])
                        s.add(If(wire_exist[i][j][k]==1, Sum([tmp for tmp in tmplist])>=2, wire_exist[i][j][k]==0))
                        s.add(If(wire_exist[i][j][k]==1, Sum([tmpath for tmpath in pathlist])>=2, wire_exist[i][j][k]==0))
                
    # 空白のクロックゾーンからpathが出ないようにする制約
    # todo : 何故かunsatになるpath[kr]~~の制約式が怪しいのだがどこが間違っているのか(4/30)
    for i in range(wd):
        for j in range(hi):
            tmplist = []
            for k in range(circ.op_num):
                tmplist.append(op_exist[k][i][j])
                tmplist.append(wire_exist[k][i][j])
                for kr in circ.find_node_id(k).input:
                    node = kr.id
                    if i<wd-1:
                        s.add(Implies(op_exist[k][i][j]==0,path[node][i+1][j][i][j] == 0))
                        s.add(Implies(wire_exist[k][i][j] == 0, path[node][i+1][j][i][j] == 0))
                    if i>0:
                        s.add(Implies(op_exist[k][i][j] == 0, path[node][i-1][j][i][j] == 0))
                        s.add(Implies(wire_exist[k][i][j] == 0, path[node][i-1][j][i][j] == 0))
                    if j<hi-1:
                        s.add(Implies(op_exist[k][i][j] == 0, path[node][i][j+1][i][j] == 0))
                        s.add(Implies(wire_exist[k][i][j] == 0, path[node][i][j+1][i][j] == 0))
                    if j>0:
                        s.add(Implies(op_exist[k][i][j] == 0, path[node][i][j-1][i][j] == 0))
                        s.add(Implies(wire_exist[k][i][j] == 0, path[node][i][j-1][i][j] == 0))
            if i<wd-1:
                s.add(Implies(Sum([tmp for tmp in tmplist])==0, path[k][i][j][i+1][j]==0))
            if i>0:
                s.add(Implies(Sum([tmp for tmp in tmplist])==0, path[k][i][j][i-1][j]==0))
            if j<hi-1:
                s.add(Implies(Sum([tmp for tmp in tmplist])==0, path[k][i][j][i][j+1]==0))
            if j>0:
                s.add(Implies(Sum([tmp for tmp in tmplist])==0, path[k][i][j][i][j-1]==0))
               
    # 同じクロックゾーンを跨るpathが2つ以上存在しない制約
    for i in range(wd):
        for j in range(hi):
            tmplist = []
            if i < wd - 1:
                for node in range(circ.op_num):
                    tmplist.append(path[node][i+1][j][i][j])
                    tmplist.append(path[node][i][j][i+1][j])
                s.add(Sum([tmp for tmp in tmplist])<=1)
                tmplist = []
                if i > 0:
                    for node in range(circ.op_num):
                        tmplist.append(path[node][i-1][j][i][j])
                        tmplist.append(path[node][i][j][i-1][j])
                    s.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist = []
                if j < hi - 1:
                    for node in range(circ.op_num):
                        tmplist.append(path[node][i][j+1][i][j])
                        tmplist.append(path[node][i][j][i][j+1])
                    s.add(Sum([tmp for tmp in tmplist]) <= 1)
                tmplist = []
                if j > 0:
                    for node in range(circ.op_num):
                        tmplist.append(path[node][i][j-1][i][j])
                        tmplist.append(path[node][i][j][i][j-1])
                    s.add(Sum([tmp for tmp in tmplist]) <= 1)



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
            for j in range(wd):
                for i in range(circ.op_num):
                    if m[wire_exist[i][j][k]].as_long() !=0:
                        frg = i
                print(' [%s] '% frg, end='')
                frg = '*'
            print()
        # for node in range(circ.op_num)
        # print path
        print("\npath")
        for j in range(hi):
            for i in range(wd-1):
                print("[ ]",end='')
                frg = 0
                for node in range(circ.op_num):
                    if m[path[node][i][j][i+1][j]].as_long()==1:
                        print(">",end='')
                        frg = 1
                    elif m[path[node][i+1][j][i][j]].as_long()==1:
                        print("<",end='')
                        frg = 1
                if frg==0:
                    print(" ",end='')
            print("[ ]")
            for i in range(wd):
                frg = 0
                for node in range(circ.op_num):
                    if j<hi-1 and m[path[node][i][j][i][j+1]].as_long()==1:
                        print(" v  ",end='')
                        frg = 1
                    if j<hi-1 and m[path[node][i][j+1][i][j]].as_long()==1:
                        print(" A  ",end='')
                        frg = 1
                if frg==0:
                    print("    ",end='')
            print()
        print("\nclock_zone")
        for j in range(hi):
            for i in range(wd):
                print (" [%d] " % m[clock_zone[i][j]].as_long(), end='')
            print()
        print()
    else:
        print(r)
       
    
if __name__ == '__main__':
    main()
