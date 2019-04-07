# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8


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
    else_tmp = Int("else_tmp") #else_tmpはz3がif文を使用する際にelseの入力がないことを許可しなかったのでできた変数.基本的に意味はない.できれば消したい
    hi = 5 # circuit high
    wd = 6 # circuit wide
    s = Solver()
    
    # op_exist is int variable : op_exist[op_id][wide][high]
    # wire_exist is int variable : wire_exist[source_op][wide][high]
    # clock_zone is int variable : clock_zone[wide][high]
    # path is int variable : if information flow exist as operater[a][b] or wire[a][b] -> operater[c][d] or wire[c][d], path[source_node][destination_node][a][b][c][d] is 1
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[Int("wire_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j,i)) for i in range(hi)] for j in range(wd)]
    path = [[[[[[Int("path[%d][%d][%d][%d][%d][%d]" % (n,m,l,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(hi)] for l in range(wd)] for m in range(circ.op_num)]for n in range(circ.op_num)]
    
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
    for i in range(wd-1):
        for j in range(hi-1):
            s.add(clock_zone[i][j]!=clock_zone[i+1][j])
            s.add(clock_zone[i][j]!=clock_zone[i][j+1])

    # operater has adjacent wire or operater
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
                    

    # wire has no roop
    # 0 <= path <= 1 
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    for node in range(circ.op_num):
                        for tonode in range(circ.op_num):
                            s.add(path[node][tonode][i][j][ir][jr]>=0, path[node][tonode][i][j][ir][jr]<=1)
                        
    for i in range(circ.op_num):
        input = circ.find_node_id(i).input
        for node in input:
            for j in range(wd):
                for k in range(hi):
                    # 右方向
                    if j<wd-1:
                        s.add(If(Or(And(op_exist[i][j][k]==1, wire_exist[node.id][j+1][k]==1),And(op_exist[i][j][k]==1, op_exist[node.id][j+1][k]==1)), path[node.id][i][j+1][k][j][k]==1,path[node.id][i][j+1][k][j][k]==0))
                    # 左方向
                    if j>0:
                        s.add(If(Or(And(op_exist[i][j][k]==1, wire_exist[node.id][j-1][k]==1),And(op_exist[i][j][k]==1, op_exist[node.id][j-1][k]==1)), path[node.id][i][j-1][k][j][k]==1, path[node.id][i][j-1][k][j][k]==0))
                    # 下方向
                    if k<hi-1:
                        s.add(If(Or(And(op_exist[i][j][k]==1, wire_exist[node.id][j][k+1]==1),And(op_exist[i][j][k]==1, op_exist[node.id][j][k+1]==1)), path[node.id][i][j][k+1][j][k]==1, path[node.id][i][j][k+1][j][k]==0))
                    # 上方向    
                    if k>0:
                        s.add(If(Or(And(op_exist[i][j][k]==1, wire_exist[node.id][j][k-1]==1),And(op_exist[i][j][k]==1, op_exist[node.id][j][k-1]==1)), path[node.id][i][j][k-1][j][k]==1, path[node.id][i][j][k-1][j][k]==0))
    # print model or unsat           
    r = s.check()
    if r == sat:
        m = s.model()
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
        print("\nclock_zone")
        for j in range(hi):
            for i in range(wd):
                print (" [%d] " % m[clock_zone[i][j]].as_long(), end='')
            print()
        #for node in range(circ.op_num):
            #print(node)
        for j in range(hi):
            for i in range(wd):
                frg = 0
                for node in range(circ.op_num):
                    for tonode in range(circ.op_num):
                        if i<wd-1 and  m[path[node][tonode][i][j][i+1][j]].as_long()!=0:
                            print("[ ]>%d" % node,end='')
                            frg = 1
                        elif i<wd-1 and m[path[node][tonode][i+1][j][i][j]].as_long()!=0:
                            print("[ ]<%d" % node,end='')
                            frg = 1
                if frg == 0:                
                    print("[ ]  ",end='')
            print()
            for i in range(wd):
                frg = 0
                for node in range(circ.op_num):
                    for tonode in range(circ.op_num):
                        if j<hi-1 and m[path[node][tonode][i][j][i][j+1]].as_long()!=0:
                            print(" V%d  " % node,end='')
                            frg = 1
                        elif j<hi-1 and m[path[node][tonode][i][j+1][i][j]].as_long()!=0:
                            print(" A%d  " % node,end='')
                            frg = 1
                if frg == 0:                
                    print("     ",end='')
            print()
        print()
            
    else:
        print(r)
       
    
if __name__ == '__main__':
    main()
