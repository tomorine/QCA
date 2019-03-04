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
    # test case in 4*4 clock zones
    else_tmp = Int("else_tmp")
    hi = 5 # circuit high
    wd = 6 # circuit wide
    s = Solver()
    
    # op_exist is int variable : op_exist[op_id][wide][high]
    # wire_exist is int variable : wire_exist[source_op][wide][high]
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[Int("wire_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j,i)) for i in range(hi)] for j in range(wd)]

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
                tmplist = []
                node = circ.find_node_id(i)
                if node.gatetype != 'p_input':
                    for input in node.input:
                        tmp = input.id
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
                    s.add(If(op_exist[i][j][k]==1, Sum([tmp for tmp in tmplist])==len(node.input), op_exist[i][j][k]==0))
                    s.add(If(wire_exist[tmp][j][k]==1, Sum([tmp for tmp in tmplist])>=2, wire_exist[tmp][j][k]==0))

    # wire has no roop
    path = [[[[[Int("path[%d][%d][%d][%d][%d]" % (m,l,k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(hi)] for l in range(wd)] for m in range(circ.op_num)]
    for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    for node in range(circ.op_num):
                        s.add(path[node][i][j][ir][jr]>=0, path[node][i][j][ir][jr]<=1)
    for i in range(circ.op_num):
        input = circ.find_node_id(i).input
        for node in input:
            for j in range(wd):
                for k in range(hi):
                    if j<wd-1:
                        s.add(If(And(op_exist[i][j][k]==1, wire_exist[node.id][j+1][k]==1), path[node.id][j+1][k][j][k]==1,else_tmp==0))
                        s.add(If(And(op_exist[i][j][k]==1, op_exist[node.id][j+1][k]==1), path[node.id][j+1][k][j][k]==1,else_tmp==0))
                    if j>0:
                        s.add(If(And(op_exist[i][j][k]==1, wire_exist[node.id][j-1][k]==1), path[node.id][j-1][k][j][k]==1,else_tmp==0))
                        s.add(If(And(op_exist[i][j][k]==1, op_exist[node.id][j-1][k]==1), path[node.id][j-1][k][j][k]==1,else_tmp==0))
                    if k<hi-1:
                        s.add(If(And(op_exist[i][j][k]==1,wire_exist[node.id][j][k+1]==1), path[node.id][j][k+1][j][k]==1,else_tmp==0))
                        s.add(If(And(op_exist[i][j][k]==1,op_exist[node.id][j][k+1]==1), path[node.id][j][k+1][j][k]==1,else_tmp==0))
                    if k>0:
                        s.add(If(And(op_exist[i][j][k]==1, wire_exist[node.id][j][k-1]==1), path[node.id][j][k-1][j][k]==1,else_tmp==0))
                        s.add(If(And(op_exist[i][j][k]==1, op_exist[node.id][j][k-1]==1), path[node.id][j][k-1][j][k]==1,else_tmp==0))
    
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
        for node in range(circ.op_num):
            print(node)
            for j in range(hi):
                for i in range(wd):
                    print("[ ]",end='')
                    if i<wd-1 and  m[path[node][i][j][i+1][j]].as_long()!=0:
                        print(">",end='')
                    elif i<wd-1 and m[path[node][i+1][j][i][j]].as_long()!=0:
                        print("<",end='')
                    else:
                        print(" ",end='')
                print()
                for i in range(wd):
                    if j<hi-1 and m[path[node][i][j][i][j+1]].as_long()!=0:
                        print(" V  ",end='')
                    elif j<hi-1 and m[path[node][i][j+1][i][j]].as_long()!=0:
                        print(" A  ",end='')
                    else:
                        print("    ",end='')
                print()
            print()
            
    else:
        print(r)
       
    
if __name__ == '__main__':
    main()
