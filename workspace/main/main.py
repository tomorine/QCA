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
    hi = 5 # circuit high
    wd = 5 # circuit wide
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

    # print model or unsat           
    r = s.check()
    if r == sat:
        m = s.model()
        print("oprater")
        for j in range(wd):
            frg = '*'
            for k in range(hi):
                for i in range(circ.op_num):
                    if m[op_exist[i][j][k]].as_long() != 0:
                        frg = i
                print(" [%s] " % frg, end='')
                frg = '*'
            print()
        print("\nwire")
        for j in range(wd):
            frg = '*'
            for k in range(hi):
                for i in range(circ.op_num):
                    if m[wire_exist[i][j][k]].as_long() !=0:
                        frg = i
                print(' [%s] '% frg, end='')
                frg = '*'
            print()
        print("\nclock_zone")
        for i in range(wd):
            for j in range(hi):
                print (" [%d] " % m[clock_zone[i][j]].as_long(), end='')
            print()
    else:
        print(r)
       
    
if __name__ == '__main__':
    main()
