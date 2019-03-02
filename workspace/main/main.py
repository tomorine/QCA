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
    hi = 4 # circuit high
    wd = 5 # circuit wide
    s = Solver()
    
    # op_exist is int variable : op_exist[op_num][wide][high]
    # wire_exist is int variable : wire_exist[wide][high]
    op_exist = [[[Int("op_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(circ.op_num)]
    wire_exist = [[[Int("wire_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)] for k in range(circ.op_num)]
    clock_zone = [[Int("clock_zone[%d][%d]" % (j,i)) for i in range(hi)] for j in range(wd)]

    # 0 <= op_exist,wire_exist <= 1
    # 1 <= clock_zone <= 4
    for i in range(circ.op_num):
        for j in range(wd):
            for k in range(hi):
                s.add(0 <= op_exist[i][j][k], op_exist[i][j][k] <= 1)
                s.add(0 <= wire_exist[j][k], wire_exist[j][k] <= 1)
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
            tmplist.append(wire_exist[j][k])
            for i in range(circ.op_num):
                tmplist.append(op_exist[i][j][k])
            s.add(Sum([tmp for tmp in tmplist]) <= 1)

    for i in range(wd-1):
        for j in range(hi-1):
            s.add(clock_zone[i][j]!=clock_zone[i+1][j])
            s.add(clock_zone[i][j]!=clock_zone[i][j+1])            

     # print model or unsat           
    r = s.check()
    if r == sat:
        m = s.model()
        for j in range(wd):
            frg = 0
            for k in range(hi):
                for i in range(circ.op_num):
                    if m[op_exist[i][j][k]].as_long() != 0:
                        frg = i+1
                print(" %d " % frg, end='')
                frg = 0
            print()
            
    else:
        print(r)

    if r == sat:
        m = s.model()
        for i in range(wd):
            for j in range(hi):
                print (m[clock_zone[i][j]].as_long(), end='')
            print()
    
if __name__ == '__main__':
    main()
