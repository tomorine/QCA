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
    #Print_Network.node_inf(circ)

    # 制約式の追加
    # test case in 4*4 clock zones
    hi = 4 # circuit high
    wd = 5 # circuit wide
    s = Solver()
    
    # gate_exist is bool variable : gate_exist[gate_num][wide][high]
    gate_exist = [[[Int("gate_exist[%d][%d][%d]" % (k,j,i)) for i in range(hi)] for j in range(wd)]for k in range(1,len(circ.intnode)+1)]

    # 0 <= gate_exist[i][j][k] <= 1
    for i in range(1,len(circ.intnode)):
        for j in range(wd):
            for k in range(hi):
                s.add(0 <= gate_exist[i][j][k], gate_exist[i][j][k] <= 1)

    # gate should be used only once
    for i in range(1,len(circ.intnode)):
        tmplist = []
        for j in range(wd):
            for k in range(hi):
                tmplist.append(gate_exist[i][j][k])
        s.add(Sum([tmp for tmp in tmplist]) == 1)

    # clock zone can have only one gate
    for k in range(hi):
        for j in range(wd):
            tmplist = []
            for i in range(1,len(circ.intnode)):
                #print("gate_exist[%d][%d][%d]" % (i,j,k))
                tmplist.append(gate_exist[i][j][k])
            s.add(Sum([tmp for tmp in tmplist]) <= 1)
    # print model or unsat           
    r = s.check()
    if r == sat:
        m = s.model()
        for j in range(wd):
            frg = 0
            for k in range(hi):
                for i in range(1,len(circ.intnode)):
                    if m[gate_exist[i][j][k]].as_long() != 0:
                        frg = i
                print(frg,end='')
                frg = 0
            print()
            
    else:
        print(r)
        
if __name__ == '__main__':
    main()
