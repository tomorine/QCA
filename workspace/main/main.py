# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8

# インポートz3
from z3 import *  
import sys
import circ

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

if __name__ == '__main__':
    main()
