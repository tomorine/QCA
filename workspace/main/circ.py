# tomorow@ngc.is.ritsumei.ac.jp
# writing by python3 
# coding:utf-8
from z3 import *

class Create_Node:         
    def __init__(self,name):
        self.name = name
        self.input = list()
        self.output = list()
        self.gatetype = "none"
        self.id= -1

    # ノードに対する入力の追加    
    def add_input(self,node):
        self.input.append(node)

    # ノードに対数出力の追加    
    def add_output(self,node):
        self.output.append(node)

    # ゲートタイプの定義    
    def def_gatetype(self,name):
        self.gatetype = name

    # ゲート番号の定義
    def def_opnum(self,op_num):
        self.id = op_num-1
        
# ネットワークのクラス
class Create_Network:
    def __init__(self,name):
        self.name = name
        self.intnode = list()
        self.p_input = list()
        self.p_output = list()
        self.op_num = 0

    # ネットワークの外部入力の追加    
    def add_primary_input(self,name):
        node = Create_Node(name)
        node.def_gatetype("p_input")
        self.op_num += 1
        node.def_opnum(self.op_num)
        self.p_input.append(node)

    # ネットワークの外部出力の追加    
    def add_primary_output(self,name):
        node = Create_Node(name)
        node.def_gatetype("p_output")
        self.op_num += 1
        node.def_opnum(self.op_num)
        self.p_output.append(node)

    # ネットワークの内部ノードの追加        
    def add_intnode(self,node):
        self.op_num += 1
        node.def_opnum(self.op_num)
        self.intnode.append(node)
        

    # ネットワーク内のノードを探してもしなければ新たに生成    
    def find_node(self,name):
        for node in self.intnode:
            if node.name == name:
                return node
        for node in self.p_input:
            if node.name == name:
                return node
        for node in self.p_output:
            if node.name == name:
                return node
        # 見つからない場合は新しいノードを作成。intnodeに登録
        node = Create_Node(name)
        self.add_intnode(node)
        return node

    # ネットワーク内のノードをidで探索　見つからなければ-1を返す
    def find_node_id(self,id):
        for node in self.intnode:
            if node.id == id:
                return node
        for node in self.p_input:
            if node.id == id:
                return node
        for node in self.p_output:
            if node.id == id:
                return node
        return (-1)

    
# ネットワークの中身をプリントする関数        
class Print_Network:
    @classmethod
    def node_inf(cls,circ):
        print('circuit name:',circ.name)  # print circuit
        print("primary input list\n--------------------")  # print input 
        for node in circ.p_input:
            print("%s:%d " % (node.name,node.id), end='')
        print("\n")
        print("int node list\n--------------------")  # print intnode
        for node in circ.intnode:
            print("node name:%s node id:%d " % (node.name,node.id))
            print("gatetype : %s" % node.gatetype)
            print("input : ",end='')
            for tmp in node.input:
                print("%s:%d " % (tmp.name,tmp.id),end ='')
            print()
            print("output : ",end='')
            for tmp in node.output:
                print("%s:%d " % (tmp.name,tmp.id),end='')
            print("\n")
        print("primary output list\n--------------------")  # print output
        for node in circ.p_output:
            print("%s:%d " % (node.name,node.id),end='')
        print("\n")

# ファイルから回路情報を読み取ってネットワークを作成する関数
# todo AND/OR/NOT以外にも対応させる
class Make_Network:
    @classmethod
    def blif(cls,filename):
        f = open("../b_mark/halh_adder.blif")  # デバッグ用
        #f = open(filename)                    # file open
        circ = Create_Network("none")          # circはネットワークを保持
        frg = "none"                           # frgはファイルの各行の識別子を保持
        current_node = Create_Node("none")     # currernt_nodeはintnodeに登録するノードを保持
        for line in f:
            data = line.split()
            if data[0] == ".end":
                break
            elif data[0] == "#":
                continue
            elif data[0] == ".model":
                frg = ".model"
                circ = Create_Network(data[1])
            elif data[0] == ".input":
                frg = ".input"
                data.pop(0)
                for tmp in data:
                    circ.add_primary_input(tmp)
            elif data[0] == ".output":
                frg = ".output"
                data.pop(0)
                for tmp in data:
                    circ.add_primary_output(tmp)
            elif data[0] == ".names":
                frg = ".names"
                data.pop(0)
                node = circ.find_node(data[-1])
                data.pop(-1)
                if node.gatetype == "p_output":
                    tmp = Create_Node("node_to_"+node.name)
                    tmp.add_output(node)
                    circ.add_intnode(tmp)
                    node.input.append(tmp)
                    node = tmp
                for tmp in data:
                    tmp_node = circ.find_node(tmp)
                    node.add_input(tmp_node)
                    tmp_node.add_output(node)
                    current_node = node
            elif frg == ".names":
                current_node.def_gatetype(data[0])          
        f.close()
        return circ
