for i in range(wd):
        for j in range(hi):
            for ir in range(wd):
                for jr in range(hi):
                    for node in range(circ.op_num):
                        if ir<wd-1:
                            s.add(If(path[node][i][j][ir][jr]==1 and wire_exist[node][ir+1][jr]==1, path[node][i][j][ir+1][jr]==1, path[node][i][j][ir][jr]==0))
                            s.add(If(path[node][i][j][ir][jr]==1 and op_exist[node][ir+1][jr]==1, path[node][i][j][ir+1][jr]==1, path[node][i][j][ir][jr]==0))
                        if ir>0:
                            s.add(If(path[node][i][j][ir][jr]==1 and wire_exist[node][ir-1][jr]==1, path[node][i][j][ir-1][jr]==1, path[node][i][j][ir][jr]==0))
                            s.add(If(path[node][i][j][ir][jr]==1 and op_exist[node][ir-1][jr]==1, path[node][i][j][ir-1][jr]==1, path[node][i][j][ir][jr]==0))
                        if jr<hi-1:
                            s.add(If(path[node][i][j][ir][jr]==1 and wire_exist[node][ir][jr+1]==1, path[node][i][j][ir][jr+1]==1, path[node][i][j][ir][jr]==0))
                            s.add(If(path[node][i][j][ir][jr]==1 and op_exist[node][ir][jr+1]==1, path[node][i][j][ir][jr+1]==1, path[node][i][j][ir][jr]==0))
                        if jr>0:
                            s.add(If(path[node][i][j][ir][jr]==1 and wire_exist[node][ir][jr-1]==1, path[node][i][j][ir][jr-1]==1, path[node][i][j][ir][jr]==0))
                            s.add(If(path[node][i][j][ir][jr]==1 and op_exist[node][ir][jr-1]==1, path[node][i][j][ir][jr-1]==1, path[node][i][j][ir][jr]==0))
                        s.add(path[node][i][j][i][j]==0)   
