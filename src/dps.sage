class Tree():
    def __init__(self,item,left=None,right=None):
        self.item = item
        self.left = left
        self.right = right
 
    def show(self):
        G = self.get_graph(Graph(), [0])
        return G.plot(layout="tree", tree_orientation = "down", figsize = 30, vertex_size = 0, fontsize = 1)
    def get_graph(self, g: Graph, cnt):
        init = cnt[0]
        if self.right:
            g.add_path([f"{init}, {self.item}", f"{cnt[0] + 1}, {self.right.item}"])
            cnt[0] = cnt[0] + 1
            self.right.get_graph(g, cnt)
        if self.left:
            g.add_path([f"{init}, {self.item}", f"{cnt[0] + 1}, {self.left.item}"])
            cnt[0] = cnt[0] + 1
            self.left.get_graph(g, cnt)
        return g
    def evaluate(self):
        if self.left==None and self.right==None: 
            return self.item
        elif self.left==None:
            return self.item(self.right.evaluate())
        else:
            return self.item(self.left.evaluate(),self.right.evaluate())

class Scheme:
    def __init__(self, left: list, ops: list, param, sch, order, n_val = var('n_val'), delta = None):
        self.scheme = sch
        self.dvar = left[0]
        self.ivar = left[1]
        self.params = param
        self.n_val = n_val
        self.explicit = True
        self.order = order
        self.tree = self.__create_tree(self.scheme)
        self.func = ops[0]
        self.op = ops[1]
        
        #if n_val != 'n_val': self.explicit = False
        
        if not delta:
            self.delta = var('d' + str(self.ivar))
        else:
            self.delta = delta
        self.__check_validity()
    
    def subs(self, tree: Tree, func, f, x, coef):
        arg = lambda v: v.variables()[0]
        fun = lambda v: [ff for (xx,ff) in zip(x,f) if xx == arg(v)][0]
        D = lambda u: sum([diff(u,xx)*ff for (xx,ff) in zip(x,f)])
        node = tree.item

        if issubclass(type(node), sage.symbolic.function.SymbolicFunction):
            func = fun(func)
            node = func
        elif node == self.op:
            if not tree.left:
                tree = self.__create_tree(D(tree.right.evaluate()))
                node = tree.item
            else:
                raise ValueError('Derivative operator error')
        elif node == self.dvar:
            node = arg(func)
        if tree.left==None and tree.right==None:
            return SR(node).subs(coef)
        elif tree.left==None:
            return node(self.subs(tree.right, func, f, x, coef))
        else:
            return node(self.subs(tree.left, func, f, x, coef),self.subs(tree.right, func, f, x, coef))
    def __subs(self, tree: Tree, func, f, x, coef):
        arg = lambda v: v.variables()[0]
        fun = lambda v: [ff for (xx,ff) in zip(x,f) if xx == arg(v)][0]
        D = lambda u: sum([diff(u,xx)*ff for (xx,ff) in zip(x,f)])
        node = tree.item

        if issubclass(type(node), sage.symbolic.function.SymbolicFunction):
            func = fun(func)
            node = func
        elif type(node) == sage.symbolic.operators.FDerivativeOperator:
            if not tree.left:
                node = fun(func)
                for _ in range(len(node.parameter_set())):
                    node = D(node)
                tree = self.__create_tree(node)
                node = tree.item
        elif node == self.dvar:
            node = arg(func)  
        return node
    def __add_to_graph(self, tree: Tree, func, f, x, coef, g: Graph, cnt):
        init = cnt[0]
        if tree.right:
            g.add_path([f"{init}, {self.__subs(tree, func, f, x, coef)}", f"{cnt[0] + 1}, {self.__subs(tree.right, func, f, x, coef)}"])
            cnt[0] = cnt[0] + 1
            self.__add_to_graph(tree.right, func, f, x, coef, g, cnt)
        if tree.left:
            g.add_path([f"{init}, {self.__subs(tree, func, f, x, coef)}", f"{cnt[0] + 1}, {self.__subs(tree.left, func, f, x, coef)}"])
            cnt[0] = cnt[0] + 1
            self.__add_to_graph(tree.left, func, f, x, coef, g, cnt)
        return g
        
    def show_substitution(self, func, f, x, coef):
        G = self.__add_to_graph(self.tree, func, f, x, coef, Graph(), [0])
        return G.plot(layout="tree", tree_orientation = "down", figsize = 30, vertex_size = 0, fontsize = 1)
    
    def __check_validity(self):
        if self.scheme.factor().operands().count(self.delta):
            raise ValueError('Scheme must not be multiplied by dt')
    def __diff_coef(self, k, G, SS, c):
        if (k == 0):
            SS = SS + solve(G.subs([self.delta == 0]), c[k])
        else:
            SS_pred = self.__diff_coef(k - 1, G, SS, c)
            solved = solve(diff(G,self.delta,k).subs([self.delta == 0]).subs(SS_pred),c[k])
            SS = SS_pred + solved
        return SS
    def latex(self):
        print(f'\\frac{{d{self.dvar}}}{{{self.delta}}} = {latex(self.scheme)}')
    def __create_tree(self, expr):

        if type(expr)==tuple:
            op = expr[0]
            operands = expr[1]
        else:
            try:
                op = expr.operator()
                operands = expr.operands()
            except:
                return Tree(expr)
        if not op:  
               return Tree(expr)
        else:
            if len(operands) > 2:
                return Tree(op,left=self.__create_tree(operands[0]),
                               right=self.__create_tree((op,operands[1:])))
            elif len(operands) == 2:
                return Tree(op,left=self.__create_tree(operands[0]),
                               right=self.__create_tree(operands[1])) 
            else:
                return Tree(op,right=self.__create_tree(operands[0]))

    def parametric_eqs(self, right = None):
        dvar = self.dvar
        delta = self.delta
        D = lambda v: diff(v)*v
        scheme = self.scheme.substitute_function(self.op, D)
        
        k = self.order + 1
        c = var(['c' + str(i) for i in range(k + 1)])
        S = [self.n_val == sum([cc*tt for (cc,tt) in zip(c,[self.delta^n for n in range(k + 1)])])]
        
        if not right: 
            right = self.func
        else:
            right = right.function(dvar, delta)
        
        A = []
        A.append(c[0] == dvar)
        for i in range(1, k):
            A = A + [c[i] == diff(c[i - 1].subs(A)) * right(dvar)]
        for i in range(1, k):
            A[i] = (A[i].operands()[1] / factorial(i) - A[i].operands()[0]).solve(c[i])

        F(n_val, dvar, delta) = scheme.substitute_function(self.func, right)
        G = self.n_val - self.dvar - F*self.delta
        G = G.subs(S)
        B = []
        B = self.__diff_coef(k, G, B, c)

        return [B[i].subs(A[i]) for i in range(k)]
    def coefficients(self, right):
        
        Y = self.parametric_eqs(right)

        R = QQ[tuple(list(self.params) + [self.ivar])]
        K = PolynomialRing(R, self.dvar, order = 'lex')
        RES = []
        for i in range(len(Y)):
            if K(Y[i].operands()[1]) == 0:
                 return [1]
            D = []
            for j in range(len(list(K(Y[i].operands()[1])))):
                org = K(Y[i].operands()[0]).list()[j] if j < len(K(Y[i].operands()[0]).list()) else 0
                D.append((SR(org - (K(Y[i].operands()[1]).list())[j])))
            RES = RES + D
        basis = (R*RES).groebner_basis()
        return basis
def dps(problem, scheme: Scheme, coef: list, N = 10):
    if not scheme.explicit:
        raise NotImplementedError("Only for explicit schemes")
    t0 = 0
    [f,x,x0,T]=problem.list()
    dt = RR(T/N)
    l = [[t0] + x0]
    fun = lambda v: [ff for (xx,ff) in zip(x,f) if xx == arg(v)][0]
    arg = lambda v: v.variables()[0]
    sch = {}
    for ff in f:
        sch[ff] = scheme.subs(scheme.tree, fun(ff), f, x, coef)
    for n in range(N):
        t0=t0+dt
        x0=[xx+ problem.subs(sch[ff]*dt, x0).subs([scheme.delta == dt]) for (xx,ff) in zip(x0,f)]
        l.append([t0]+x0)
    return Numsol(l,[t]+x,dt,scheme.order,problem)