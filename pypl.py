import ply.lex as lex
import ply.yacc as yacc
from collections import OrderedDict
from ordered_set import OrderedSet
import readline

class PL_Exp(object): 
	def __eq__(self, other):
		return str(self) == str(other)
	def __hash__(self):
		return hash(str(self))
	def __repr__(self):
		return str(self)
	def make_table(self, table):
		pass

class PL_Exp_Set(OrderedSet): 
	def make_table(self):
		table = OrderedDict()
		for exp in self:
			exp.make_table(table)
		return table

def make_table_memo(make_table):
	def wrapper(self, table):
		if self not in table:
			make_table(self, table)
	return wrapper

class PL_Var_Exp(PL_Exp):
	def __init__(self, var_name):
		self.var_name = var_name
	def __str__(self):
		return self.var_name
	@make_table_memo
	def make_table(self, table):
		for pl, col in table.items():
			table[pl] = reduce(lambda x, y: x + y, map(lambda item: [item, item], col))
		table[self] = [True, False] * (len(table.values()[0])/2 if len(table) > 0 else 1)
	def latex_str(self):
		return str(self)

class PL_Neg_Exp(PL_Exp):
	def __init__(self, content):
		self.content = content
	def __str__(self):
		return "!" + str(self.content)
	@make_table_memo
	def make_table(self, table):
		self.content.make_table(table)
		table[self] = list(map(lambda item: not item, table[self.content]))
	def latex_str(self):
		return "\\neg " + self.content.latex_str()

class PL_Bin_Exp(PL_Exp):
	def __init__(self, left, right):
		self.left = left
		self.right = right
	@make_table_memo
	def make_table(self, table):
		self.left.make_table(table)
		self.right.make_table(table)
		table[self] = list(map(self.make_table_op, 
							zip(table[self.left], table[self.right])))

class PL_And_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " & " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] and lr[1]
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\wedge " + self.right.latex_str() + ")"

class PL_Or_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " | " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] or lr[1]
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\vee " + self.right.latex_str() + ")"

class PL_Cond_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " -> " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[1] if lr[0] else True
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\supset " + self.right.latex_str() + ")"

class PL_Bicond_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " = " + str(self.right) + ")"
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\leftrightarrow " + self.right.latex_str() + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] == lr[1]

def make_latex_table(table):
	num_cols = len(table)
	num_rows = len(table.values()[0]) if len(table) > 0 else 1
	s = "\\begin{tabular}{|" + "c|" * num_cols + "}\n\t\\hline\n"
	s += "\t" + reduce(lambda s1, s2: s1 + s2, map(lambda pl: "$" + pl.latex_str() + "$" + " & ", table.keys()))
	s = s[:-2] + "\\\\\n\t\\hline\n"
	for i in range(num_rows):
		s += "\t" + reduce(lambda s1, s2: s1 + s2, map(lambda col: ("T" if col[i] else "F") + " & ", table.values()))
		s = s[:-2] + "\\\\\n"
	s += "\t\\hline\n\\end{tabular}"
	return s

tokens = (
 	'PL_AND',
 	'PL_OR',
  	'PL_NEG',
    'PL_COND',
    'PL_BICOND',
    'PL_VAR',
    'LPAREN',
    'RPAREN',
    'COMMA'
 )

t_PL_AND = r'\&|\\wedge|and'
t_PL_OR = r'\||\\vee|or'
t_PL_NEG = r'\!|\\neg|not'
t_PL_COND = r'->|\\supset'
t_PL_BICOND = r'=|\\leftrightarrow'
t_PL_VAR = r'[A-Z]'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_COMMA = r','

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)
# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'
# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

lexer = lex.lex()

# Precedence rules for operators, though parenthesis is standard
precedence = (
    ('left','PL_AND','PL_OR'),
    ('left','PL_COND','PL_BICOND'),
    ('right','PL_NEG'),
)

start = "statement"

def p_statement_exp(p):
	"""statement : exp"""
	p[0] = PL_Exp_Set((p[1],))

def p_statement_list(p):
	"""statement : exp COMMA statement"""
	p[0] = PL_Exp_Set((p[1],)) | p[3]

def p_statement_empty(p):
	"""statement : """
	p[0] = PL_Exp_Set()

def p_exp_and(p):
	"""exp : exp PL_AND exp"""
	p[0] = PL_And_Exp(p[1], p[3])

def p_exp_or(p):
	"""exp : exp PL_OR exp"""
	p[0] = PL_Or_Exp(p[1], p[3])

def p_exp_cond(p):
	"""exp : exp PL_COND exp"""
	p[0] = PL_Cond_Exp(p[1], p[3])

def p_exp_bicond(p):
	"""exp : exp PL_BICOND exp"""
	p[0] = PL_Bicond_Exp(p[1], p[3])

def p_exp_neg(p):
	"""exp : PL_NEG exp"""
	p[0] = PL_Neg_Exp(p[2])

def p_exp_group(p):
	"""exp : LPAREN exp RPAREN"""
	p[0] = p[2]

def p_exp_var(p):
	"""exp : PL_VAR"""
	p[0] = PL_Var_Exp(p[1])

def p_error(p):
    print("Syntax error at '%s'" % p.value)

import ply.yacc as yacc
yacc.yacc()

while True:
    try:
        s = raw_input('PL> ')
    except EOFError:
        break
    pl_tree_set = yacc.parse(s)
    if pl_tree_set != None and len(pl_tree_set) != 0 :
	    table = pl_tree_set.make_table()
	    print make_latex_table(table)