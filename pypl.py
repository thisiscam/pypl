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
	def seman_derive(self):
		gen = self.seman_gen(1)
		s = gen.next() + "\\\\"
		for deriv in gen:
			if deriv[0] == "[" and deriv[-1] == "]":
				deriv = deriv[1:-1] # hack, who cares
			s += "\n\t\\indent iff \\quad {0} \\\\".format(deriv)
		return s

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
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.var_name, tf)
		yield "$I({0})$ = {1}".format(self.var_name, tf)

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
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.latex_str(), tf)
		for body_gen in self.content.seman_gen(1 - tf):
			yield body_gen

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
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.latex_str(), tf)
		lv, mid, rv = self.seman_deriv_expands(tf)
		if isinstance(self.left, PL_Var_Exp) and isinstance(self.right, PL_Var_Exp):
			for left_gen, right_gen in zip(self.left.seman_gen(lv), self.right.seman_gen(rv)):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen)
		else:
			left_final_gen = None
			righ_generator = self.right.seman_gen(rv)
			right_gen_init = righ_generator.next()
			for left_gen in self.left.seman_gen(lv):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen_init)
				left_final_gen = left_gen
			for right_gen in righ_generator:
				yield "[{0} {1} {2}]".format(left_final_gen, mid, right_gen)

class PL_And_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " & " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] and lr[1]
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\wedge " + self.right.latex_str() + ")"
	def seman_deriv_expands(self, tf):
		if tf:
			return (1, "and", 1)
		else:
			return (0, "or", 0)

class PL_Or_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " | " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] or lr[1]
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\vee " + self.right.latex_str() + ")"
	def seman_deriv_expands(self, tf):
		if tf:
			return (1, "or", 1)
		else:
			return (0, "and", 0)

class PL_Cond_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " -> " + str(self.right) + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[1] if lr[0] else True
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\supset " + self.right.latex_str() + ")"
	def seman_deriv_expands(self, tf):
		if tf:
			return (0, "or", 1)
		else:
			return (1, "and", 0)

class PL_Bicond_Exp(PL_Bin_Exp):
	def __str__(self):
		return "(" + str(self.left) + " = " + str(self.right) + ")"
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\leftrightarrow " + self.right.latex_str() + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] == lr[1]
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.latex_str(), tf)
		left_final_gen0, left_final_gen1 = None, None
		righ_generator0, righ_generator1 = self.right.seman_gen(0), self.right.seman_gen(1)
		right_gen_init0, right_gen_init1 = righ_generator0.next(), righ_generator1.next()
		for left_gen0, left_gen1 in zip(self.left.seman_gen(0), self.left.seman_gen(1)):
			yield "[[{0} and {1}] or [{2} and {3}]]".format(left_gen0, right_gen_init0, 
														left_gen1, right_gen_init1)
			left_final_gen0, left_final_gen1 = left_gen0, left_gen1
		for right_gen0, right_gen1 in zip(self.right.seman_gen(0), self.right.seman_gen(1)):
			yield "[[{0} and {1}] or [{2} and {3}]]".format(left_final_gen0, right_gen0, 
														left_final_gen1, right_gen1)

def make_latex_table(table):
	num_cols = len(table)
	num_rows = len(table.values()[0]) if len(table) > 0 else 1
	s = "\\begin{center}\\begin{tabular}{|" + "c|" * num_cols + "}\n\t\\hline\n"
	s += "\t" + reduce(lambda s1, s2: s1 + s2, map(lambda pl: "$" + pl.latex_str() + "$" + " & ", table.keys()))
	s = s[:-2] + "\\\\\n\t\\hline\n"
	for i in range(num_rows):
		s += "\t" + reduce(lambda s1, s2: s1 + s2, map(lambda col: ("T" if col[i] else "F") + " & ", table.values()))
		s = s[:-2] + "\\\\\n"
	s += "\t\\hline\n\\end{tabular}\\end{center}"
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
	'COMMA',
	'CMD_LATEX_TABLE',
	'CMD_SEMANTIC_DERIV'
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
def t_CMD_LATEX_TABLE(t):
	r'table'
	t.value = "CMD_LATEX_TABLE"
	return t
def t_CMD_SEMANTIC_DERIV(t):
	r'derive'
	t.value = "CMD_SEMANTIC_DERIV"
	return t

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

start = "command"

def p_empty_command(p):
	"""command : """	
	p[0] = ("CMD_EMPTY", None)

def p_command(p):
	"""
		command : CMD_LATEX_TABLE statement
				| CMD_SEMANTIC_DERIV statement
	"""
	p[0] = (p[1], p[2])

def p_statement_exp(p):
	"""statement : exp"""
	p[0] = PL_Exp_Set((p[1],))

def p_statement_list(p):
	"""statement : exp COMMA statement"""
	p[0] = PL_Exp_Set((p[1],)) | p[3]

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

def run_cmd(cmd, pl_tree_set):
	if cmd == "CMD_LATEX_TABLE":
		if pl_tree_set != None and len(pl_tree_set) != 0 :
			table = pl_tree_set.make_table()
			print make_latex_table(table)
	elif cmd == "CMD_SEMANTIC_DERIV":
		if pl_tree_set != None and len(pl_tree_set) == 1:
			pl_tree = pl_tree_set[0]
			print pl_tree.seman_derive()
	elif cmd == "CMD_EMPTY":
		pass
	else:
		print "Invalid command. "

import ply.yacc as yacc
yacc.yacc()

while True:
	try:
		s = raw_input('PL> ')
	except EOFError:
		break
	cmd, pl_tree_set = yacc.parse(s)
	run_cmd(cmd, pl_tree_set)
