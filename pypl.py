# -*- coding: utf-8 -*-

import ply.lex as lex
import ply.yacc as yacc
from collections import OrderedDict
from ordered_set import OrderedSet
import readline
import clipboard

class AssignmengFunctionG(OrderedDict):
	def __init__(self, *args, **kwargs):
		super(AssignmengFunctionG, self).__init__(*args, **kwargs)
		self.used_d_count = 0
	def add_variable(self, var):
		if self.used_d_count == 0:
			self[var] = "d"
		elif self.used_d_count == 1:
			self[var] = "d'"
		else:
			self[var] = "d^{{{0}}}".format(self.used_d_count)
		self.used_d_count += 1
		return self[var]
	def copy(self):
		new_obj = super(AssignmengFunctionG, self).copy()
		new_obj.used_d_count = self.used_d_count
		return new_obj

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
		s = gen.next() + " \\\\"
		for deriv in gen:
			if deriv[0] == "[" and deriv[-1] == "]":
				deriv = deriv[1:-1] # hack, who cares
			s += "\n\t\\hspace*{{1em}} iff \\quad {0} \\\\".format(deriv)
		return s
	def fol_seman_derive(self):
		g = AssignmengFunctionG()
		gen = self.fol_seman_gen(g, 1)
		s = gen.next() + " \\\\"
		for deriv in gen:
			if deriv[0] == "[" and deriv[-1] == "]":
				deriv = deriv[1:-1] # hack, who cares
			s += "\n\\tiff {0} \\\\".format(deriv)
		return s

def tf_to_not(tf):
	if tf == 1:
		return ""
	else:
		return "\\not"

def g_map_str(g):
	if len(g) == 0:
		return "g"
	elif len(g) == 1:
		k, v = g.items()[0]
		return "g^{{{0}\\to {1}}}".format(k, v)
	elif len(g) == 2:
		k1, v1 = g.items()[0]
		k2, v2 = g.items()[1]
		return "g^{{{0}\\to {1}}}_{{{2}\\to {3}}}".format(k1, v1, k2, v2)
	else:
		k_last, v_last = g.items()[-1]
		vstack = "\\\\".join("{0}\\to {1}".format(k,v) for k,v in g.items()[:-1])
		return "g^{{\\substack{{{0}}}}}_{{{1}\\to {2}}}".format(vstack, k_last, v_last)

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

class PL_Atomic_Formula_Exp(PL_Exp):
	def __init__(self, atomicformula_name, terms):
		self.atomicformula_name = atomicformula_name
		self.terms = terms
	def __str__(self):
		return self.atomicformula_name + "".join(str(t) for t in self.terms)
	@make_table_memo
	def make_table(self, table):
		for pl, col in table.items():
			table[pl] = reduce(lambda x, y: x + y, map(lambda item: [item, item], col))
		table[self] = [True, False] * (len(table.values()[0])/2 if len(table) > 0 else 1)
	def latex_str(self):
		return str(self)
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.atomicformula_name, tf)
		yield "$I({0})$ = {1}".format(self.atomicformula_name, tf)
	def fol_seman_gen(self, g, tf):
		yield "\\M{0}\\m_{{{1}}}{2}".format(tf_to_not(tf), g_map_str(g), self.latex_str())
		if len(self.terms) == 0:
			yield "\\I({0})={1}".format(self.atomicformula_name, tf)
		elif len(self.terms) == 1:
			for t_gen in self.terms[0].fol_term_gen(g):
				yield "{0}{1}\\in\\I({2})".format(t_gen, tf_to_not(tf), self.atomicformula_name)
		else:
			for i, term in enumerate(self.terms):
				tuple_pre = ",".join(self.terms[:i]) + "," if i > 0 else ""
				tuple_post = "," + ",".join(map(lambda t: t.denotation_str(g), self.terms[i+1:])) if i < len(self.terms) - 1 else ""
				last_t_gen = None
				for t_gen in term.fol_term_gen(g):
					yield "\\tuple{{{0}{1}{2}}}{3}\\in\\I({4})".format(tuple_pre, t_gen, tuple_post, 
															tf_to_not(tf), self.atomicformula_name)
					last_t_gen = t_gen
				self.terms[i] = last_t_gen


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
	def fol_seman_gen(self, g, tf):
		yield "\\M{0}\\m_{{{1}}}{2}".format(tf_to_not(tf), g_map_str(g), self.latex_str())
		for body_gen in self.content.fol_seman_gen(g, 1 - tf):
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
		if isinstance(self.left, PL_Atomic_Formula_Exp) and isinstance(self.right, PL_Atomic_Formula_Exp):
			for left_gen, right_gen in zip(self.left.seman_gen(lv), self.right.seman_gen(rv)):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen)
		else:
			left_final_gen = None
			right_generator = self.right.seman_gen(rv)
			right_gen_init = right_generator.next()
			for left_gen in self.left.seman_gen(lv):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen_init)
				left_final_gen = left_gen
			for right_gen in right_generator:
				yield "[{0} {1} {2}]".format(left_final_gen, mid, right_gen)
	def fol_seman_gen(self, g, tf):
		yield "\\M{0}\\m_{{{1}}}{2}".format(tf_to_not(tf), g_map_str(g), self.latex_str())
		lv, mid, rv = self.fol_seman_deriv_expands(tf)
		if isinstance(self.left, PL_Atomic_Formula_Exp) and isinstance(self.right, PL_Atomic_Formula_Exp):
			for left_gen, right_gen in zip(self.left.fol_seman_gen(g, lv), self.right.fol_seman_gen(g, rv)):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen)
		else:
			left_final_gen = None
			right_generator = self.right.fol_seman_gen(g, rv)
			right_gen_init = right_generator.next()
			for left_gen in self.left.fol_seman_gen(g, lv):
				yield "[{0} {1} {2}]".format(left_gen, mid, right_gen_init)
				left_final_gen = left_gen
			for right_gen in right_generator:
				yield "[{0} {1} {2}]".format(left_final_gen, mid, right_gen)
	def fol_seman_deriv_expands(self, tf):
		""" Compat from pl, this will map e.g. add to \\tand """
		sde = self.seman_deriv_expands(tf)
		return sde[0], "\\t" + sde[1], sde[2]

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
		return "(" + str(self.left) + " == " + str(self.right) + ")"
	def latex_str(self):
		return "(" + self.left.latex_str() + " \\leftrightarrow " + self.right.latex_str() + ")"
	@staticmethod
	def make_table_op(lr):
		return lr[0] == lr[1]
	def seman_gen(self, tf):
		yield "$V_I({0})$ = {1}".format(self.latex_str(), tf)
		if isinstance(self.left, PL_Atomic_Formula_Exp) and isinstance(self.right, PL_Atomic_Formula_Exp):
			for left_gen0, right_gen0, left_gen1, right_gen1  in zip(	  
																		self.left.seman_gen(0), 
																		self.right.seman_gen(0),
																		self.left.seman_gen(1), 
																		self.right.seman_gen(1)
										    						):
				yield "[[{0} and {1}] or [{2} and {3}]]".format(left_gen0, right_gen0, 
																left_gen1, right_gen1)
		else:
			left_final_gen0, left_final_gen1 = None, None
			right_generator0, right_generator1 = self.right.seman_gen(0), self.right.seman_gen(1)
			right_gen_init0, right_gen_init1 = right_generator0.next(), right_generator1.next()
			for left_gen0, left_gen1 in zip(self.left.seman_gen(0), self.left.seman_gen(1)):
				yield "[[{0} and {1}] or [{2} and {3}]]".format(left_gen0, right_gen_init0, 
															left_gen1, right_gen_init1)
				left_final_gen0, left_final_gen1 = left_gen0, left_gen1
			for right_gen0, right_gen1 in zip(self.right.seman_gen(0), self.right.seman_gen(1)):
				yield "[[{0} and {1}] or [{2} and {3}]]".format(left_final_gen0, right_gen0, 

															left_final_gen1, right_gen1)
	def seman_deriv_expands(self, tf):
		if tf:
			return (1, "iff", 1)
		else:
			return (0, "notiff", 0) #TODO: what should it be in this case?

class FOL_Identity_Exp(PL_Exp):
	def __init__(self, lterm, rterm):
		self.lterm = lterm
		self.rterm = rterm
	def __str__(self):
		return "(" + str(self.lterm) + "=" + str(self.rterm) + ")"
	def latex_str(self):
		return "(" + self.lterm.latex_str() + "=" + self.rterm.latex_str() + ")"
	def fol_seman_gen(self, g, tf):
		yield "\\M{0}\\m_{{{1}}}{2}".format(tf_to_not(tf), g_map_str(g), self.latex_str())
		for lgen, rgen in zip(self.lterm.fol_term_gen(g), self.rterm.fol_term_gen(g)):
			yield "{0}\\tid {1}".format(lgen, rgen)

class FOL_Quantifier_Exp(PL_Exp):
	def __init__(self, var_name, scoped_exp):
		self.var_name = var_name
		self.scoped_exp = scoped_exp
	def fol_seman_gen(self, g, tf):
		yield "\\M{0}\\m_{{{1}}}{2}".format(tf_to_not(tf), g_map_str(g), self.latex_str())
		g_prime = g.copy()
		var_bound_d = g_prime.add_variable(self.var_name)
		for gen in self.scoped_exp.fol_seman_gen(g_prime, tf):
			yield "{0} {1}\\in\\D, {2}".format(self.fol_seman_deriv_quantifier(), var_bound_d, gen)

class FOL_All_Exp(FOL_Quantifier_Exp):
	def __str__(self):
		return "∀{0}{1}".format(self.var_name, self.scoped_exp)
	def latex_str(self):
		return "\\forall {0}{1}".format(self.var_name.latex_str(), self.scoped_exp.latex_str())
	def fol_seman_deriv_quantifier(self):
		return "\\tall"

class FOL_Exist_Exp(FOL_Quantifier_Exp):
	def __str__(self):
		return "∃{0}{1}".format(self.var_name, self.scoped_exp)
	def latex_str(self):
		return "\\exists {0}{1}".format(self.var_name.latex_str(), self.scoped_exp.latex_str())
	def fol_seman_deriv_quantifier(self):
		return "\\tsome"

class FOL_Term(object):
	def __init__(self, name):
		self.name = name
	def __str__(self):
		return self.name
	def latex_str(self):
		if len(self.name) > 1:
			return "{0}_{{{1}}}".format(self.name[0], self.name[1:])
		else:
			return self.name
	def __hash__(self):
		return hash(str(self))
	def __eq__(self, other):
		return str(self) == str(other)
	def denotation_str(self, g):
		return "[{0}]_{{\M,{1}}}".format(self.name, g_map_str(g))

class FOL_Var(FOL_Term):
	def fol_term_gen(self, g):
		yield self.denotation_str(g)
		if self in g:
			yield g[self]
		else:
			pass # Unbound variable

class FOL_Const(FOL_Term):
	def fol_term_gen(self, g):
		yield self.denotation_str(g)
		yield "\I({0})".format(self.name)

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
	'FOL_IDENTITY',
	'PL_PREDVAR',
	'PL_VAR',
	'PL_CONST',
	'FOL_ALL',
	'FOL_EXIST',
	'LPAREN',
	'RPAREN',
	'COMMA',
	'CMD_LATEX_TABLE',
	'CMD_SEMANTIC_DERIV',
	'CMD_ECHO_STRING'
)
 
t_PL_COND = r'->|\\supset'
t_PL_BICOND = r'<->|==|\\leftrightarrow'
t_FOL_IDENTITY = r'='
t_PL_PREDVAR = r'[A-Z]'
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
def t_CMD_ECHO_STRING(t):
	r'echo|print'
	t.value = "CMD_ECHO_STRING"
	return t
def t_PL_AND(t):
	r'\&|\\wedge|and'
	return t
def t_PL_OR(t):
	r'\||\\vee|or'
	return t
def t_PL_NEG(t):
	r'\!|\\neg|not'
	return t
def t_FOL_ALL(t):
	r'all|\\forall'
	t.value = "FOL_ALL"
	return t
def t_FOL_EXIST(t):
	r'exists|\\exists'
	t.value = "FOL_EXIST"
	return t
def t_PL_VAR(t):
	r'[wxyz][0-9]*'
	t.value = FOL_Var(t.value)
	return t
def t_PL_CONST(t):
	r'[a-v][0-9]*'
	t.value = FOL_Const(t.value)
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
	('right','PL_NEG', 'FOL_ALL', 'FOL_EXIST', 'PL_VAR'),
)

start = "command"

def p_empty_command(p):
	"""command : """	
	p[0] = ("CMD_EMPTY", None)

def p_command(p):
	"""
		command : CMD_LATEX_TABLE exp_list
				| CMD_SEMANTIC_DERIV exp_list
				| CMD_ECHO_STRING exp_list
	"""
	p[0] = (p[1], p[2])

def p_exp_list_1(p):
	"""exp_list : exp"""
	p[0] = PL_Exp_Set((p[1],))

def p_exp_list_2(p):
	"""exp_list : exp COMMA exp_list"""
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

def p_exp_indentity(p):
	"""exp : LPAREN term FOL_IDENTITY term RPAREN"""
	p[0] = FOL_Identity_Exp(p[2], p[4])

def p_exp_neg(p):
	"""exp : PL_NEG exp"""
	p[0] = PL_Neg_Exp(p[2])

def p_exp_group(p):
	"""exp : LPAREN exp RPAREN"""
	p[0] = p[2]

def p_exp_quantifier_all(p):
	"""exp : FOL_ALL PL_VAR exp """
	p[0] = FOL_All_Exp(p[2], p[3])

def p_exp_quantifier_exist(p):
	"""exp : FOL_EXIST PL_VAR exp """
	p[0] = FOL_Exist_Exp(p[2], p[3])

def p_exp_atomicformula(p):
	"""exp : PL_PREDVAR term_list """
	p[0] = PL_Atomic_Formula_Exp(p[1], p[2])

def p_term_list(p):
	"""
		term_list : 
				  | term term_list 
	"""
	if len(p) > 1:
		p[0] = [p[1]] + p[2]
	else:
		p[0] = []

def p_term(p):
	"""term : PL_VAR 
			| PL_CONST """
	p[0] = p[1]

def p_error(p):
	if p is None:
		error_s = "EOF"
	else:
		error_s = p.value
	print("Syntax error at '%s'" % error_s)

import ply.yacc as yacc
parser = yacc.yacc()

def run_cmd(cmd, pl_tree_set):
	if cmd == "CMD_LATEX_TABLE":
		if pl_tree_set != None and len(pl_tree_set) != 0 :
			table = pl_tree_set.make_table()
			s = make_latex_table(table)
			print s
			clipboard.copy(s)
	elif cmd == "CMD_SEMANTIC_DERIV":
		if pl_tree_set != None and len(pl_tree_set) == 1:
			pl_tree = pl_tree_set[0]
			s = pl_tree.fol_seman_derive()
			print s
			clipboard.copy(s)
	elif cmd == "CMD_ECHO_STRING":
		for pl_tree in pl_tree_set:
			print pl_tree
	elif cmd == "CMD_EMPTY":
		pass
	else:
		print "Invalid command."

while True:
	try:
		s = raw_input('PL> ')
	except EOFError:
		break
	result = parser.parse(s)
	if result is not None:
		cmd, pl_tree_set = result
		run_cmd(cmd, pl_tree_set)
