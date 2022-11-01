import copy
from operator import eq
from prolog_structures import Constant, Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass

'''
Please read prolog_structures.py for data structures
that represent Prolog terms, rules, and goals.
'''
class Interpreter:
	def __init__(self):
		pass

	'''
	Example
	occurs_check (v, t) where v is of type Variable, t is of type Term.
	occurs_check (v, t) returns true if the Prolog Variable v occurs in t.
	Please see the lecture note Control in Prolog to revisit the concept of
	occurs-check.
	'''
	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	'''
	Problem 1
	variables_of_term (t) where t is of type Term.
	variables_of_clause (c) where c is of type Rule.

	The function should return the Variables contained in a term or a rule
	using Python set.

	The result must be saved in a Python set. The type of each element (a Prolog Variable)
	in the set is Variable.
	'''
	def variables_of_term (self, t : Term) -> set :
		vars = set()
		for v in t.terms:
			if isinstance(v, Variable): vars.add(v)
		return vars
		

	def variables_of_clause (self, c : Rule) -> set :
		vars = set()
		for v in c.head.terms:
			if isinstance(v, Variable): vars.add(v)
		return vars


	'''
	Problem 2
	substitute_in_term (s, t) where s is of type dictionary and t is of type Term
	substitute_in_clause (s, t) where s is of type dictionary and c is of type Rule,

	The value of type dict should be a Python dictionary whose keys are of type Variable
	and values are of type Term. It is a map from variables to terms.

	The function should return t_ obtained by applying substitution s to t.

	Please use Python dictionary to represent a subsititution map.
	'''
	def substitute_in_term (self, s : dict, t : Term) -> Term:
		if isinstance(t, Function):
			new_terms = []
			for term in t.terms:
				if isinstance(term, Function):
					if term.relation in s:
						for key in s:
							if isinstance(key, Function):
								if key.relation == term.relation and set(key.terms) == set(term.terms):
									new_terms.append(s[term.relation])
					else:
						new_terms.append(term)
				else: 
					new_terms.append(s[term] if term in s else term)
			return Function(t.relation, new_terms)
		elif isinstance(t, Variable):
			return Variable(t.value)
		elif isinstance(t, Constant):
			return Constant(t.value)
		return t
		


	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		if isinstance(c, Rule):
			new_terms = []
			for term in c.head.terms:
				new_terms.append(s[term] if term in s else term)
		return Rule(Function(c.head.relation,new_terms), c.body)


	'''
	Problem 3
	unify (t1, t2) where t1 is of type term and t2 is of type Term.
	The function should return a substitution map of type dict,
	which is a unifier of the given terms. You may find the pseudocode
	of unify in the lecture note Control in Prolog useful.

	The function should raise the exception raise Not_unfifiable (),
	if the given terms are not unifiable.

	Please use Python dictionary to represent a subsititution map.
	'''

	def unify (self, t1: Term, t2: Term) -> dict:
		return self.unify_s(t1, t2, {})


	def unify_s(self, x: Term, y: Term, s: dict) -> dict:
		if x == y:
			return s
		if isinstance(x, Variable):
			return self.unify_v(x, y, s)
		elif isinstance(y, Variable):
			return self.unify_v(y, x, s)
		elif isinstance(x, Function) and isinstance(y, Function):
			if x.relation != y.relation or len(x.terms) != len(y.terms):
				raise Not_unifiable
			else:
				for i in range(len(x.terms)):
					s = self.unify_s(x.terms[i], y.terms[i], s)
				return s
		else:
			raise Not_unifiable


	def unify_v(self, x: Variable, y: Term, s: dict) -> dict:
		if x in s:
			return self.unify_s(s[x], y, s)
		elif isinstance(y, Variable) and y in s:
			return self.unify_s(x, s[y], s)
		else:
			for key, value in s.items():
				if value == x:
					s[key] = y
			return {**s, x:y}




	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)


	'''
	Problem 4
	Following the Abstract interpreter pseudocode in the lecture note Control in Prolog to implement
	a nondeterministic Prolog interpreter.

	nondet_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of Terms (results), which is an instance of the original goal and is
	a logical consequence of the program. See the tests cases (in src/main.py) as examples.
	'''
	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		G = copy.deepcopy(pgoal)
		resolvent = copy.deepcopy(pgoal)

		while resolvent:
			A = resolvent.pop(random.randint(0, len(resolvent)-1))
			for rule in program:
				try:
					frule = self.freshen(rule)
					theta = self.unify(frule.head, A)
					resolvent.extend(frule.body.terms)
					for i in range(len(G)):
						G[i] = self.substitute_in_term(theta, G[i])
					for j in range(len(resolvent)):
						resolvent[j] = self.substitute_in_term(theta, resolvent[j])
					if resolvent != None:
						break
				except Not_unifiable:
					continue
		return G
		
		
		

	'''
	Challenge Problem

	det_query (program, goal) where
		the first argument is a program which is a list of Rules.
		the second argument is a goal which is a list of Terms.

	The function returns a list of term lists (results). Each of these results is
	an instance of the original goal and is a logical consequence of the program.
	If the given goal is not a logical consequence of the program, then the result
	is an empty list. See the test cases (in src/main.py) as examples.
	'''
	def det_query (self, program : List[Rule], pgoal : List[Term]) -> List[List[Term]]:
		
	
		def dfs (resolvent : List[Term], goal : List[Term], solutions : List[List[Term]]) -> List[List[Term]]:
			if not resolvent:
				solutions.append(goal)
			else:
				chosen_goal = resolvent.pop(0)
				for rule in program:
					try:
						rule = self.freshen(rule)
						theta = self.unify(rule.head, chosen_goal)
						new_resolvent = resolvent.copy()
						new_goal = goal.copy()

						new_resolvent.extend(rule.body.terms)
						for i in range(len(new_resolvent)):
							new_resolvent[i] = self.substitute_in_term(theta, new_resolvent[i])
						for j in range(len(new_goal)):
							new_goal[j] = self.substitute_in_term(theta, new_goal[j])

					except Not_unifiable:
						continue
				
					return dfs(new_resolvent, new_goal, solutions)
	
		resolvent = pgoal.copy()
		solutions = []
		dfs(resolvent, pgoal, solutions)
		return solutions