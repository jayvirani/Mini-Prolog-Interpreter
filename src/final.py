import copy
from operator import eq
from prolog_structures import Constant, Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass


class Interpreter:
	def __init__(self):
		pass

	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False

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