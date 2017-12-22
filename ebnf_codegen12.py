import sys

import ebnf_semantic

class StateNode(object):
	def __init__(self):
		self.transitions = {}

def print_state_graph_recurse(node, cache):
	for symbol, next_node in node.transitions.items():
		if next_node == None:
			continue

		if next_node not in cache["ids"]:
			cache["ids"][next_node] = cache["counter"]
			cache["counter"] += 1
			print_state_graph_recurse(next_node, cache)

	print "state_%d:"%cache["ids"][node]

	for symbol, next_node in node.transitions.items():
		if next_node == None:
			print "\t%s -> None"%repr(symbol)
		else:
			print "\t%s -> state_%d"%(repr(symbol), cache["ids"][next_node])

	print ""

def print_state_graph(node):
	cache = {"ids": {node: 0}, "counter": 1}
	print_state_graph_recurse(node, cache)

def build_state_node_for_terminal(pattern, cache):
	terminal = pattern.terminal
	node = StateNode()

	if len(terminal) == 1:
		node.transitions = {terminal[0]: None}
	else:
		node.transitions = {terminal[0]: ebnf_semantic.Terminal(terminal[1:])}

	return node

def build_state_node_for_identifier(pattern, cache):
	node = StateNode()
	node.transitions = {pattern: None}
	return node

def build_state_node_for_optional(pattern, cache):
	subnode = build_state_node(pattern.rhs, cache)
	transitions = {symbol: next_pattern for symbol, next_pattern in subnode.transitions.items()}
	transitions[None] = None
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_repetition(pattern, cache):
	subnode = build_state_node(pattern.rhs, cache)
	transitions = {}

	for symbol, next_pattern in subnode.transitions.items():
		if next_pattern == None:
			transitions[symbol] = pattern
		else:
			transitions[symbol] = ebnf_semantic.Concatenation([next_pattern, pattern])

	transitions[None] = None
	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_concatenation(pattern, cache):
	terms = list(pattern.terms)

	if type(terms[0]) == ebnf_semantic.Optional:
		clause1 = ebnf_semantic.Concatenation([terms[0].rhs] + terms[1:])
		clause2 = ebnf_semantic.Concatenation(terms[1:]) if len(terms) > 2 else terms[1]
		return build_state_node(ebnf_semantic.Alternation([clause1, clause2]), cache)

	if type(terms[0]) == ebnf_semantic.Repetition:
		clause1 = ebnf_semantic.Concatenation([terms[0].rhs, terms[0]] + terms[1:])
		clause2 = ebnf_semantic.Concatenation(terms[1:]) if len(terms) > 2 else terms[1]
		return build_state_node(ebnf_semantic.Alternation([clause1, clause2]), cache)

	subnode = build_state_node(terms[0], cache)
	transitions = {}

	for symbol, next_pattern in subnode.transitions.items():
		if next_pattern == None:
			if len(terms) > 2:
				transitions[symbol] = ebnf_semantic.Concatenation(terms[1:])
			else:
				transitions[symbol] = terms[1]
		else:
			transitions[symbol] = ebnf_semantic.Concatenation([next_pattern] + terms[1:])

	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node_for_alternation(pattern, cache):
	subnodes = [build_state_node(clause, cache) for clause in pattern.clauses]
	transitions_clauses = {}

	for subnode in subnodes:
		for symbol, next_pattern in subnode.transitions.items():
			if symbol not in transitions_clauses:
				transitions_clauses[symbol] = []

			transitions_clauses[symbol].append(next_pattern)

	transitions = {}

	for symbol, _clauses in transitions_clauses.items():
		if symbol == None:
			continue

		clauses = [clause for clause in _clauses if clause != None]
		clauses = sorted(list(set(clauses)))

		if len(clauses) == 0:
			transitions[symbol] = None
		elif len(clauses) == 1:
			transitions[symbol] = clauses[0]
		elif len(clauses) > 1:
			transitions[symbol] = ebnf_semantic.Alternation(clauses)

		if None in _clauses and transitions[symbol] != None:
			transitions[symbol] = ebnf_semantic.Optional(transitions[symbol])

	if None in transitions_clauses:
		transitions[None] = None

	node = StateNode()
	node.transitions = transitions
	return node

def build_state_node(pattern, cache):
	if pattern not in cache["nodes"]:
		builders = {ebnf_semantic.Terminal: build_state_node_for_terminal,
				ebnf_semantic.Identifier: build_state_node_for_identifier,
				ebnf_semantic.Optional: build_state_node_for_optional,
				ebnf_semantic.Repetition: build_state_node_for_repetition,
				ebnf_semantic.Concatenation: build_state_node_for_concatenation,
				ebnf_semantic.Alternation: build_state_node_for_alternation}

		cache["nodes"][pattern] = builders[type(pattern)](pattern, cache)

	return cache["nodes"][pattern]

def build_state_graph(pattern, cache):
	if pattern not in cache["graphs"]:
		node = StateNode()
		cache["graphs"][pattern] = node

		entrynode = build_state_node(pattern, cache)

		for symbol, next_pattern in entrynode.transitions.items():
			if next_pattern == None:
				node.transitions[symbol] = None
			else:
				node.transitions[symbol] = build_state_graph(next_pattern, cache)

	return cache["graphs"][pattern]

def build_state_graphs(ast_info):
	cache = {"graphs": {}, "nodes": {}}
	graphs = {identifier: build_state_graph(pattern, cache) for identifier, pattern in ast_info.rules.items()}
	return graphs

if len(sys.argv) != 3:
	print "Usage: %s <grammar file> <top_id>"%(sys.argv[0])
	quit()

filename = sys.argv[1]
top_id = sys.argv[2]

with open(filename, 'r') as f:
	description = f.read()

ast_info = ebnf_semantic.create_ast(description, top_id)
graphs = build_state_graphs(ast_info)

for identifier, node in graphs.items():
	print "/* %s = %s */"%(identifier, ast_info.rules[identifier])
	print_state_graph(node)
